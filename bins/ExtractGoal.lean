import Lean
import LeanUtils.TargetEnv

open Lean Elab Meta Expr MVarId

def Pp.compactOptions (numericTypes : Bool := false) : Options → Options :=
  (pp.proofs.set · false |>
  (pp.deepTerms.set · true |>
  (pp.numericTypes.set · numericTypes |>
  (pp.maxSteps.set · 1000000 |>
  (pp.match.set · true |>
  (pp.motives.all.set · false |>
  (pp.coercions.types.set · true |>
  (pp.unicode.fun.set · true |>
  (pp.funBinderTypes.set · true |>
  (pp.explicit.set · false |>
  (pp.universes.set · false)))))))))))

def Pp.extractionOptions (numericTypes : Bool) (opts : Options) : Options :=
  Pp.compactOptions numericTypes opts

/-- Rendering flags for the helper's *statement*.

Each corresponds to a delaborator habit that does not round-trip:
* `noFunBinderTypes` — forced `fun (a : T) ↦ …` ascriptions can name types with no
  matching instance (an appended `OracleSpec` prints as a bare arrow).
* `noCoercionTypes` — `pp.coercions.types` ascribes `⇑f`'s *unbundled* arrow, losing
  every implicit that only the bundled hom type pins.
* `noFieldNotation` — `X.ρ` re-resolves to the wrong constant when the type is a
  reducible alias whose namespace defines a same-named field.
* `coeExplicit` — print `DFunLike.coe (F := <bundled>)` explicitly; needs `pp.analyze`
  *and* `pp.coercions := false` together, neither works alone.
* `showProofs` — re-enable `pp.proofs`, which `Pp.compactOptions` turns off for every
  rung.  A `Prop`-typed proof nested inside a *data* value (`⟨σ, ⁻o⟩ : OSequence`)
  is then elided as `⋯` in the statement and no rung can recover it, even though the
  term is already spelled out in scope.  Printing it is lossless: by definitional
  proof irrelevance any proof of that `Prop` is interchangeable, so the restated
  signature elaborates to the same type.  Kept off by default because proofs are
  usually large and irrelevant; this is a retry rung, not a new baseline.
-/
structure SigFlags where
  noFunBinderTypes : Bool := false
  noCoercionTypes : Bool := false
  noFieldNotation : Bool := false
  coeExplicit : Bool := false
  analyze : Bool := false
  showProofs : Bool := false
  deriving Inhabited

def Pp.signatureOptions (numericTypes : Bool) (f : SigFlags) (opts : Options) : Options :=
  let opts := Pp.compactOptions numericTypes opts
  let opts := if f.noFunBinderTypes then pp.funBinderTypes.set opts false else opts
  let opts := if f.noCoercionTypes then pp.coercions.types.set opts false else opts
  let opts := if f.noFieldNotation then opts.setBool `pp.fieldNotation false else opts
  let opts := if f.analyze then opts.setBool `pp.analyze true else opts
  let opts := if f.showProofs then pp.proofs.set opts true else opts
  if f.coeExplicit then
    opts.setBool `pp.coercions false
      |>.setBool `pp.analyze true
      |>.setBool `pp.analyze.checkInstances true
  else opts

/-- Find a maximal *closed* proof subterm that is not already an fvar.

`Meta.isProof` guarantees the subterm's type is a `Prop`, which is exactly the
guard we need: abstracting a `Prop` is lossless in both directions by definitional
proof irrelevance, whereas abstracting a data subterm would yield a strictly
stronger and possibly false statement.  Subterms with loose bvars are skipped --
they cannot be hoisted into an outer binder -- and fvars are skipped because they
already print by name rather than as `⋯`.
-/
partial def collectProofSubterms (e : Expr) : MetaM (Array Expr) := do
  if !e.hasLooseBVars && !e.isFVar then
    if ← Meta.isProof e then
      return #[e]
  match e with
  | .app f a => return (← collectProofSubterms f) ++ (← collectProofSubterms a)
  | .lam _ t b _ => return (← collectProofSubterms t) ++ (← collectProofSubterms b)
  | .forallE _ t b _ => return (← collectProofSubterms t) ++ (← collectProofSubterms b)
  | .letE _ t v b _ =>
      return (← collectProofSubterms t) ++ (← collectProofSubterms v)
        ++ (← collectProofSubterms b)
  | .mdata _ b => collectProofSubterms b
  | .proj _ _ b => collectProofSubterms b
  | _ => return #[]

/-- All maximal closed proof subterms, the ones containing a `sorry` first.

Ordering matters: a subterm that mentions `sorryAx` is what actually blocks
extraction, and hoisting it is the whole point.  An unrelated instance proof found
earlier in the traversal must not stop us from reaching it -- the previous version
searched for a single subterm and gave up if that one turned out unusable. -/
def proofSubtermCandidates (e : Expr) : MetaM (Array Expr) := do
  let all ← collectProofSubterms e
  return (all.filter (·.hasSorry)) ++ (all.filter (fun t => !t.hasSorry))

partial def getFreshConstName (base : Name) : MetaM Name := do
  let env ← getEnv
  let consts := env.constants
  let rec loop (i : Nat) :=
    let cand :=
      if i = 0 then base else base.appendIndexAfter i
    if consts.contains cand then
      loop (i + 1)
    else
      cand
  return loop 0

def keepUsedSignatureLevelParams (name : Name) (levels : List Name)
    (signature : String) : String :=
  match signature.splitOn "}" with
  | first :: rest =>
      if first.startsWith (name.toString ++ ".{") then
        let body := String.intercalate "}" rest
        let used := levels.filter fun level =>
          (body.splitOn level.toString).length > 1
        let renderedName :=
          if used.isEmpty then
            name.toString
          else
            name.toString ++ ".{" ++
              String.intercalate ", " (used.map (·.toString)) ++ "}"
        renderedName ++ body
      else
        signature
  | [] => signature

/--
Obtain the inaccessible fvars from the given local context. An fvar is
inaccessible if (a) its user name is inaccessible or (b) it is shadowed by a
later fvar with the same user name.
-/
def Lean.LocalContext.inaccessibleFVars (lctx : LocalContext) :
    Array LocalDecl :=
  let (result, _) :=
    lctx.foldr (β := Array LocalDecl × Std.HashSet Name)
      (init := (Array.mkEmpty lctx.numIndices, {}))
      fun ldecl (result, seen) =>
        let result :=
          if ldecl.isImplementationDetail || ldecl.userName.hasMacroScopes ||
              seen.contains ldecl.userName then
            result.push ldecl
          else
            result
        (result, seen.insert ldecl.userName)
  result.reverse


/--
Rename all inaccessible fvars. An fvar is inaccessible if (a) its user name is
inaccessible or (b) it is shadowed by a later fvar with the same user name. This
function gives all inaccessible fvars a unique, accessible user name. It returns
the new goal and the fvars that were renamed.
-/
def Lean.MVarId.renameInaccessibleFVars (mvarId : MVarId) :
    MetaM (MVarId × Array FVarId) := do
  let mdecl ← mvarId.getDecl
  let mut lctx := mdecl.lctx
  let inaccessibleFVars := lctx.inaccessibleFVars
  if inaccessibleFVars.isEmpty then
    return (mvarId, #[])
  let mut renamedFVars := Array.mkEmpty lctx.decls.size
  for ldecl in inaccessibleFVars do
    let newName := lctx.getUnusedName ldecl.userName
    lctx := lctx.setUserName ldecl.fvarId newName
    renamedFVars := renamedFVars.push ldecl.fvarId
  let newMVar ← mkFreshExprMVarAt lctx mdecl.localInstances mdecl.type
  mvarId.assign newMVar
  return (newMVar.mvarId!, renamedFVars)

/-- Convert local proof definitions into ordinary hypotheses. This is safe for
proofs because their particular values are irrelevant, while generalizing a
data-valued `let` could make the extracted theorem strictly stronger. -/
def Lean.MVarId.abstractLocalProofValues (mvarId : MVarId) :
    MetaM (MVarId × Array FVarId) := do
  let mdecl ← mvarId.getDecl
  let candidates :=
    mdecl.lctx.foldl (init := #[]) fun result ldecl =>
      if ldecl.isLet then result.push ldecl else result
  let mut lctx := mdecl.lctx
  let mut abstracted := #[]
  for ldecl in candidates do
    if ← isProp ldecl.type then
      lctx := lctx.modifyLocalDecl ldecl.fvarId fun
        | .ldecl index fvarId userName type _ _ kind =>
            .cdecl index fvarId userName type .default kind
        | decl => decl
      abstracted := abstracted.push ldecl.fvarId
  if abstracted.isEmpty then
    return (mvarId, abstracted)
  let newMVar ← mkFreshExprMVarAt lctx mdecl.localInstances mdecl.type
  mvarId.assign newMVar
  return (newMVar.mvarId!, abstracted)

/-- Preserve all locals except blockers that Lean can prove are unused. Local
proof definitions become hypotheses. Unused local definitions are removed.
Used data-valued definitions retain their values; if such a value contains a
sorry, it is removed only when `tryClearMany'` proves it unused, and otherwise
extraction is rejected by the final sorry check.
The returned arrays contain removed locals and abstracted proof definitions. -/
def Lean.MVarId.sanitizeForExtraction (mvarId : MVarId) :
    MetaM (MVarId × Array FVarId × Array FVarId) := do
  let (mvarId, abstractedProofs) ← mvarId.abstractLocalProofValues
  let contaminated := (← mvarId.getDecl).lctx.foldl (init := #[]) fun result ldecl =>
    let valueHasSorry := ldecl.value?.any (fun value => value.hasSorry)
    if ldecl.type.hasSorry || valueHasSorry then
      result.push ldecl.fvarId
    else
      result
  let (mvarId, clearedContaminated) ← mvarId.tryClearMany' contaminated
  let localDefinitions := (← mvarId.getDecl).lctx.foldl (init := #[]) fun result ldecl =>
    if ldecl.isLet then result.push ldecl.fvarId else result
  let (mvarId, clearedDefinitions) ← mvarId.tryClearMany' localDefinitions
  let inaccessible := (← mvarId.getDecl).lctx.inaccessibleFVars.map (·.fvarId)
  let (mvarId, clearedInaccessible) ← mvarId.tryClearMany' inaccessible
  return (mvarId, clearedContaminated ++ clearedDefinitions ++ clearedInaccessible,
    abstractedProofs)

/-- Format a goal into a type signature for a declaration named `name`.

Example output: `myTheorem (a b : Nat) : a + b = b + a`.

The return values are:
* A formatted piece of `MessageData`, like `m!"myTheorem (a b : Nat) : a + b = b + a"`.
-/
def mkThmHeader (name : Name) (g : MVarId) (numericTypes : Bool := false)
    (sanitizeContext : Bool := false) (analyze : Bool := false)
    (sigFlags : SigFlags := {}) (exprSignature : Bool := false)
    (abstractProofs : Bool := false) :
    TermElabM (MessageData × MessageData × List Name) :=
  withoutModifyingEnv <| withoutModifyingState do
    let originalLctx := (← g.getDecl).lctx
    let (g, removedFVarIds, abstractedProofFVarIds) ←
      if sanitizeContext then g.sanitizeForExtraction else pure (g, #[], #[])
    let (g, inaccessibleFVarIds) ← g.renameInaccessibleFVars

    -- Hoist proof subterms of the goal into real locals *before* the context is
    -- reverted -- afterwards every context variable is a bound variable, so the
    -- subterms we want are no longer closed and cannot be abstracted.
    -- `generalize` introduces each as a local, which the existing revert then turns
    -- into a binder; marking them inaccessible makes the call site pass a hole, and
    -- unification restores the original proof term.
    let (g, generalizedFVarIds, generalizedTypes) ← do
      if !abstractProofs then
        pure (g, #[], #[])
      else
        let mut g := g
        let mut introduced : Array FVarId := #[]
        -- record each type here: the generalized fvar lives only in the
        -- intermediate goal's context, so `fvarId.getType` cannot find it later
        let mut types : Array Expr := #[]
        for _ in [0:8] do
          let next? ← g.withContext do
            let ty ← instantiateMVars (← g.getType)
            -- take the first *usable* candidate rather than giving up on the first
            -- unusable one; sorry-bearing subterms are tried first
            for sub in ← proofSubtermCandidates ty do
              let subTy ← instantiateMVars (← inferType sub)
              unless subTy.hasSorry || subTy.hasLooseBVars || subTy.hasExprMVar do
                return some sub
            return none
          match next? with
          | none => break
          | some sub =>
            let name := Name.mkSimple s!"sorrydb_prf_{introduced.size + 1}"
            let subTy ← g.withContext do instantiateMVars (← inferType sub)
            let (ids, g') ← g.generalize #[{ expr := sub, xName? := some name }]
            g := g'
            introduced := introduced ++ ids
            types := types ++ ids.map (fun _ => subTy)
        pure (g, introduced, types)
    let inaccessibleFVarIds := inaccessibleFVarIds ++ generalizedFVarIds

    let (fvarIds, defaultApplicationFVarIds) :=
      (← g.getDecl).lctx.foldl (init := (#[], #[])) fun (ids, applicationIds) decl =>
        if decl.isAuxDecl then
          (ids, applicationIds)
        else
          let ids := ids.push decl.fvarId
          let applicationIds :=
            if decl.isLet then applicationIds else applicationIds.push decl.fvarId
          (ids, applicationIds)
    let applicationFVarIds :=
      if sanitizeContext then
        originalLctx.foldl (init := #[]) fun ids decl =>
          if decl.isAuxDecl || removedFVarIds.contains decl.fvarId then ids
          else if decl.isLet && !abstractedProofFVarIds.contains decl.fvarId then ids
          else ids.push decl.fvarId
      else
        defaultApplicationFVarIds
    let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := false) fvarIds
    let fvars ←
      if sanitizeContext then
        applicationFVarIds.mapM fun fvarId => pure (mkFVar fvarId)
      else
        applicationFVarIds.mapM fun fvarId => do
          if inaccessibleFVarIds.contains fvarId then
            let ty ← match generalizedFVarIds.findIdx? (· == fvarId) with
              | some i => pure generalizedTypes[i]!
              | none => fvarId.getType
            mkFreshExprSyntheticOpaqueMVar ty
          else
            pure (mkFVar fvarId)
    let ty ← instantiateMVars (← g.getType)
    if ty.hasExprMVar then
      -- TODO: turn metavariables into new hypotheses?
      throwError "Extracted goal has metavariables: {ty}"
    let ty ← Term.levelMVarToParam ty
    if ty.hasSorry then
      throwError "Unsupported extracted goal: its type depends on an earlier sorry"
    let originalLevels := (collectLevelParams {} ty).params.toList
    -- Pretty-printer-generated names such as `u_1` may already be in scope
    -- through a section variable, or may be genuinely new. Give every helper
    -- declaration its own predictable level names so both cases elaborate the
    -- same way when the rendered theorem is inserted back into the source.
    let levels := originalLevels.mapIdx fun index _ =>
      Name.mkSimple s!"sorrydb_u_{index + 1}"
    let ty := ty.instantiateLevelParams originalLevels (levels.map mkLevelParam)
    addAndCompile <| Declaration.axiomDecl
      { name := name
        levelParams := levels
        isUnsafe := false
        type := ty }
    -- `MessageData.signature` routes through `ppSignature`, which delaborates the
    -- bare `.const` -- so `topDownAnalyze` has no application to look at and
    -- `pp.analyze` is structurally a no-op there.  Rendering the quantified type
    -- directly makes the statement a real, re-renderable artifact that the retry
    -- ladder can act on.  Kept behind a flag so the default path is byte-identical.
    let signature ← withOptions
        (Pp.signatureOptions numericTypes sigFlags) do
      if exprSignature then
        let levelSuffix :=
          if levels.isEmpty then ""
          else ".{" ++ String.intercalate ", " (levels.map (·.toString)) ++ "}"
        addMessageContext m!"{name.toString ++ levelSuffix} : {ty}"
      else
        addMessageContext <| MessageData.signature name
    let application := mkAppN (← mkConstWithFreshMVarLevels name) fvars
    discard <| inferType application
    let application ← instantiateMVars application
    -- `pp.analyze` re-renders the application with the *minimum* annotations
    -- needed for it to elaborate back to the same term: named arguments like
    -- `(d := d)` for implicits the call site cannot infer, and nothing at all
    -- where inference already works.  Without it the implicit arguments are
    -- passed in the term but omitted from the rendering, so re-elaboration
    -- fails with `don't know how to synthesize implicit argument`.
    let application ← withOptions
        (fun opts =>
          (pp.explicit.set (pp.universes.set (pp.proofs.set opts true) false) false)
            |>.setBool `pp.mvars false |>.setBool `pp.analyze analyze) do
      addMessageContext <| MessageData.ofExpr application
    return (signature, application, levels)

/--
Render the application, optionally turning unfilled holes into `by assumption`.

`mkThmHeader` passes a fresh metavariable for any argument whose value is an
*inaccessible* local, since such a local cannot be named at the call site.  That
renders as `?_`, which does not elaborate.  For a binder the conclusion never
mentions, any inhabitant of the right type will do, so `by assumption` is enough;
for one the conclusion does mention, a wrong choice changes the statement and the
candidate fails to compile, so the compile stage is the safety net.
-/
def renderApplication (application : MessageData) (assumptionHoles : Bool)
    (abstractProofs : Bool) : CoreM String := do
  let rendered ← application.toString
  if assumptionHoles then
    return rendered.replace "?_" "(by assumption)"
  else if abstractProofs then
    -- holes standing for abstracted proof binders: `_` lets unification put the
    -- original proof term back, which is what makes the round trip exact
    return rendered.replace "?_" "_"
  else
    return rendered

def getTheoremPosition (ci : ConstantVal) : MetaM (Option Position) := do
  return (← findDeclarationRanges? ci.name).map (·.range.pos)

def extractGoal (args : List String): IO (Except String String) := do
  let readRawSorry : IO String := do
    let stdin ← IO.getStdin
    return (← stdin.getLine).trim
  let (path, rawSorry, numericTypes, sanitizeContext, analyze, assumptionHoles,
       sigFlags, exprSignature, abstractProofs) ← match args with
  | path :: rest => do
      let flags := rest.filter (fun arg => arg.startsWith "--")
      let positional := rest.filter (fun arg => !arg.startsWith "--")
      let rawSorry ← match positional with
        | [] => readRawSorry
        | [raw] => pure raw
        | _ => throw (IO.userError "Expected at most one JSON argument")
      let sigFlags : SigFlags := {
        noFunBinderTypes := flags.contains "--no-fun-binder-types"
        noCoercionTypes := flags.contains "--no-coercion-types"
        noFieldNotation := flags.contains "--no-field-notation"
        coeExplicit := flags.contains "--coe-explicit"
        analyze := flags.contains "--analyze"
        showProofs := flags.contains "--show-proofs" }
      pure (path, rawSorry,
        flags.contains "--numeric-types",
        flags.contains "--sanitize-context",
        flags.contains "--analyze",
        flags.contains "--assumption-holes",
        sigFlags,
        flags.contains "--expr-signature",
        flags.contains "--abstract-proofs")
  | [] => throw (IO.userError "Requires a path, optional JSON input, and optional --numeric-types, --sanitize-context, --analyze or --assumption-holes")

  let (fileMap, singleData) ← match ← findSorryTargetFromFile path rawSorry with
  | .ok x => pure x
  | .error e => throw (IO.userError e)

  singleData.ctx.runMetaM singleData.lctx do
    MonadWithOptions.withOptions (Pp.extractionOptions numericTypes) do
      let g ← mkFreshExprMVar singleData.type
      let name ← getFreshConstName `mytheorem
      let (header, application, levels) ←
        Lean.Elab.Term.TermElabM.run' (mkThmHeader name g.mvarId! numericTypes sanitizeContext analyze sigFlags exprSignature abstractProofs)
      let header := keepUsedSignatureLevelParams name levels (← header.toString)
      if header.contains '⋯' then
        throwError "Unsupported extracted goal: compact theorem signature contains omitted terms (⋯)"
      let commandPositions := singleData.commandPositions.map fileMap.ofPosition
      let commandPos := commandPositions.head!
      let wrapperPrefix :=
        (commandPositions.zip (commandPositions.drop 1)).foldl
          (fun text positions =>
            text ++ (String.fromUTF8! <| fileMap.source.toUTF8.extract positions.1.byteIdx positions.2.byteIdx)) ""
      let «prefix» := String.fromUTF8! <| fileMap.source.toUTF8.extract 0 commandPos.byteIdx
      return .ok («prefix» ++ "\n-- sorrydb-helper-start\n" ++ wrapperPrefix ++
        "theorem " ++ header ++ " := sorry" ++
        "\n-- sorrydb-application: " ++ (← renderApplication application assumptionHoles abstractProofs))

def main (args : List String) : IO UInt32  := do
  -- Every failure, including refusals raised inside MetaM, is reported as
  -- `{"error": ...}` so callers can rely on one output shape.
  let res ← try extractGoal args catch e => pure (.error (toString e))
  let res := match res with
  | .ok a    => Json.mkObj [("ok", ToJson.toJson a)]
  | .error e => Json.mkObj [("error", ToJson.toJson e)]
  IO.println (toJson res)
  return 0
