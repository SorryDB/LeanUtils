import Lean
import LeanUtils.TargetEnv

open Lean Elab Meta Expr MVarId

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
        if ldecl.isImplementationDetail then
          (result, seen)
        else
          let result :=
            if ldecl.userName.hasMacroScopes || seen.contains ldecl.userName then
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

/-- Format a goal into a type signature for a declaration named `name`.

Example output: `myTheorem (a b : Nat) : a + b = b + a`.

The return values are:
* A formatted piece of `MessageData`, like `m!"myTheorem (a b : Nat) : a + b = b + a"`.
-/
def mkThmHeader (name : Name) (g : MVarId) : TermElabM (MessageData) :=
  withoutModifyingEnv <| withoutModifyingState do
    let (g, _) ← g.renameInaccessibleFVars

    let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
    let ty ← instantiateMVars (← g.getType)
    if ty.hasExprMVar then
      -- TODO: turn metavariables into new hypotheses?
      throwError "Extracted goal has metavariables: {ty}"
    let ty ← Term.levelMVarToParam ty
    let seenLevels := collectLevelParams {} ty
    let levels := (← Term.getLevelNames).filter
      fun u => seenLevels.visitedLevel.contains (.param u)
    addAndCompile <| Declaration.axiomDecl
      { name := name
        levelParams := levels
        isUnsafe := false
        type := ty }
    let sig ← addMessageContext <| MessageData.signature name
    return sig

def getTheoremPosition (ci : ConstantVal) : MetaM (Option Position) := do
  return (← findDeclarationRanges? ci.name).map (·.range.pos)

def Pp.applyOptions : Options → Options :=
  (pp.proofs.set · false |>
  (pp.motives.all.set · true |>
  (pp.coercions.types.set · true |>
  (pp.unicode.fun.set · true |>
  (pp.funBinderTypes.set · true)))))

def extractGoal (args : List String): IO (Except String String) := do
  let (path, rawSorry) ← match args with
  | [path, rawSorry] => pure (path, rawSorry)
  | [path] => do
    -- Read from stdin
    let stdin ← IO.getStdin
    let rawSorry ← stdin.getLine
    pure (path, rawSorry.trim)
  | _ => throw (IO.userError "Requires a path and either a JSON argument or stdin")

  let (fileMap, singleData) ← match ← findSorryTargetFromFile path rawSorry with
  | .ok x => pure x
  | .error e => throw (IO.userError e)

  singleData.ctx.runMetaM {} do
    MonadWithOptions.withOptions Pp.applyOptions do
      let g ← mkFreshExprMVar singleData.type
      let x ← Lean.Elab.Term.TermElabM.run' (mkThmHeader (← getFreshConstName `mytheorem) g.mvarId!)
      let «prefix» := match ← getTheoremPosition singleData.theoremVal.toConstantVal with
      | some pos =>
          let strPos := fileMap.ofPosition pos
          String.Pos.Raw.extract fileMap.source 0 strPos
      | none => ""
      return .ok («prefix» ++ "\n" ++ "theorem " ++ (← x.toString) ++ " := sorry")

def main (args : List String) : IO UInt32  := do
  let res ← extractGoal args
  let res := match res with
  | .ok a    => Json.mkObj [("ok", ToJson.toJson a)]
  | .error e => Json.mkObj [("error", ToJson.toJson e)]
  IO.println (toJson res)
  return 0
