import LeanUtils.ExtractSorry
import Lean.Meta.Basic

open Lean Meta Elab Term Expr Meta Tactic

structure TargetEnvData where
  ctx: ContextInfo
  theoremVal: TheoremVal
  type: Expr



def findTargetEnv (tree: InfoTree) (targetSorry: ParsedSorry): IO (List TargetEnvData) := do
  -- TODO - explain why an empty LocalContext is okay. Maybe - local context occurs within TermElabM - we're at top-level decl, so no local context
  let a ←  (do (tree.visitM (m := IO) (postNode := fun ctx i _ as => do
    let head := (as.flatMap' Option.toList).flatten'
    match i with
    -- TODO - deduplicate this
    | .ofTermInfo ti =>
      if targetSorry.startPos == ctx.fileMap.toPosition ti.stx.getPos?.get! && isSorryTerm ti.stx then do
        if let some type := ti.expectedType? then
          return head ++ ([(ctx, some (type), none)])
        else
          return head ++ [(ctx, none, none)]
      else
        return head
    | .ofTacticInfo ti =>
      -- TODO - do we need the 'mctxBefore' stuff from 'visitSorryNode'?
      if targetSorry.startPos == ctx.fileMap.toPosition ti.stx.getPos?.get! && isSorryTactic ti.stx then do
        let goal ← if let [goal] := ti.goalsBefore then pure goal else (throw (IO.userError "Found more than one goal"))
        return head ++ ([(ctx, none, some goal)])
      else
        return head
    | _ => return head

  )))

  let matchedCtxs := a.get!
  let targetDatas ← (matchedCtxs.mapM (fun (ctx, type, goal) => do
    ctx.runMetaM {} do
      if let some oldDecl :=  ctx.env.find? targetSorry.parentDecl then
        match oldDecl with
        | .thmInfo info =>
          match (type, goal) with
          | (some type, none) => return [({ctx := ctx, theoremVal := info, type := type} : TargetEnvData)]
          | (none, some goal) =>
              let goalType ← goal.getType
              return [({ctx := ctx, theoremVal := info, type := goalType} : TargetEnvData)]
          | _ => throwError "Bad case"
        | _ => throwError "Bad decl type"
      else
        throwError ("Missing parentDecl in environment")
  ))
  let allTargets := targetDatas.flatten'.filter (fun data => data.ctx.parentDecl? == (some targetSorry.parentDecl))
  return allTargets


def findSorryTargetFromFile (path rawSorry : String) : IO (Except String (FileMap × TargetEnvData)) := do
  unsafe enableInitializersExecution
  let path : System.FilePath := { toString := path }
  let path ← IO.FS.realPath path
  let projectSearchPath ← getProjectSearchPath path
  searchPathRef.set projectSearchPath
  let a := Json.parse rawSorry
  let json ← match a with
    | .ok json => pure json
    | .error e => return .error s!"Failed to parse input as valid JSON {e}"

  let parsedSorry : ParsedSorry ← match (Lean.FromJson.fromJson? json) with
  | .ok parsedSorry => pure parsedSorry
  | .error e => return .error s!"Failed to deserialize ParsedSorry: {e}"

  let (fileMap, trees) ← extractInfoTrees path

  let targetEnvs ← trees.mapM (fun t => findTargetEnv t parsedSorry)

  let targetEnvs := targetEnvs.flatten'
  -- We might have both term-mode and tactic-mode info trees for the same source-level 'sorry'
  -- (since the 'sorry' tactic will end up emitting a 'sorry' term)
  -- We just pick the first one - as long as they all have the same type (which we check),
  -- shouldn't matter
  let some singleData := targetEnvs[0]? | return .error s!"Did not find any targetEnv"
  if !targetEnvs.all (fun d => d.type == singleData.type) then
    return .error ("Found different types for infotrees corresponding to same sorry")
  return .ok (fileMap, singleData)
