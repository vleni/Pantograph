import Lean

import Pantograph.Symbol

def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
  {
    msgs := log.msgs.filter fun m => match m.severity with | MessageSeverity.error => true | _ => false
  }


namespace Pantograph
open Lean

structure GoalState where
  savedState : Elab.Tactic.SavedState

  -- The root hole which is the search target
  root: MVarId
  -- New metavariables acquired in this state
  newMVars: SSet MVarId

  -- The id of the goal in the parent
  parentGoalId: Nat := 0

abbrev M := Elab.TermElabM

protected def GoalState.create (expr: Expr): M GoalState := do
  -- May be necessary to immediately synthesise all metavariables if we need to leave the elaboration context.
  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unknown.20universe.20metavariable/near/360130070

  --Elab.Term.synthesizeSyntheticMVarsNoPostponing
  --let expr ← instantiateMVars expr
  let goal := (← Meta.mkFreshExprMVar expr (kind := MetavarKind.synthetic) (userName := .anonymous))
  let savedStateMonad: Elab.Tactic.TacticM Elab.Tactic.SavedState := MonadBacktrack.saveState
  let root := goal.mvarId!
  let savedState ← savedStateMonad { elaborator := .anonymous } |>.run' { goals := [root]}
  return {
    savedState,
    root,
    newMVars := SSet.insert .empty root,
  }
protected def GoalState.goals (state: GoalState): List MVarId := state.savedState.tactic.goals

protected def GoalState.runM {α: Type} (state: GoalState) (m: Elab.TermElabM α) : M α := do
  state.savedState.term.restore
  m

protected def GoalState.mctx (state: GoalState): MetavarContext :=
  state.savedState.term.meta.meta.mctx
private def GoalState.mvars (state: GoalState): SSet MVarId :=
  state.mctx.decls.foldl (init := .empty) fun acc k _ => acc.insert k

/-- Inner function for executing tactic on goal state -/
def executeTactic (state: Elab.Tactic.SavedState) (goal: MVarId) (tactic: Syntax) :
    M (Except (Array String) (Elab.Tactic.SavedState × List MVarId)):= do
  let tacticM (stx: Syntax):  Elab.Tactic.TacticM (Except (Array String) (Elab.Tactic.SavedState × List MVarId)) := do
    state.restore
    Elab.Tactic.setGoals [goal]
    try
      Elab.Tactic.evalTactic stx
      if (← getThe Core.State).messages.hasErrors then
        let messages := (← getThe Core.State).messages.getErrorMessages |>.toList.toArray
        let errors ← (messages.map Message.data).mapM fun md => md.toString
        return .error errors
      else
        let unsolved ← Elab.Tactic.getUnsolvedGoals
        -- The order of evaluation is important here, since `getUnsolvedGoals` prunes the goals set
        return .ok (← MonadBacktrack.saveState, unsolved)
    catch exception =>
      return .error #[← exception.toMessageData.toString]
  tacticM tactic { elaborator := .anonymous } |>.run' state.tactic

/-- Response for executing a tactic -/
inductive TacticResult where
  -- Goes to next state
  | success (state: GoalState)
  -- Tactic failed with messages
  | failure (messages: Array String)
  -- Could not parse tactic
  | parseError (message: String)
  -- The goal index is out of bounds
  | indexError (goalId: Nat)

/-- Execute tactic on given state -/
protected def GoalState.execute (state: GoalState) (goalId: Nat) (tactic: String):
    M TacticResult := do
  let goal ← match state.savedState.tactic.goals.get? goalId with
    | .some goal => pure $ goal
    | .none => return .indexError goalId
  let tactic ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `tactic)
    (input := tactic)
    (fileName := "<stdin>") with
    | .ok stx => pure $ stx
    | .error error => return .parseError error
  match (← executeTactic (state := state.savedState) (goal := goal) (tactic := tactic)) with
  | .error errors =>
    return .failure errors
  | .ok (nextSavedState, nextGoals) =>
    assert! nextSavedState.tactic.goals.length == nextGoals.length
    -- Assert that the definition of metavariables are the same
    let nextMCtx := nextSavedState.term.meta.meta.mctx
    let prevMCtx := state.savedState.term.meta.meta.mctx
    -- Generate a list of mvarIds that exist in the parent state; Also test the
    -- assertion that the types have not changed on any mvars.
    let newMVars ← nextMCtx.decls.foldlM (fun acc mvarId mvarDecl => do
      if let .some prevMVarDecl := prevMCtx.decls.find? mvarId then
        assert! prevMVarDecl.type == mvarDecl.type
        return acc
      else
        return acc.insert mvarId
      ) SSet.empty
    return .success {
      savedState := nextSavedState
      root := state.root,
      newMVars,
      parentGoalId := goalId,
    }

/-- After finishing one branch of a proof (`graftee`), pick up from the point where the proof was left off (`target`) -/
protected def GoalState.continue (target: GoalState) (graftee: GoalState): Except String GoalState :=
  if target.root != graftee.root then
    .error s!"Roots of two continued goal states do not match: {target.root.name} != {graftee.root.name}"
  -- Ensure goals are not dangling
  else if ¬ (target.goals.all (λ goal => graftee.mvars.contains goal)) then
    .error s!"Some goals in target are not present in the graftee"
  else
    -- Set goals to the goals that have not been assigned yet, similar to the `focus` tactic.
    let unassigned := target.goals.filter (λ goal =>
      let mctx := graftee.mctx
      ¬(mctx.eAssignment.contains goal || mctx.dAssignment.contains goal))
    .ok {
      savedState := {
        term := graftee.savedState.term,
        tactic := { goals := unassigned },
      },
      root := target.root,
      newMVars := graftee.newMVars,
    }

protected def GoalState.rootExpr (goalState: GoalState): Option Expr :=
  let expr := goalState.mctx.eAssignment.find! goalState.root
  let (expr, _) := instantiateMVarsCore (mctx := goalState.mctx) (e := expr)
  if expr.hasMVar then
    -- Must not assert that the goal state is empty here. We could be in a branch goal.
    --assert! ¬goalState.goals.isEmpty
    .none
  else
    assert! goalState.goals.isEmpty
    .some expr

end Pantograph
