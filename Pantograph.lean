import Pantograph.Goal
import Pantograph.Protocol
import Pantograph.Serial
import Pantograph.Symbol
import Lean.Data.HashMap

namespace Pantograph

structure Context where
  imports: List String

/-- Stores state of the REPL -/
structure State where
  options: Protocol.Options := {}
  nextId: Nat := 0
  goalStates: Lean.HashMap Nat GoalState := Lean.HashMap.empty

/-- Main state monad for executing commands -/
abbrev MainM := ReaderT Context (StateT State Lean.Elab.TermElabM)
-- HACK: For some reason writing `CommandM α := MainM (Except ... α)` disables
-- certain monadic features in `MainM`
abbrev CR α := Except Protocol.InteractionError α

def execute (command: Protocol.Command): MainM Lean.Json := do
  let run { α β: Type } [Lean.FromJson α] [Lean.ToJson β] (comm: α → MainM (CR β)): MainM Lean.Json :=
    match Lean.fromJson? command.payload with
    | .ok args => do
      match (← comm args) with
      | .ok result =>  return Lean.toJson result
      | .error ierror => return Lean.toJson ierror
    | .error error => return Lean.toJson $ errorCommand s!"Unable to parse json: {error}"
  match command.cmd with
  | "reset"         => run reset
  | "stat"          => run stat
  | "expr.echo"     => run expr_echo
  | "lib.catalog"   => run lib_catalog
  | "lib.inspect"   => run lib_inspect
  | "options.set"   => run options_set
  | "options.print" => run options_print
  | "goal.start"    => run goal_start
  | "goal.tactic"   => run goal_tactic
  | "goal.continue" => run goal_continue
  | "goal.delete"   => run goal_delete
  | "goal.print"    => run goal_print
  | cmd =>
    let error: Protocol.InteractionError :=
      errorCommand s!"Unknown command {cmd}"
    return Lean.toJson error
  where
  errorI (type desc: String): Protocol.InteractionError := { error := type, desc := desc }
  errorCommand := errorI "command"
  errorIndex := errorI "index"
  -- Command Functions
  reset (_: Protocol.Reset): MainM (CR Protocol.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    set { state with nextId := 0, goalStates := Lean.HashMap.empty }
    return .ok { nGoals }
  stat (_: Protocol.Stat): MainM (CR Protocol.StatResult) := do
    let state ← get
    let nGoals := state.goalStates.size
    return .ok { nGoals }
  lib_catalog (_: Protocol.LibCatalog): MainM (CR Protocol.LibCatalogResult) := do
    let env ← Lean.MonadEnv.getEnv
    let names := env.constants.fold (init := #[]) (λ acc name info =>
      match to_filtered_symbol name info with
      | .some x => acc.push x
      | .none => acc)
    return .ok { symbols := names }
  lib_inspect (args: Protocol.LibInspect): MainM (CR Protocol.LibInspectResult) := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    let name :=  args.name.toName
    let info? := env.find? name
    match info? with
    | none => return .error $ errorIndex s!"Symbol not found {args.name}"
    | some info =>
      let module? := env.getModuleIdxFor? name >>=
        (λ idx => env.allImportedModuleNames.get? idx.toNat) |>.map toString
      let value? := match args.value?, info with
        | .some true, _ => info.value?
        | .some false, _ => .none
        | .none, .defnInfo _ => info.value?
        | .none, _ => .none
      return .ok {
        type := ← serialize_expression state.options info.type,
        value? := ← value?.mapM (λ v => serialize_expression state.options v),
        module? := module?
      }
  expr_echo (args: Protocol.ExprEcho): MainM (CR Protocol.ExprEchoResult) := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    match syntax_from_str env args.expr with
    | .error str => return .error $ errorI "parsing" str
    | .ok syn => do
      match (← syntax_to_expr syn) with
      | .error str => return .error $ errorI "elab" str
      | .ok expr => do
        try
          let type ← Lean.Meta.inferType expr
          return .ok {
              type := (← serialize_expression (options := state.options) type),
              expr := (← serialize_expression (options := state.options) expr)
          }
        catch exception =>
          return .error $ errorI "typing" (← exception.toMessageData.toString)
  options_set (args: Protocol.OptionsSet): MainM (CR Protocol.OptionsSetResult) := do
    let state ← get
    let options := state.options
    set { state with
      options := {
        -- FIXME: This should be replaced with something more elegant
        printJsonPretty := args.printJsonPretty?.getD options.printJsonPretty,
        printExprPretty := args.printExprPretty?.getD options.printExprPretty,
        printExprAST := args.printExprAST?.getD options.printExprAST,
        noRepeat := args.noRepeat?.getD options.noRepeat,
        printAuxDecls := args.printAuxDecls?.getD options.printAuxDecls,
        printImplementationDetailHyps := args.printImplementationDetailHyps?.getD options.printImplementationDetailHyps
      }
    }
    return .ok {  }
  options_print (_: Protocol.OptionsPrint): MainM (CR Protocol.OptionsPrintResult) := do
    return .ok (← get).options
  goal_start (args: Protocol.GoalStart): MainM (CR Protocol.GoalStartResult) := do
    let state ← get
    let env ← Lean.MonadEnv.getEnv
    let expr?: Except _ Lean.Expr ← (match args.expr, args.copyFrom with
      | .some expr, .none =>
        (match syntax_from_str env expr with
        | .error str => return .error <| errorI "parsing" str
        | .ok syn => do
          (match (← syntax_to_expr syn) with
          | .error str => return .error <| errorI "elab" str
          | .ok expr => return .ok expr))
      | .none, .some copyFrom =>
        (match env.find? <| copyFrom.toName with
        | .none => return .error <| errorIndex s!"Symbol not found: {copyFrom}"
        | .some cInfo => return .ok cInfo.type)
      | _, _ =>
        return .error <| errorI "arguments" "Exactly one of {expr, copyFrom} must be supplied")
    match expr? with
    | .error error => return .error error
    | .ok expr =>
      let goalState ← GoalState.create expr
      let stateId := state.nextId
      set { state with
        goalStates := state.goalStates.insert stateId goalState,
        nextId := state.nextId + 1
      }
      return .ok { stateId, root := goalState.root.name.toString }
  goal_tactic (args: Protocol.GoalTactic): MainM (CR Protocol.GoalTacticResult) := do
    let state ← get
    match state.goalStates.find? args.stateId with
    | .none => return .error $ errorIndex s!"Invalid state index {args.stateId}"
    | .some goalState => do
      let nextGoalState?: Except _ GoalState ← match args.tactic?, args.expr? with
        | .some tactic, .none => do
          pure ( Except.ok (← GoalState.execute goalState args.goalId tactic))
        | .none, .some expr => do
          pure ( Except.ok (← GoalState.tryAssign goalState args.goalId expr))
        | _, _ => pure (Except.error <| errorI "arguments" "Exactly one of {tactic, expr} must be supplied")
      match nextGoalState? with
      | .error error => return .error error
      | .ok (.success nextGoalState) =>
        let nextStateId := state.nextId
        set { state with
          goalStates := state.goalStates.insert state.nextId nextGoalState,
          nextId := state.nextId + 1,
        }
        let goals ← nextGoalState.serializeGoals (parent := .some goalState) (options := state.options)
        return .ok {
          nextStateId? := .some nextStateId,
          goals? := .some goals,
        }
      | .ok (.parseError message) =>
        return .ok { parseError? := .some message }
      | .ok (.indexError goalId) =>
        return .error $ errorIndex s!"Invalid goal id index {goalId}"
      | .ok (.failure messages) =>
        return .ok { tacticErrors? := .some messages }
  goal_continue (args: Protocol.GoalContinue): MainM (CR Protocol.GoalContinueResult) := do
    let state ← get
    match state.goalStates.find? args.target with
    | .none => return .error $ errorIndex s!"Invalid state index {args.target}"
    | .some target => do
      let nextState? ← match args.branch?, args.goals? with
        | .some branchId, .none => do
          match state.goalStates.find? branchId with
          | .none => return .error $ errorIndex s!"Invalid state index {branchId}"
          | .some branch => pure $ target.continue branch
        | .none, .some goals =>
          let goals := goals.map (λ name => { name := name.toName })
          pure $ target.resume goals
        | _, _ => return .error <| errorI "arguments" "Exactly one of {branch, goals} must be supplied"
      match nextState? with
      | .error error => return .ok { error? := .some error }
      | .ok nextGoalState =>
        let nextStateId := state.nextId
        set { state with
          goalStates := state.goalStates.insert nextStateId nextGoalState,
          nextId := state.nextId + 1
        }
        let goals ← nextGoalState.serializeGoals (parent := .none) (options := state.options)
        return .ok {
          nextStateId? := .some nextStateId,
          goals? := .some goals,
        }
  goal_delete (args: Protocol.GoalDelete): MainM (CR Protocol.GoalDeleteResult) := do
    let state ← get
    let goalStates := args.stateIds.foldl (λ map id => map.erase id) state.goalStates
    set { state with goalStates }
    return .ok {}
  goal_print (args: Protocol.GoalPrint): MainM (CR Protocol.GoalPrintResult) := do
    let state ← get
    match state.goalStates.find? args.stateId with
    | .none => return .error $ errorIndex s!"Invalid state index {args.stateId}"
    | .some goalState => do
      let root? ← goalState.rootExpr?.mapM (λ expr => serialize_expression state.options expr)
      return .ok {
        root?,
      }

end Pantograph
