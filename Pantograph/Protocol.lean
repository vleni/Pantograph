/-
All the command input/output structures are stored here

Note that no command other than `InteractionError` may have `error` as one of
its field names to avoid confusion with error messages generated by the REPL.
-/
import Lean.Data.Json

namespace Pantograph.Protocol


/-- Main Option structure, placed here to avoid name collision -/
structure Options where
  -- When false, suppress newlines in Json objects. Useful for machine-to-machine interaction.
  -- This should be  false` by default to avoid any surprises with parsing.
  printJsonPretty: Bool    := false
  -- When enabled, pretty print every expression
  printExprPretty: Bool    := true
  -- When enabled, print the raw AST of expressions
  printExprAST: Bool       := false
  -- When enabled, the types and values of persistent variables in a goal
  -- are not shown unless they are new to the proof step. Reduces overhead.
  -- NOTE: that this assumes the type and assignment of variables can never change.
  noRepeat: Bool := false
  -- See `pp.auxDecls`
  printAuxDecls: Bool      := false
  -- See `pp.implementationDetailHyps`
  printImplementationDetailHyps: Bool := false
  deriving Lean.ToJson

abbrev OptionsT := ReaderT Options

--- Expression Objects ---

structure BoundExpression where
  binders: Array (String × String)
  target: String
  deriving Lean.ToJson
structure Expression where
  -- Pretty printed expression
  pp?: Option String             := .none
  -- AST structure
  sexp?: Option String           := .none
  deriving Lean.ToJson

structure Variable where
  /-- The internal name used in raw expressions -/
  name: String := ""
  /-- The name displayed to the user -/
  userName: String
  /-- Does the name contain a dagger -/
  isInaccessible?: Option Bool := .none
  type?: Option Expression  := .none
  value?: Option Expression := .none
  deriving Lean.ToJson
structure Goal where
  name: String := ""
  /-- Name of the metavariable -/
  userName?: Option String  := .none
  /-- Is the goal in conversion mode -/
  isConversion: Bool        := false
  /-- target expression type -/
  target: Expression
  /-- Variables -/
  vars: Array Variable      := #[]
  deriving Lean.ToJson



--- Individual Commands and return types ---

structure Command where
  cmd: String
  payload: Lean.Json
  deriving Lean.FromJson

structure InteractionError where
  error: String
  desc: String
  deriving Lean.ToJson


--- Individual command and return types ---


structure Reset where
  deriving Lean.FromJson
structure Stat where
  deriving Lean.FromJson
structure StatResult where
  -- Number of goals states
  nGoals: Nat
  deriving Lean.ToJson

-- Return the type of an expression
structure ExprEcho where
  expr: String
  deriving Lean.FromJson
structure ExprEchoResult where
  expr: Expression
  type: Expression
  deriving Lean.ToJson

-- Print all symbols in environment
structure LibCatalog where
  deriving Lean.FromJson
structure LibCatalogResult where
  symbols: Array String
  deriving Lean.ToJson
-- Print the type of a symbol
structure LibInspect where
  name: String
  -- If true/false, show/hide the value expressions; By default definitions
  -- values are shown and theorem values are hidden.
  value?: Option Bool := .some false
  deriving Lean.FromJson
structure LibInspectResult where
  type: Expression
  value?: Option Expression := .none
  module?: Option String
  deriving Lean.ToJson

/-- Set options; See `Options` struct above for meanings -/
structure OptionsSet where
  printJsonPretty?: Option Bool
  printExprPretty?: Option Bool
  printExprAST?: Option Bool
  noRepeat?: Option Bool
  printAuxDecls?: Option Bool
  printImplementationDetailHyps?: Option Bool
  deriving Lean.FromJson
structure OptionsSetResult where
  deriving Lean.ToJson
structure OptionsPrint where
  deriving Lean.FromJson
abbrev OptionsPrintResult := Options

structure GoalStart where
  -- Only one of the fields below may be populated.
  expr: Option String     -- Directly parse in an expression
  copyFrom: Option String -- Copy the type from a theorem in the environment
  deriving Lean.FromJson
structure GoalStartResult where
  stateId: Nat := 0
  deriving Lean.ToJson
structure GoalTactic where
  -- Identifiers for tree, state, and goal
  stateId: Nat
  goalId: Nat := 0
  -- One of the fields here must be filled
  tactic?: Option String := .none
  expr?: Option String := .none
  deriving Lean.FromJson
structure GoalTacticResult where
  -- The next goal state id. Existence of this field shows success
  nextStateId?: Option Nat          := .none
  -- If the array is empty, it shows the goals have been fully resolved.
  goals?: Option (Array Goal)          := .none

  -- Existence of this field shows tactic execution failure
  tacticErrors?: Option (Array String) := .none

  -- Existence of this field shows the tactic parsing has failed
  parseError?: Option String := .none
  deriving Lean.ToJson

-- Remove goal states
structure GoalDelete where
  stateIds: List Nat
  deriving Lean.FromJson
structure GoalDeleteResult where
  deriving Lean.ToJson

structure GoalPrint where
  stateId: Nat
  deriving Lean.FromJson
structure GoalPrintResult where
  -- The root expression
  root?: Option Expression
  deriving Lean.ToJson

-- Diagnostic Options, not available in REPL
structure GoalDiag where
  printContext: Bool := true
  printValue: Bool := true
  printNewMVars: Bool := false
  -- Print all mvars
  printAll: Bool := false


end Pantograph.Protocol