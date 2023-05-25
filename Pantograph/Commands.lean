/-
All the command input/output structures are stored here

Note that no command other than `InteractionError` may have `error` as one of
its field names to avoid confusion with error messages generated by the REPL.
-/
import Lean.Data.Json

import Pantograph.Serial

namespace Pantograph.Commands

structure Command where
  cmd: String
  payload: Lean.Json
  deriving Lean.FromJson

structure InteractionError where
  error: String
  desc: String
  deriving Lean.ToJson


-- Individual command and return types


-- Print all symbols in environment
structure Catalog where
  deriving Lean.FromJson
structure CatalogResult where
  symbols: List String
  deriving Lean.ToJson

-- Print the type of a symbol
structure Inspect where
  name: String
  deriving Lean.FromJson
structure InspectResult where
  type: String
  -- Decompose the bound expression when the type is forall.
  boundExpr?: Option BoundExpression
  module?: Option String
  deriving Lean.ToJson

structure ProofStart where
  name: Option String     -- Identifier of the proof
  -- Only one of the fields below may be populated.
  expr: Option String     -- Proof expression
  copyFrom: Option String -- Theorem name
  deriving Lean.FromJson
structure ProofStartResult where
  treeId: Nat := 0 -- Proof tree id
  deriving Lean.ToJson

structure ProofTactic where
  -- Identifiers for tree, state, and goal
  treeId: Nat
  stateId: Nat
  goalId: Option Nat
  tactic: String
  deriving Lean.FromJson
structure ProofTacticResultSuccess where
  goals: Array String
  nextId?: Option Nat -- Next proof state id
  deriving Lean.ToJson
structure ProofTacticResultFailure where
  tacticErrors: Array String -- Error messages generated by tactic
  deriving Lean.ToJson

structure ProofPrintTree where
  treeId: Nat
  deriving Lean.FromJson
structure ProofPrintTreeResult where
  -- "" if no parents, otherwise "parentId.goalId"
  parents: Array String
  deriving Lean.ToJson

end Pantograph.Commands
