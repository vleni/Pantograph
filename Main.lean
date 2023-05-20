import Lean.Data.Json
import Lean.Environment

import Pantograph.Commands
import Pantograph.IO
import Pantograph.Symbols

namespace Pantograph

/-- Stores state of the REPL -/
structure State where
  environments: Array Lean.Environment

-- State monad
abbrev T (m: Type → Type) := StateT State m
abbrev Subroutine α := ExceptT String (T IO) α

def nextId (s: State): Nat := s.environments.size

def State.getEnv (state: State) (id: Nat): Except String Lean.Environment :=
  match state.environments.get? id with
  | .some env => return env
  | .none => throw s!"Invalid environment id {id}"


-- Utilities
def option_expect (o: Option α) (error: String): Except String α :=
  match o with
  | .some value => return value
  | .none => throw error

structure Command where
  cmd: String
  payload: Lean.Json
  deriving Lean.FromJson

/-- Parse a command either in `{ "cmd": ..., "payload": ... }` form or `cmd { ... }` form. -/
def parse_command (s: String): Except String Command := do
  let s := s.trim
  match s.get? 0 with
  | .some '{' => -- Parse in Json mode
    Lean.fromJson? (← Lean.Json.parse s)
  | .some _ => -- Parse in line mode
    let offset := s.posOf ' ' |> s.offsetOfPos
    if offset = s.length then
      return { cmd := s.take offset, payload := Lean.Json.null }
    else
      let payload ← s.drop offset |> Lean.Json.parse
      return { cmd := s.take offset, payload := payload }
  | .none => throw "Command is empty"



open Commands

unsafe def execute (command: String): ExceptT String (T IO) Lean.Json := do
  let command: Command ← parse_command command
  match command.cmd with
  | "create" =>
    let args: Commands.Create ← Lean.fromJson? command.payload
    let ret ← create args
    return Lean.toJson ret
  | "catalog" =>
    let args: Commands.Catalog ← Lean.fromJson? command.payload
    let ret ← catalog args
    return Lean.toJson ret
  | "clear" =>
    -- Delete all the environments
    let ret ← clear
    return Lean.toJson ret
  | "inspect" =>
    let args: Commands.Inspect ← Lean.fromJson? command.payload
    let ret ← inspect args
    return Lean.toJson ret
  | "proof.trace" =>
    let args: Commands.ProofTrace ← Lean.fromJson? command.payload
    let ret ← proof_trace args
    return Lean.toJson ret
  | cmd => throw s!"Unknown verb: {cmd}"
  where
  create (args: Create): Subroutine CreateResult := do
    let state ← get
    let id := nextId state
    let env ← Lean.importModules
      (imports := args.imports.map (λ str => { module := strToName str, runtimeOnly := false }))
      (opts := {})
      (trustLevel := 1)
    modify fun s => { environments := s.environments.push env }
    let num_filtered_symbols := env.constants.fold (init := 0) (λ acc name info =>
      acc + if is_symbol_unsafe_or_internal name info then 0 else 1)
    return {
      id := id,
      symbols := env.constants.size,
      filtered_symbols := num_filtered_symbols }
  catalog (args: Catalog): Subroutine CatalogResult := do
    let state ← get
    let env ← state.getEnv args.id
    let names := env.constants.fold (init := []) (λ es name info =>
      match to_filtered_symbol name info with
      | .some x => x::es
      | .none => es)
    return { theorems := names }
  clear: Subroutine ClearResult := do
    let state ← get
    for env in state.environments do
      env.freeRegions
    return { n := state.environments.size }
  inspect (args: Inspect): Subroutine InspectResult := do
    let state ← get
    let env ← state.getEnv args.id
    let info? := env.find? <| strToName args.symbol
    let info ← match info? with
      | none => throw s!"Symbol not found: {args.symbol}"
      | some info => pure info.toConstantVal
    -- Now print the type expression
    let format := IO.exprToStr env info.type
    return { type := format }
  proof_trace (args: ProofTrace): Subroutine ProofTraceResult := do
    -- Step 1: Create tactic state
    -- Step 2: Execute tactic
    -- Step 3: ??
    return { expr := "test" }


end Pantograph

open Pantograph



-- Main IO functions

unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "" => pure ""
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

unsafe def loop : T IO Unit := do
  let command ← getLines
  if command == "" then return ()
  let ret ← execute command
  match ret with
  | .error e => IO.println s!"Error: {e}"
  | .ok obj => IO.println <| toString <| obj
  loop

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  StateT.run' loop ⟨#[]⟩
