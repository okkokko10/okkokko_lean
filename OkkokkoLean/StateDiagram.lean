import Mathlib.tactic
import OkkokkoLean.Lead
import OkkokkoLean.AutomatonConfiguration
import OkkokkoLean.StateAutomaton


/-
plan:
represents a circuit diagram.

should be a StateAutomaton itself?
- maybe rather used as an internal state of one.

should support adding more StateAutomatons (is it possible to make them arbitrary I/O?)

should have "actions" that update it:
advance an automaton `n` steps -- possibly return how many steps
read whether an automaton has halted, acc/rej
read an automaton's result given it has accepted
move an automaton's result into a field
move an automaton's status into a field
move (multiple) fields into some automaton's input. this resets the automaton.

has a counter on how many steps it has done.


Do all automatons have to have identical IO to fit in?
I guess ⊕ and a wrapper that automatically rejects wrong types can be used


hold on, the mutable automata inside aren't StateAutomaton, but AutomatonConfiguration.



-/


variable {I O X : Type} (M : StateAutomaton I O) (tape : I)

-- #check Prod
structure StateDiagram (ι : Type) (X : Type) [DecidableEq ι] [DecidableEq X] where
  nodes : ι → (StateAutomaton X X)
  steps : ℕ

variable {ι : Type} [DecidableEq ι] [DecidableEq X] (D : StateDiagram ι X)

def StateDiagram.advance (i : ι) : StateDiagram ι X where
  nodes (j) := if j = i then (nodes D i) else (nodes D j)
  steps := steps D + 1
