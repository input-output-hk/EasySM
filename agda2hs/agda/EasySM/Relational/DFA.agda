-- DFA (deterministic finite automata) definitions in relational style.
--
module EasySM.Relational.DFA where

open import Level
open import Relation.Unary                        using (Pred)


-- Definition of a deterministic finite automaton
--
-- To ensure that the automaton is deterministic, we do need show that `δ` is a partial function.
--
record DFA (Q  : Set) (Σ  : Set) : Set₁ where
  field
    δ  : Q → Σ → Q -> Set   -- transition relation
    q₀ : Q                  -- initial state
    F  : Pred Q 0ℓ          -- final states
