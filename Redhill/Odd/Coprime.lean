module

public import Redhill.Common.TupleSets
public import Redhill.Odd.Defs

@[expose] public section

namespace OddCase

open Nat Finset

variable {n : ℕ} {F : Finset ℕ} {x : ℤ} (hx : ↑(Y n F) ∣ x)

lemma pairwiseCoprime_tup : PairwiseCoprime (tup n F x) := fun {i j} h ↦ by
  sorry

end OddCase
