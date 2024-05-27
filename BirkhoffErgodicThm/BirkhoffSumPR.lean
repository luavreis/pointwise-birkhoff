import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Tactic

open Finset in
theorem birkhoffSum_eq_of_invariant [AddCommMonoid M] {φ : α → M}
    (h : φ ∘ f = φ) : birkhoffSum f φ n = n • φ := by
  sorry

open Finset in
theorem birkhoffAverage_eq_of_invariant
    [AddCommMonoid M] [DivisionSemiring R] [Module R M] {φ : α → M}
    (h : φ ∘ f = φ) : birkhoffAverage R f φ n = φ := by
  unfold birkhoffAverage
  rw [birkhoffSum_eq_of_invariant h]
  sorry
