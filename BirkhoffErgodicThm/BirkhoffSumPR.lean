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

lemma birkhoffAverage_neg
    [AddCommMonoid M] [DivisionSemiring R] [Module R M] [Neg M] {φ : α → M} :
    birkhoffAverage R f (-φ) n x = - birkhoffAverage R f φ n x := sorry
