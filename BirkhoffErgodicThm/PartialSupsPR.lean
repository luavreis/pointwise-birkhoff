import Mathlib.Tactic

lemma map_partialSups
    [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
    (f : ℕ → α) (g : F) : partialSups (g ∘ f) = g ∘ partialSups f := by
  funext n; induction n <;> simp [*]

open OrderIso in
lemma add_partialSups
    [Lattice α] [AddGroup α] [CovariantClass α α ((· + ·)) (· ≤ ·)]
    (f : ℕ → α) (c : α) : partialSups (c + f ·) n = c + partialSups f n := by
  change (partialSups (addLeft c ∘ _)) n = _
  rw [map_partialSups f (addLeft c)]; rfl

theorem partialSups_succ' [SemilatticeSup α] (f : ℕ → α) (n : ℕ) :
    partialSups f n.succ = f 0 ⊔ partialSups (f ∘ .succ) n := by
  induction' n with n hn; rfl
  nth_rw 2 [partialSups_succ]
  rw [←sup_assoc, ←hn]; rfl
