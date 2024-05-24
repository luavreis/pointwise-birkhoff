import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic
import BirkhoffErgodicThm.PartialSupsPR

set_option maxHeartbeats 0

section BirkhoffMax

variable {α : Type*}

/- note that we must compose with .succ, as we want to allow `birkhoffMax`
   to be negative but `birkhoffSum f φ 0 = 0`.
-/
def birkhoffMax (f : α → α) (φ : α → ℝ) : ℕ →o (α → ℝ) :=
  partialSups (birkhoffSum f φ ∘ .succ)

lemma birkhoffMax_succ : birkhoffMax f φ n.succ x = φ x + 0 ⊔ birkhoffMax f φ n (f x) := by
  have : birkhoffSum f φ ∘ .succ = λ k ↦ φ + birkhoffSum f φ k ∘ f
  · funext k x; dsimp
    rw [Nat.succ_eq_one_add, birkhoffSum_add f φ 1, birkhoffSum_one]; rfl
  nth_rw 1 [birkhoffMax, this, add_partialSups]; simp [-partialSups_succ]
  rw [partialSups_succ']; simp
  simp_rw [partialSups_apply, Function.comp_apply, ←partialSups_apply]; rfl

abbrev birkhoffMaxDiff (f : α → α) (φ : α → ℝ) (n : ℕ) (x : α) :=
  birkhoffMax f φ n.succ x - birkhoffMax f φ n (f x)

theorem birkhoffMaxDiff_aux : birkhoffMaxDiff f φ n x = φ x - (0 ⊓ birkhoffMax f φ n (f x)) := by
  rw [sub_eq_sub_iff_add_eq_add, birkhoffMax_succ, add_assoc, add_right_inj]
  change max _ _ + min _ _ = _
  rw [max_add_min, zero_add]

@[measurability]
lemma birkhoffSum_measurable [MeasurableSpace α]
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSum f φ n) := by
  apply Finset.measurable_sum
  measurability

@[measurability]
lemma birkhoffMax_measurable [MeasurableSpace α]
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffMax f φ n) := by
  induction n <;> unfold birkhoffMax <;> measurability

end BirkhoffMax


noncomputable section BirkhoffThm

open MeasureTheory Filter Topology

variable {α : Type*} [msα : MeasurableSpace α] (μ : Measure α := by volume_tac)

def birkhoffSup (f : α → α) (φ : α → ℝ) (x : α) : EReal :=
  iSup λ n ↦ ↑(birkhoffSum f φ (n + 1) x)

lemma birkhoffSup_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSup f φ) := by
  unfold birkhoffSup
  measurability

def divergentSet (f : α → α) (φ : α → ℝ) : Set α := (birkhoffSup f φ)⁻¹' {⊤}

def invSigmaAlg (f : α → α) : MeasurableSpace α where
  MeasurableSet' s := msα.MeasurableSet' s ∧ f⁻¹' s = s
  measurableSet_empty := by
    constructor
    · exact msα.measurableSet_empty
    · rfl
  measurableSet_compl s hs := by
    constructor
    · exact msα.measurableSet_compl s hs.1
    · simp; exact hs.right
  measurableSet_iUnion s hs := by
    constructor
    · exact msα.measurableSet_iUnion s (λ i ↦ (hs i).left)
    · simp; exact Set.iUnion_congr (λ i ↦ (hs i).right)

lemma divergentSet_invariant : f x ∈ divergentSet f φ ↔ x ∈ divergentSet f φ := by
  constructor
  all_goals
    intro hx
    simp [divergentSet, birkhoffSup, iSup_eq_top] at *
    intro M hM
    cases' M using EReal.rec with a
    · use 0; apply EReal.bot_lt_coe
    case h_top => contradiction
  · specialize hx ↑(- φ x + a) (EReal.coe_lt_top _)
    cases' hx with N hN
    simp_rw [EReal.coe_lt_coe_iff] at *
    rw [neg_add_lt_iff_lt_add, ←birkhoffSum_succ'] at hN
    use N + 1
  · cases' hx ↑(φ x + a) (EReal.coe_lt_top _) with N hN
    simp_rw [EReal.coe_lt_coe_iff] at *
    conv =>
      congr
      intro i
      rw [←add_lt_add_iff_left (φ x), ←birkhoffSum_succ']
    cases' N with N
    · /- ugly case! :( -/
      cases' hx ↑(birkhoffSum f φ 1 x) (EReal.coe_lt_top _) with N hNN
      cases' N with N
      · exfalso
        exact (lt_self_iff_false _).mp hNN
      · use N
        rw [EReal.coe_lt_coe_iff] at hNN
        apply lt_trans hN hNN
    · use N

lemma divergentSet_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet (divergentSet f φ) := by
  apply measurableSet_preimage (birkhoffSup_measurable hf hφ)
  apply measurableSet_singleton

lemma divergentSet_invariant'
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet[invSigmaAlg f] (divergentSet f φ) :=
  /- IMPORTANT: should be `Set.ext divergentSet_invariant` but it is VERY slow -/
  ⟨divergentSet_measurable hf hφ, funext (λ _ ↦ propext divergentSet_invariant)⟩

lemma birkhoffMax_tendsto_top_mem_divergentSet (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMax f φ · x) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  simp [divergentSet, birkhoffSup, iSup_eq_top] at hx
  cases' hx b (EReal.coe_lt_top _) with N hN
  simp [EReal.coe_lt_coe_iff] at hN
  use N
  intro n hn
  apply le_trans (le_of_lt hN)
  exact le_partialSups_of_le (birkhoffSum f φ ∘ .succ) hn x

lemma birkhoffMaxDiff_tendsto_mem_divergentSet (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMaxDiff f φ · x) atTop (𝓝 (φ x)) := by
  have hx' : f x ∈ divergentSet f φ := divergentSet_invariant.mpr hx
  simp_rw [birkhoffMaxDiff_aux]
  nth_rw 2 [←sub_zero (φ x)]
  apply Tendsto.sub tendsto_const_nhds
  have := birkhoffMax_tendsto_top_mem_divergentSet hx'
  cases' tendsto_atTop_atTop.mp this 0 with N hN
  apply tendsto_atTop_of_eventually_const (i₀ := N)
  intro i hi
  exact inf_of_le_left (hN i hi)

/- From now on, assume f is measure-preserving and φ is integrable. -/
variable {f : α → α} (hf : MeasurePreserving f μ μ) (φ : α →₁[μ] ℝ)



-- def birkhoff_ergodic
--     {f : α → α}
--     (_ : MeasurePreserving f μ μ)
--     (ψ : α → ℝ) (_ : Integrable ψ μ) : Prop :=
--   ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f ψ · x) atTop
--   (nhds ((μ[ψ|invariantSubalgebra f]) x))
