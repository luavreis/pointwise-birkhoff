import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
  birkhoffMax f φ (n + 1) x - birkhoffMax f φ n (f x)

theorem birkhoffMaxDiff_aux : birkhoffMaxDiff f φ n x = φ x - (0 ⊓ birkhoffMax f φ n (f x)) := by
  rw [sub_eq_sub_iff_add_eq_add, birkhoffMax_succ, add_assoc, add_right_inj]
  change max _ _ + min _ _ = _
  rw [max_add_min, zero_add]

lemma birkhoffMaxDiff_antitone : Antitone (birkhoffMaxDiff f φ) := by
  intro m n h x
  rw [birkhoffMaxDiff_aux, birkhoffMaxDiff_aux]
  apply add_le_add_left
  simp
  right
  exact (birkhoffMax f φ).monotone' h _

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

section InvariantFun

def Function.isInvariant (f : α → α) (φ : α → β) : Prop := φ ∘ f = φ

end InvariantFun

section InvariantSetsSpace

open MeasureTheory

def invariantSets [ms : MeasurableSpace α] (f : α → α) : MeasurableSpace α where
  MeasurableSet' s := ms.MeasurableSet' s ∧ f⁻¹' s = s
  measurableSet_empty := by
    constructor
    · exact ms.measurableSet_empty
    · rfl
  measurableSet_compl s hs := by
    constructor
    · exact ms.measurableSet_compl s hs.1
    · simp; exact hs.right
  measurableSet_iUnion s hs := by
    constructor
    · exact ms.measurableSet_iUnion s (λ i ↦ (hs i).left)
    · simp; exact Set.iUnion_congr (λ i ↦ (hs i).right)

theorem invariantSets_le [ms : MeasurableSpace α] :
    invariantSets f ≤ ms := λ _ hs => hs.1

theorem InvAlg.invariant_of_measurable
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (f : α → α) (φ : α → β) (hφ : Measurable[invariantSets f] φ) :
    Function.isInvariant f φ := by
  funext x
  suffices x ∈ f⁻¹' (φ⁻¹' {φ x}) by simpa
  rw [(hφ $ measurableSet_singleton (φ x)).2]
  rfl

end InvariantSetsSpace


noncomputable section BirkhoffThm

open MeasureTheory Filter Topology

variable {α : Type*} [msα : MeasurableSpace α] (μ : Measure α := by volume_tac)
        [hμ : IsProbabilityMeasure μ]

def birkhoffSup (f : α → α) (φ : α → ℝ) (x : α) : EReal :=
  iSup λ n ↦ ↑(birkhoffSum f φ (n + 1) x)

lemma birkhoffSup_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSup f φ) := by
  unfold birkhoffSup
  measurability

def divergentSet (f : α → α) (φ : α → ℝ) : Set α := (birkhoffSup f φ)⁻¹' {⊤}

lemma divergentSet_invariant : f x ∈ divergentSet f φ ↔ x ∈ divergentSet f φ := by
  constructor
  all_goals
    intro hx
    simp [divergentSet, birkhoffSup, iSup_eq_top] at *
    intro M hM
    cases' M using EReal.rec with a
    · use 0; apply EReal.bot_lt_coe
    case h_top => contradiction
  case mp =>
    cases' hx ↑(- φ x + a) (EReal.coe_lt_top _) with N hN
    norm_cast at *
    rw [neg_add_lt_iff_lt_add, ←birkhoffSum_succ'] at hN
    use N + 1
  case mpr =>
    cases' hx ↑(φ x + a) (EReal.coe_lt_top _) with N hN
    norm_cast at *
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
        norm_cast at hNN
        apply lt_trans hN hNN
    · use N

lemma divergentSet_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet (divergentSet f φ) := by
  apply measurableSet_preimage (birkhoffSup_measurable hf hφ)
  apply measurableSet_singleton

lemma divergentSet_mem_invalg
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet[invariantSets f] (divergentSet f φ) :=
  /- should be `Set.ext divergentSet_invariant` but it is VERY slow -/
  ⟨divergentSet_measurable hf hφ, funext (λ _ ↦ propext divergentSet_invariant)⟩

lemma birkhoffMax_tendsto_top_mem_divergentSet (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMax f φ · x) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  simp [divergentSet, birkhoffSup, iSup_eq_top] at hx
  cases' hx b (EReal.coe_lt_top _) with N hN
  norm_cast at hN
  use N
  intro n hn
  apply le_trans (le_of_lt hN)
  exact le_partialSups_of_le (birkhoffSum f φ ∘ .succ) hn x

lemma birkhoffMaxDiff_tendsto_of_mem_divergentSet (hx : x ∈ divergentSet f φ) :
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

def birkhoffLimsup (f : α → α) (φ : α → ℝ) (x : α) :=
  limsup (λ n ↦ (birkhoffAverage ℝ f φ n x).toEReal) atTop

lemma limsup_birkhoffAverage_nonpos_of_not_mem_divergentSet
    (hx : x ∉ divergentSet f φ) : birkhoffLimsup f φ x ≤ 0 := by
  /- it suffices to show there are upper bounds ≤ ε for all ε > 0 -/
  apply le_of_forall_le_of_dense
  intro ε' hε

  /- it suffices show for ε in ℝ -/
  cases' ε' using EReal.rec with ε
  case h_bot => contradiction
  case h_top => exact le_top
  norm_cast at hε

  /- from `hx` hypothesis, the birkhoff sums are bounded above -/
  simp [divergentSet, birkhoffSup, iSup_eq_top] at hx
  rcases hx with ⟨M', M_lt_top, M_is_bound⟩

  /- the upper bound is, in fact, a real number -/
  cases' M' using EReal.rec with M
  case h_bot => exfalso; exact (EReal.bot_lt_coe _).not_le (M_is_bound 0)
  case h_top => contradiction
  norm_cast at M_is_bound

  /- use archimedian property of reals -/
  cases' Archimedean.arch M hε with N hN
  have upperBound (n : ℕ) (hn : N ≤ n) : birkhoffAverage ℝ f φ (n + 1) x < ε
  · have : M < (n + 1) • ε
    · exact hN.trans_lt $ smul_lt_smul_of_pos_right (Nat.lt_succ_of_le hn) hε
    rw [nsmul_eq_smul_cast ℝ] at this
    apply (inv_smul_lt_iff_of_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ n))).mpr
    exact (M_is_bound n).trans_lt this

  /- conclusion -/
  apply sInf_le; simp
  use N + 1
  intro n hn
  specialize upperBound n.pred (Nat.le_pred_of_lt hn)
  rw [←Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hn)]
  apply le_of_lt upperBound


/- From now on, assume f is measure-preserving and φ is integrable. -/
variable {f : α → α} (hf : MeasurePreserving f μ μ)
         {φ : α → ℝ} (hφ : Integrable φ μ) (hφ' : Measurable φ) /- seems necessary? -/

lemma iterates_integrable : Integrable (φ ∘ f^[i]) μ := by
  apply (integrable_map_measure _ _).mp
  · rwa [(hf.iterate i).map_eq]
  · rw [(hf.iterate i).map_eq]
    exact hφ.aestronglyMeasurable
  exact (hf.iterate i).measurable.aemeasurable

lemma birkhoffSum_integrable : Integrable (birkhoffSum f φ n) μ := by
  unfold birkhoffSum
  apply integrable_finset_sum
  intros
  exact iterates_integrable μ hf hφ

lemma birkhoffMax_integrable : Integrable (birkhoffMax f φ n) μ := by
  unfold birkhoffMax
  induction' n with n hn
  · simpa
  · simp
    exact Integrable.sup hn (birkhoffSum_integrable μ hf hφ)

lemma birkhoffMaxDiff_integrable : Integrable (birkhoffMaxDiff f φ n) μ := by
  unfold birkhoffMaxDiff
  apply Integrable.sub
  · exact birkhoffMax_integrable μ hf hφ
  · apply (integrable_map_measure _ _).mp
    · rw [hf.map_eq]
      exact (birkhoffMax_integrable μ hf hφ)
    · rw [hf.map_eq]
      exact (birkhoffMax_integrable μ hf hφ).aestronglyMeasurable
    exact hf.measurable.aemeasurable

lemma abs_le_bound {a b c : ℝ} : a ≤ b → b ≤ c → abs b ≤ max (abs a) (abs c) := by
  simp_rw [abs_eq_max_neg, max_le_iff]
  aesop

lemma int_birkhoffMaxDiff_in_divergentSet_tendsto :
    Tendsto (λ n ↦ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ) atTop
            (𝓝 $ ∫ x in divergentSet f φ, φ x ∂ μ) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (abs φ ⊔ abs (birkhoffMaxDiff f φ 0))
  · intro n
    exact (birkhoffMaxDiff_integrable μ hf hφ).aestronglyMeasurable.restrict
  · apply Integrable.sup <;> apply Integrable.abs
    · exact hφ.restrict
    · exact (birkhoffMaxDiff_integrable μ hf hφ).restrict
  · intro n
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    apply abs_le_bound
    · rw [birkhoffMaxDiff_aux]; simp
    · apply birkhoffMaxDiff_antitone (zero_le n)
  · apply (ae_restrict_iff' _).mpr
    · apply ae_of_all
      intro x hx
      apply birkhoffMaxDiff_tendsto_of_mem_divergentSet hx
    · exact divergentSet_measurable hf.measurable hφ'

lemma int_birkhoffMaxDiff_in_divergentSet_nonneg :
    0 ≤ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ := by
  unfold birkhoffMaxDiff
  have : (μ.restrict (divergentSet f φ)).map f = μ.restrict (divergentSet f φ)
  · nth_rw 1 [
      ←(divergentSet_mem_invalg hf.measurable hφ').2,
      ←μ.restrict_map hf.measurable (divergentSet_measurable hf.measurable hφ'),
      hf.map_eq
    ]
  have mi {n : ℕ} := birkhoffMax_integrable μ hf hφ (n := n)
  have mm {n : ℕ} := birkhoffMax_measurable hf.measurable hφ' (n := n)
  rw [integral_sub, sub_nonneg]
  · rw [←integral_map (hf.aemeasurable.restrict) mm.aestronglyMeasurable, this]
    apply integral_mono mi.restrict mi.restrict ((birkhoffMax f φ).monotone (Nat.le_succ _))
  · exact mi.restrict
  · apply (integrable_map_measure mm.aestronglyMeasurable hf.aemeasurable.restrict).mp
    rw [this]
    exact mi.restrict

lemma int_in_divergentSet_nonneg : 0 ≤ ∫ x in divergentSet f φ, φ x ∂μ :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds
    (int_birkhoffMaxDiff_in_divergentSet_tendsto μ hf hφ hφ')
    (λ _ ↦ int_birkhoffMaxDiff_in_divergentSet_nonneg μ hf hφ hφ')

/- these seem to be missing? -/
lemma nullMeasurableSpace_le [ms : MeasurableSpace α] {μ : Measure α} :
    ms ≤ NullMeasurableSpace.instMeasurableSpace (α := α) (μ := μ) :=
  λ s hs ↦ ⟨s, hs, ae_eq_refl s⟩

lemma divergentSet_zero_meas_of_condexp_neg
    (h : ∀ᵐ x ∂μ, (μ[φ|invariantSets f]) x < 0) :
    μ (divergentSet f φ) = 0 := by
  have pos : ∀ᵐ x ∂μ.restrict (divergentSet f φ), 0 < -(μ[φ|invariantSets f]) x
  · apply ae_restrict_of_ae
    exact h.mono λ _ hx ↦ neg_pos.mpr hx
  have ds_meas := divergentSet_mem_invalg hf.measurable hφ'
  by_contra hm; simp_rw [←pos_iff_ne_zero] at hm
  have : ∫ x in divergentSet f φ, φ x ∂μ < 0
  · rw [←set_integral_condexp invariantSets_le hφ ds_meas]
    rw [←Left.neg_pos_iff, ←integral_neg, integral_pos_iff_support_of_nonneg_ae]
    · unfold Function.support
      rw [(ae_iff_measure_eq _).mp]
      · rwa [Measure.restrict_apply_univ _]
      · conv in _ ≠ _ => rw [ne_comm]
        exact Eventually.ne_of_lt pos
      · apply measurableSet_support
        apply (stronglyMeasurable_condexp).measurable.neg.le
        apply le_trans invariantSets_le nullMeasurableSpace_le
    · exact ae_le_of_ae_lt pos
    · exact integrable_condexp.restrict.neg
  exact this.not_le (int_in_divergentSet_nonneg μ hf hφ hφ')

lemma limsup_birkhoffAverage_nonpos_of_condexp_neg
    (h : ∀ᵐ x ∂μ, (μ[φ|invariantSets f]) x < 0) : birkhoffLimsup f φ ≤ᵐ[μ] 0 := by
  apply Eventually.mono _ λ _ ↦ limsup_birkhoffAverage_nonpos_of_not_mem_divergentSet
  apply ae_iff.mpr; simp
  exact divergentSet_zero_meas_of_condexp_neg μ hf hφ hφ' h

/- can't find those -/
lemma Filter.EventuallyEq.add_right {f : Filter α} {f₁ f₂ f₃ : α → ℝ} (h : f₁ =ᶠ[f] f₂) :
    f₁ + f₃ =ᶠ[f] f₂ + f₃ := h.mono λ x hx ↦ by simp [hx]
lemma Filter.EventuallyEq.add_left {f : Filter α} {f₁ f₂ f₃ : α → ℝ} (h : f₁ =ᶠ[f] f₂) :
    f₃ + f₁ =ᶠ[f] f₃ + f₂ := h.mono λ x hx ↦ by simp [hx]

theorem birkhoffErgodicTheorem_aux (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f φ · x) atTop ≤ (μ[φ|invariantSets f]) x + ε := by

  let φ' := (φ - (μ[φ|invariantSets f])) - (λ _ ↦ ε)
  have φ'int : Integrable φ' μ := (hφ.sub integrable_condexp).sub (integrable_const _)
  have φ'meas : Measurable φ'
  · suffices Measurable (μ[φ|invariantSets f]) by measurability
    exact stronglyMeasurable_condexp.measurable.le (invariantSets_le)

  have : μ[φ'|invariantSets f] =ᵐ[μ] -(λ _ ↦ ε)
  · calc μ[φ'|invariantSets f]
      _ =ᵐ[μ] _ - _ := condexp_sub (hφ.sub integrable_condexp) (integrable_const _)
      _ =ᵐ[μ] _ - _ - _ := (condexp_sub hφ integrable_condexp).add_right
      _ =ᵐ[μ] _ - _ - _ := (condexp_condexp_of_le (le_of_eq rfl)
                            invariantSets_le).neg.add_left.add_right
      _ = - μ[(λ _ ↦ ε)|invariantSets f] := by simp
      _ = - (λ _ ↦ ε) := by rw [condexp_const invariantSets_le]

  have : ∀ᵐ x ∂μ, (μ[φ'|invariantSets f]) x < 0 := this.mono λ x hx ↦ by simp [hx, hε]
  have := limsup_birkhoffAverage_nonpos_of_condexp_neg μ hf φ'int φ'meas this

  sorry
