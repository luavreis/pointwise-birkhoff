import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic
import BirkhoffErgodicThm.PartialSupsPR
import BirkhoffErgodicThm.BirkhoffSumPR
import BirkhoffErgodicThm.FilterPR

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
  simp_rw [partialSups_apply, Function.comp_apply, ← partialSups_apply]; rfl

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

section InvariantSets

open MeasureTheory

def invariantSets [ms : MeasurableSpace α] (f : α → α) : MeasurableSpace α where
  MeasurableSet' s := ms.MeasurableSet' s ∧ f⁻¹' s = s
  measurableSet_empty := ⟨ms.measurableSet_empty, rfl⟩
  measurableSet_compl s hs := ⟨ms.measurableSet_compl s hs.1, (by simp [hs.right])⟩
  measurableSet_iUnion s hs := ⟨ms.measurableSet_iUnion s (λ i ↦ (hs i).left),
    by simp; exact Set.iUnion_congr (λ i ↦ (hs i).right)⟩

theorem invariantSets_le [ms : MeasurableSpace α] : invariantSets f ≤ ms := λ _ hs => hs.1

theorem InvariantSets.invariant_of_measurable
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (f : α → α) (φ : α → β) (hφ : Measurable[invariantSets f] φ) :
    φ ∘ f = φ := by
  funext x
  suffices x ∈ f⁻¹' (φ⁻¹' {φ x}) by simpa
  rw [(hφ $ measurableSet_singleton (φ x)).2]
  rfl

end InvariantSets

noncomputable section BirkhoffThm

open MeasureTheory Filter Topology

variable {α : Type*} [msα : MeasurableSpace α] (μ : Measure α := by volume_tac)
        [hμ : IsProbabilityMeasure μ]

def birkhoffSup (f : α → α) (φ : α → ℝ) (x : α) : EReal := iSup λ n ↦ ↑(birkhoffSum f φ (n + 1) x)

lemma birkhoffSup_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    Measurable (birkhoffSup f φ) := measurable_iSup
  (fun _ ↦ Measurable.coe_real_ereal (birkhoffSum_measurable hf hφ))

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
    rw [neg_add_lt_iff_lt_add, ← birkhoffSum_succ'] at hN
    use N + 1
  case mpr =>
    cases' hx ↑(φ x + a) (EReal.coe_lt_top _) with N hN
    norm_cast at *
    conv =>
      congr
      intro i
      rw [← add_lt_add_iff_left (φ x), ← birkhoffSum_succ']
    cases' N with N
    · /- ugly case! :( -/
      cases' hx ↑(birkhoffSum f φ 1 x) (EReal.coe_lt_top _) with N hNN
      cases' N with N
      · exfalso; exact (lt_self_iff_false _).mp hNN
      · use N
        norm_cast at hNN
        exact lt_trans hN hNN
    · use N

lemma divergentSet_measurable
    {f : α → α} (hf : Measurable f)
    {φ : α → ℝ} (hφ : Measurable φ) :
    MeasurableSet (divergentSet f φ) :=
      measurableSet_preimage (birkhoffSup_measurable hf hφ) (measurableSet_singleton _)

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
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top] at hx
  cases' hx b (EReal.coe_lt_top _) with N hN
  norm_cast at hN
  use N
  exact fun n hn ↦ le_trans (le_of_lt hN) (le_partialSups_of_le (birkhoffSum f φ ∘ .succ) hn x )

lemma birkhoffMaxDiff_tendsto_of_mem_divergentSet (hx : x ∈ divergentSet f φ) :
    Tendsto (birkhoffMaxDiff f φ · x) atTop (𝓝 (φ x)) := by
  have hx' : f x ∈ divergentSet f φ := divergentSet_invariant.mpr hx
  simp_rw [birkhoffMaxDiff_aux]
  nth_rw 2 [← sub_zero (φ x)]
  apply Tendsto.sub tendsto_const_nhds
  cases' tendsto_atTop_atTop.mp (birkhoffMax_tendsto_top_mem_divergentSet hx') 0 with N hN
  exact tendsto_atTop_of_eventually_const (i₀ := N) fun i hi ↦ inf_of_le_left (hN i hi)

abbrev nonneg : Filter ℝ := ⨅ ε > 0, 𝓟 (Set.Iio ε)

lemma birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet
    (hx : x ∉ divergentSet f φ) :
    Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  /- it suffices to show there are upper bounds ≤ ε for all ε > 0 -/
  simp only [tendsto_iInf, gt_iff_lt, tendsto_principal, Set.mem_Iio, eventually_atTop, ge_iff_le]
  intro ε hε

  /- from `hx` hypothesis, the birkhoff sums are bounded above -/
  simp only [divergentSet, Set.mem_preimage, birkhoffSup, Set.mem_singleton_iff, iSup_eq_top,
    not_forall, not_exists, not_lt, exists_prop] at hx
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
    · rw [nsmul_eq_smul_cast ℝ] at this
      exact (inv_smul_lt_iff_of_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ n))).mpr
        ((M_is_bound n).trans_lt this)

  /- conclusion -/
  use N + 1
  intro n hn
  specialize upperBound n.pred (Nat.le_pred_of_lt hn)
  rwa [← Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hn)]

/- From now on, assume f is measure-preserving and φ is integrable. -/
variable {f : α → α} (hf : MeasurePreserving f μ μ)
         {φ : α → ℝ} (hφ : Integrable φ μ) (hφ' : Measurable φ) /- seems necessary? -/

lemma iterates_integrable : Integrable (φ ∘ f^[i]) μ := by
  apply (integrable_map_measure _ _).mp
  · rwa [(hf.iterate i).map_eq]
  · rw [(hf.iterate i).map_eq]
    exact hφ.aestronglyMeasurable
  exact (hf.iterate i).measurable.aemeasurable

lemma birkhoffSum_integrable : Integrable (birkhoffSum f φ n) μ :=
  integrable_finset_sum _ fun _ _ ↦ iterates_integrable μ hf hφ

lemma birkhoffMax_integrable : Integrable (birkhoffMax f φ n) μ := by
  unfold birkhoffMax
  induction' n with n hn
  · simpa
  · rw [partialSups_succ, Function.comp_apply]
    exact Integrable.sup hn (birkhoffSum_integrable μ hf hφ)

lemma birkhoffMaxDiff_integrable : Integrable (birkhoffMaxDiff f φ n) μ := by
  apply Integrable.sub (birkhoffMax_integrable μ hf hφ)
  apply (integrable_map_measure _ hf.measurable.aemeasurable).mp <;> rw [hf.map_eq]
  · exact birkhoffMax_integrable μ hf hφ
  · exact (birkhoffMax_integrable μ hf hφ).aestronglyMeasurable

lemma abs_le_bound {a b c : ℝ} : a ≤ b → b ≤ c → abs b ≤ max (abs a) (abs c) := by
  simp_rw [abs_eq_max_neg, max_le_iff]; aesop

lemma int_birkhoffMaxDiff_in_divergentSet_tendsto :
    Tendsto (λ n ↦ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ) atTop
            (𝓝 $ ∫ x in divergentSet f φ, φ x ∂ μ) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (abs φ ⊔ abs (birkhoffMaxDiff f φ 0))
  · exact fun _ ↦ (birkhoffMaxDiff_integrable μ hf hφ).aestronglyMeasurable.restrict
  · apply Integrable.sup <;> apply Integrable.abs
    · exact hφ.restrict
    · exact (birkhoffMaxDiff_integrable μ hf hφ).restrict
  · intro n
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le_bound (by simp [birkhoffMaxDiff_aux]) (birkhoffMaxDiff_antitone (zero_le n) _)
  · exact (ae_restrict_iff' (divergentSet_measurable hf.measurable hφ')).mpr
      (ae_of_all _ fun _ hx ↦ birkhoffMaxDiff_tendsto_of_mem_divergentSet hx)

lemma int_birkhoffMaxDiff_in_divergentSet_nonneg :
    0 ≤ ∫ x in divergentSet f φ, birkhoffMaxDiff f φ n x ∂μ := by
  unfold birkhoffMaxDiff
  have : (μ.restrict (divergentSet f φ)).map f = μ.restrict (divergentSet f φ)
  · nth_rw 1 [
      ← (divergentSet_mem_invalg hf.measurable hφ').2,
      ← μ.restrict_map hf.measurable (divergentSet_measurable hf.measurable hφ'),
      hf.map_eq
    ]
  have mi {n : ℕ} := birkhoffMax_integrable μ hf hφ (n := n)
  have mm {n : ℕ} := birkhoffMax_measurable hf.measurable hφ' (n := n)
  rw [integral_sub, sub_nonneg]
  · rw [← integral_map (hf.aemeasurable.restrict) mm.aestronglyMeasurable, this]
    exact integral_mono mi.restrict mi.restrict ((birkhoffMax f φ).monotone (Nat.le_succ _))
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
  · exact ae_restrict_of_ae (h.mono λ _ hx ↦ neg_pos.mpr hx)
  have ds_meas := divergentSet_mem_invalg hf.measurable hφ'
  by_contra hm; simp_rw [← pos_iff_ne_zero] at hm
  have : ∫ x in divergentSet f φ, φ x ∂μ < 0
  · rw [← set_integral_condexp invariantSets_le hφ ds_meas,
      ← Left.neg_pos_iff, ← integral_neg, integral_pos_iff_support_of_nonneg_ae]
    · unfold Function.support
      rw [(ae_iff_measure_eq _).mp]
      · rwa [Measure.restrict_apply_univ _]
      · conv in _ ≠ _ => rw [ne_comm]
        exact Eventually.ne_of_lt pos
      · apply measurableSet_support _
        apply (stronglyMeasurable_condexp).measurable.neg.le _
        exact (le_trans invariantSets_le nullMeasurableSpace_le)
    · exact ae_le_of_ae_lt pos
    · exact integrable_condexp.restrict.neg
  exact this.not_le (int_in_divergentSet_nonneg μ hf hφ hφ')

lemma limsup_birkhoffAverage_nonpos_of_condexp_neg
    (h : ∀ᵐ x ∂μ, (μ[φ|invariantSets f]) x < 0) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop nonneg := by
  apply Eventually.mono _ λ _ ↦ birkhoffAverage_tendsto_nonpos_of_not_mem_divergentSet
  apply ae_iff.mpr; simp
  exact divergentSet_zero_meas_of_condexp_neg μ hf hφ hφ' h

def invCondexp (μ : Measure α := by volume_tac) [IsProbabilityMeasure μ]
    (f : α → α) (φ : α → ℝ) : α → ℝ := μ[φ|invariantSets f]

theorem birkhoffErgodicTheorem_aux (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x - (invCondexp μ f φ x + ε)) atTop nonneg := by
  let ψ := φ - (invCondexp μ f φ + λ _ ↦ ε)
  have ψ_integrable : Integrable ψ μ := hφ.sub (integrable_condexp.add (integrable_const _))
  have ψ_measurable : Measurable ψ
  · suffices Measurable (invCondexp μ f φ) by measurability
    exact stronglyMeasurable_condexp.measurable.le (invariantSets_le)

  let condexpψ := invCondexp μ f ψ
  have condexpψ_const : condexpψ =ᵐ[μ] - λ _ ↦ ε := calc
    μ[ψ|invariantSets f]
    _ =ᵐ[μ] _ - _ := condexp_sub hφ (integrable_condexp.add (integrable_const _))
    _ =ᵐ[μ] _ - (_ + _) := (condexp_add integrable_condexp (integrable_const _)).neg.add_left
    _ =ᵐ[μ] _ - (_ + _) := (condexp_condexp_of_le (le_of_eq rfl)
                              invariantSets_le).add_right.neg.add_left
    _ = - μ[λ _ ↦ ε|invariantSets f] := by simp
    _ = - λ _ ↦ ε := by rw [condexp_const invariantSets_le]

  have limsup_nonpos : ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f ψ · x) atTop nonneg
  · suffices ∀ᵐ x ∂μ, condexpψ x < 0 from
      limsup_birkhoffAverage_nonpos_of_condexp_neg μ hf ψ_integrable ψ_measurable this
    exact condexpψ_const.mono λ x hx ↦ by simp [hx, hε]

  refine limsup_nonpos.mono λ x hx => ?_

  suffices ∀ (n : ℕ), 0 < n → birkhoffAverage ℝ f ψ n x = birkhoffAverage ℝ f φ n x - (invCondexp μ f φ x + ε) by
    simp at hx ⊢
    intro r hr
    cases' hx r hr with n hn
    use n + 1
    intro k hk
    rw [← this k (Nat.zero_lt_of_lt hk)]
    exact hn k (Nat.le_of_succ_le hk)

  have condexpφ_invariant : invCondexp μ f φ ∘ f = invCondexp μ f φ :=
    InvariantSets.invariant_of_measurable _ _ stronglyMeasurable_condexp.measurable

  intro n hn
  simp [ψ, birkhoffAverage_sub, birkhoffAverage_add, birkhoffAverage_eq_of_invariant
    (show _ = λ _ ↦ ε from rfl) hn, birkhoffAverage_eq_of_invariant condexpφ_invariant hn]

theorem birkhoffErgodicTheorem :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f φ · x) atTop (𝓝 (invCondexp μ f φ x)) := by
  have : ∀ᵐ x ∂μ, ∀ (k : {k : ℕ // k > 0}),
    ∀ᶠ n in atTop,
      |birkhoffAverage ℝ f φ n x - (invCondexp μ f φ x)| < (k : ℝ)⁻¹
  · apply ae_all_iff.mpr
    rintro ⟨k, hk⟩
    let δ := (k : ℝ)⁻¹/2
    have hδ : δ > 0 := by simpa [δ]
    have p₁ := birkhoffErgodicTheorem_aux μ hf hφ hφ' δ hδ
    have p₂ := birkhoffErgodicTheorem_aux μ hf hφ.neg hφ'.neg δ hδ
    have : invCondexp μ f (-φ) =ᵐ[μ] -invCondexp μ f φ := condexp_neg _
    refine ((p₁.and p₂).and this).mono λ x ⟨⟨hx₁, hx₂⟩, hx₃⟩ => ?_
    simp at hx₁ hx₂ ⊢
    cases' hx₁ δ hδ with n₁ hn₁
    cases' hx₂ δ hδ with n₂ hn₂
    simp_rw [δ] at hn₁ hn₂ ⊢
    use (max n₁ n₂)
    intro m hm
    apply abs_lt.mpr
    constructor
    · specialize hn₂ m (le_of_max_le_right hm)
      rw [hx₃, birkhoffAverage_neg] at hn₂
      norm_num at hn₂
      linarith
    · specialize hn₁ m (le_of_max_le_left hm)
      linarith

  refine this.mono λ x hx => Metric.tendsto_atTop.mpr λ ε hε => ?_
  cases' Archimedean.arch 1 hε with k hk
  have hk' : 1 < (k + 1) • ε
  · exact hk.trans_lt $ smul_lt_smul_of_pos_right (lt_add_one k) hε
  simp only [eventually_atTop, ge_iff_le, Subtype.forall, gt_iff_lt] at hx
  cases' hx k.succ (Nat.zero_lt_succ k) with N hN
  use N
  intro n hn
  apply (hN n hn).trans
  rw [inv_pos_lt_iff_one_lt_mul (Nat.cast_pos.mpr k.succ_pos)]
  norm_num at hk' ⊢
  linarith

#print axioms birkhoffErgodicTheorem
