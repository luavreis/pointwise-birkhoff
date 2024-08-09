import Mathlib.MeasureTheory.MeasurableSpace.Invariants

open scoped MeasureTheory

namespace MeasurableSpace

theorem invariant_of_measurable_invariants
    {f : α → α} {g : α → β} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (h : Measurable[invariants f] g) : g ∘ f = g := by
  funext x
  suffices x ∈ f⁻¹' (g⁻¹' {g x}) by simpa
  rw [(h <| measurableSet_singleton (g x)).2]
  rfl

end MeasurableSpace
