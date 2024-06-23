import Mathlib.Tactic

/- can't find those -/

/-- If two functions `f₁` and `f₂` are eventually equal with respect to a filter `f`,
then adding to right the same function `f₃` to both `f₁` and `f₂` results in two functions that
are also eventually equal with respect to the same filter `f`.-/
lemma Filter.EventuallyEq.add_right {f : Filter α} {f₁ f₂ f₃ : α → ℝ} (h : f₁ =ᶠ[f] f₂) :
    f₁ + f₃ =ᶠ[f] f₂ + f₃ := h.mono λ x hx ↦ by simp [hx]

/-- If two functions `f₁` and `f₂` are eventually equal with respect to a filter `f`,
then adding to left the same function `f₃` to both `f₁` and `f₂` results in two functions that
are also eventually equal with respect to the same filter `f`.-/
lemma Filter.EventuallyEq.add_left {f : Filter α} {f₁ f₂ f₃ : α → ℝ} (h : f₁ =ᶠ[f] f₂) :
    f₃ + f₁ =ᶠ[f] f₃ + f₂ := h.mono λ x hx ↦ by simp [hx]
