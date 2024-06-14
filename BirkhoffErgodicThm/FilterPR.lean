import Mathlib.Tactic

/- can't find those -/
lemma Filter.EventuallyEq.add_right {f : Filter α} {f₁ f₂ f₃ : α → ℝ} (h : f₁ =ᶠ[f] f₂) :
    f₁ + f₃ =ᶠ[f] f₂ + f₃ := h.mono λ x hx ↦ by simp [hx]

lemma Filter.EventuallyEq.add_left {f : Filter α} {f₁ f₂ f₃ : α → ℝ} (h : f₁ =ᶠ[f] f₂) :
    f₃ + f₁ =ᶠ[f] f₃ + f₂ := h.mono λ x hx ↦ by simp [hx]
