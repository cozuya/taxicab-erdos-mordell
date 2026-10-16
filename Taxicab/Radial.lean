module
public import Taxicab.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Taxicab

/-- Algebraic form of extending a ray from a closed-triangle point to an edge. -/
def RadialWeights (α β γ μ ν ρ : ℝ) : Prop :=
  (α=μ ∧ β=ν ∧ γ=ρ) ∨
  ∃ t x y z : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
    x+y+z=1 ∧ (x=0 ∨ y=0 ∨ z=0) ∧
    α=t*μ+(1-t)*x ∧ β=t*ν+(1-t)*y ∧ γ=t*ρ+(1-t)*z

lemma radial_first (α β γ μ ν ρ : ℝ) (ha : 0 < α) (hb : 0 < β) (hc : 0 < γ)
    (_hμ : 0 ≤ μ) (_hν : 0 ≤ ν) (_hρ : 0 ≤ ρ)
    (hs : α+β+γ=1) (hm : μ+ν+ρ=1)
    (h₁ : ν*α ≤ μ*β) (h₂ : ρ*α ≤ μ*γ) : RadialWeights α β γ μ ν ρ := by
  have ham : α ≤ μ := by nlinarith [hs,hm]
  have hmp : 0 < μ := ha.trans_le ham
  by_cases he : α=μ
  · left
    have hbn : ν ≤ β := by nlinarith
    have hcr : ρ ≤ γ := by nlinarith
    exact ⟨he,by linarith,by linarith⟩
  · have hlt : α < μ := lt_of_le_of_ne ham he
    let t := α/μ
    have ht0 : 0 < t := div_pos ha hmp
    have ht1 : t < 1 := (div_lt_one hmp).2 hlt
    have htμ : t*μ=α := div_mul_cancel₀ α (ne_of_gt hmp)
    have hyt : 0 ≤ β-t*ν := by
      have : t*ν ≤ β := by
        dsimp [t]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hmp).2
        nlinarith
      linarith
    have hzt : 0 ≤ γ-t*ρ := by
      have : t*ρ ≤ γ := by
        dsimp [t]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hmp).2
        nlinarith
      linarith
    have hden : 0 < 1-t := by linarith
    have hden0 : 1-t ≠ 0 := ne_of_gt hden
    right
    refine ⟨t,0,(β-t*ν)/(1-t),(γ-t*ρ)/(1-t),le_of_lt ht0,le_of_lt ht1,
      le_rfl,div_nonneg hyt (le_of_lt hden),div_nonneg hzt (le_of_lt hden),?_,
      Or.inl rfl,?_,?_,?_⟩
    · field_simp
      nlinarith [congrArg (fun q : ℝ => t*q) hm]
    · simpa using htμ.symm
    · rw [mul_div_cancel₀ _ hden0]; ring
    · rw [mul_div_cancel₀ _ hden0]; ring

lemma radial_cycle (α β γ μ ν ρ : ℝ) :
    RadialWeights β γ α ν ρ μ → RadialWeights α β γ μ ν ρ := by
  rintro (⟨hb,hc,ha⟩ | ⟨t,x,y,z,ht0,ht1,hx,hy,hz,hs,hzero,hb,hc,ha⟩)
  · exact Or.inl ⟨ha,hb,hc⟩
  · right
    refine ⟨t,z,x,y,ht0,ht1,hz,hx,hy,by linarith,?_,ha,hb,hc⟩
    rcases hzero with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

theorem radial_weights (α β γ μ ν ρ : ℝ) (ha : 0 < α) (hb : 0 < β) (hc : 0 < γ)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hρ : 0 ≤ ρ)
    (hs : α+β+γ=1) (hm : μ+ν+ρ=1) : RadialWeights α β γ μ ν ρ := by
  rcases le_total (ν/β) (μ/α) with h₁ | h₁
  · rcases le_total (ρ/γ) (μ/α) with h₂ | h₂
    · exact radial_first α β γ μ ν ρ ha hb hc hμ hν hρ hs hm
        ((div_le_div_iff₀ hb ha).mp h₁) ((div_le_div_iff₀ hc ha).mp h₂)
    · apply radial_cycle α β γ μ ν ρ
      apply radial_cycle β γ α ν ρ μ
      exact radial_first γ α β ρ μ ν hc ha hb hρ hμ hν (by linarith) (by linarith)
        ((div_le_div_iff₀ ha hc).mp h₂) ((div_le_div_iff₀ hb hc).mp (h₁.trans h₂))
  · rcases le_total (ρ/γ) (ν/β) with h₂ | h₂
    · apply radial_cycle α β γ μ ν ρ
      exact radial_first β γ α ν ρ μ hb hc ha hν hρ hμ (by linarith) (by linarith)
        ((div_le_div_iff₀ hc hb).mp h₂) ((div_le_div_iff₀ ha hb).mp h₁)
    · apply radial_cycle α β γ μ ν ρ
      apply radial_cycle β γ α ν ρ μ
      exact radial_first γ α β ρ μ ν hc ha hb hρ hμ hν (by linarith) (by linarith)
        ((div_le_div_iff₀ ha hc).mp (h₁.trans h₂)) ((div_le_div_iff₀ hb hc).mp h₂)

end Taxicab
