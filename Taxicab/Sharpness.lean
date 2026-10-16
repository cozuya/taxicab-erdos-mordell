module
public import Taxicab.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Taxicab

/-- Exact evaluations on the sharpness family. -/
theorem sharpness_distances (ε : ℝ) (he0 : 0 < ε) (he1 : ε < 1) :
    S (0,ε) (-1,0) (1,0) (0,1) = 3+ε ∧
    T (0,ε) (-1,0) (1,0) (0,1) = 2-ε := by
  have he : 0 ≤ ε := le_of_lt he0
  have he' : ε-1 ≤ 0 := by linarith
  have he'' : 0 ≤ 1-ε := by linarith
  constructor
  · norm_num [S,d,abs_of_nonneg he,abs_of_nonpos he']
    ring
  · norm_num [T,h,det,sideDen,abs_mul,abs_of_nonneg he,
      abs_of_nonpos he',abs_of_nonneg he'']
    rw [show -ε+1=1-ε by ring,abs_of_nonneg he'']
    ring

/-- Every constant larger than 3/2 fails on a genuinely strict barycentric example. -/
theorem sharpness (k : ℝ) (hk : (3:ℝ)/2 < k) :
    ∃ (A B C P : Point) (α β γ : ℝ),
      det A B C ≠ 0 ∧ 0 < α ∧ 0 < β ∧ 0 < γ ∧ α+β+γ=1 ∧
      P=bary A B C α β γ ∧
      0 < sideDen B C ∧ 0 < sideDen C A ∧ 0 < sideDen A B ∧
      S P A B C < k*T P A B C := by
  let ε := (2*k-3)/(2*(k+1))
  have hden : 0 < 2*(k+1) := by linarith
  have he0 : 0 < ε := div_pos (by linarith) hden
  have he1 : ε < 1 := (div_lt_one hden).2 (by linarith)
  have heq : ε*(2*(k+1))=2*k-3 := div_mul_cancel₀ _ (ne_of_gt hden)
  obtain ⟨hS,hT⟩ := sharpness_distances ε he0 he1
  refine ⟨(-1,0),(1,0),(0,1),(0,ε),(1-ε)/2,(1-ε)/2,ε,?_,
    by linarith,by linarith,he0,by ring,?_,?_,?_,?_,?_⟩
  · norm_num [det]
  · apply Prod.ext <;> dsimp [bary] <;> ring
  · norm_num [sideDen]
  · norm_num [sideDen]
  · norm_num [sideDen]
  · rw [hS,hT]
    nlinarith

end Taxicab
