module
public import Taxicab.Imports

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Taxicab

abbrev Point := ℝ × ℝ

def d (U V : Point) : ℝ := |U.1-V.1|+|U.2-V.2|
def det (A B C : Point) : ℝ :=
  (B.1-A.1)*(C.2-A.2)-(B.2-A.2)*(C.1-A.1)
def sideDen (U V : Point) : ℝ := max |V.1-U.1| |V.2-U.2|
def h (P U V : Point) : ℝ := |det U V P| / sideDen U V

def S (P A B C : Point) : ℝ := d P A+d P B+d P C
def T (P A B C : Point) : ℝ := h P B C+h P C A+h P A B

def bary (A B C : Point) (α β γ : ℝ) : Point :=
  (α*A.1+β*B.1+γ*C.1, α*A.2+β*B.2+γ*C.2)

def InTri (P A B C : Point) : Prop :=
  ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α+β+γ=1 ∧ P=bary A B C α β γ

def mix (t : ℝ) (U V : Point) : Point :=
  (t*U.1+(1-t)*V.1, t*U.2+(1-t)*V.2)

lemma det_cycle (A B C : Point) : det B C A = det A B C := by
  dsimp [det]; ring
lemma det_swap (A B C : Point) : det B A C = -det A B C := by
  dsimp [det]; ring
lemma sideDen_symm (U V : Point) : sideDen V U = sideDen U V := by
  simp only [sideDen, abs_sub_comm]
lemma h_symm (P U V : Point) : h P V U = h P U V := by
  simp only [h]
  rw [det_swap U V P, abs_neg, sideDen_symm U V]
lemma d_symm (U V : Point) : d V U = d U V := by
  simp only [d, abs_sub_comm]

lemma sideDen_pos (U V : Point) (hUV : U ≠ V) : 0 < sideDen U V := by
  by_cases hx : V.1=U.1
  · have hy : V.2 ≠ U.2 := by
      intro hy
      exact hUV (Prod.ext hx.symm hy.symm)
    exact lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hy)) (le_max_right _ _)
  · exact lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hx)) (le_max_left _ _)

lemma sides_distinct (A B C : Point) (hn : det A B C ≠ 0) :
    B ≠ C ∧ C ≠ A ∧ A ≠ B := by
  refine ⟨?_, ?_, ?_⟩ <;> intro he <;> apply hn
  · subst C; dsimp [det]; ring
  · subst C; simp [det]
  · subst B; simp [det]

theorem side_denominators_positive (A B C : Point) (hn : det A B C ≠ 0) :
    0 < sideDen B C ∧ 0 < sideDen C A ∧ 0 < sideDen A B := by
  obtain ⟨hBC,hCA,hAB⟩ := sides_distinct A B C hn
  exact ⟨sideDen_pos B C hBC,sideDen_pos C A hCA,sideDen_pos A B hAB⟩

lemma h_le_endpoint (P U V : Point) (hUV : U ≠ V) : h P U V ≤ d P U := by
  apply (div_le_iff₀ (sideDen_pos U V hUV)).2
  have h₁ := le_max_left |V.1-U.1| |V.2-U.2|
  have h₂ := le_max_right |V.1-U.1| |V.2-U.2|
  have hc := abs_sub_le ((V.1-U.1)*(P.2-U.2)) 0 ((V.2-U.2)*(P.1-U.1))
  simp only [sub_zero, zero_sub, abs_neg, abs_mul] at hc
  have h₃ := mul_le_mul_of_nonneg_right h₁ (abs_nonneg (P.2-U.2))
  have h₄ := mul_le_mul_of_nonneg_right h₂ (abs_nonneg (P.1-U.1))
  dsimp [det,d,sideDen] at *
  nlinarith

lemma boundary (P A B C : Point) (hn : det A B C ≠ 0) (hzero : h P B C=0) :
    3*T P A B C ≤ 2*S P A B C := by
  obtain ⟨hBC,hCA,hAB⟩ := sides_distinct A B C hn
  have h₁ := h_le_endpoint P A C hCA.symm
  have h₂ := h_le_endpoint P A B hAB
  have h₃ := h_le_endpoint P C A hCA
  have h₄ := h_le_endpoint P B A hAB.symm
  rw [h_symm] at h₁ h₄
  dsimp [S,T]
  rw [hzero]
  linarith

lemma S_cycle (P A B C : Point) : S P B C A = S P A B C := by dsimp [S]; ring
lemma T_cycle (P A B C : Point) : T P B C A = T P A B C := by dsimp [T]; ring
lemma S_swap (P A B C : Point) : S P B A C = S P A B C := by dsimp [S]; ring
lemma T_swap (P A B C : Point) : T P B A C = T P A B C := by
  simp only [T,h_symm P A C,h_symm P C B,h_symm P B A]
  ring

lemma det_bary (A B C : Point) (α β γ : ℝ) (hs : α+β+γ=1) :
    det B C (bary A B C α β γ) = α*det A B C := by
  have hg : γ=1-α-β := by linarith
  rw [hg]; dsimp [det,bary]; ring

lemma bary_cycle (A B C : Point) (α β γ : ℝ) :
    bary B C A β γ α = bary A B C α β γ := by
  apply Prod.ext <;> dsimp [bary] <;> ring

lemma T_bary (A B C : Point) (α β γ : ℝ) (ha : 0 ≤ α) (hb : 0 ≤ β)
    (hc : 0 ≤ γ) (hs : α+β+γ=1) :
    T (bary A B C α β γ) A B C =
    α*(|det A B C|/sideDen B C)+β*(|det A B C|/sideDen C A)+
    γ*(|det A B C|/sideDen A B) := by
  have h₁ := det_bary A B C α β γ hs
  have h₂ := det_bary B C A β γ α (by linarith)
  have h₃ := det_bary C A B γ α β (by linarith)
  rw [bary_cycle A B C α β γ, det_cycle A B C] at h₂
  rw [bary_cycle B C A β γ α, bary_cycle A B C α β γ] at h₃
  rw [det_cycle B C A, det_cycle A B C] at h₃
  simp only [T,h,h₁,h₂,h₃,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb,abs_of_nonneg hc]
  ring

lemma inTri_vertex (A B C : Point) : InTri A A B C := by
  refine ⟨1,0,0,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  simp [bary]

lemma boundary_bary (A B C : Point) (hn : det A B C ≠ 0)
    (α β γ : ℝ) (hs : α+β+γ=1) (hz : α=0 ∨ β=0 ∨ γ=0) :
    3*T (bary A B C α β γ) A B C ≤ 2*S (bary A B C α β γ) A B C := by
  rcases hz with hz | hz | hz
  · apply boundary _ _ _ _ hn
    rw [h,det_bary A B C α β γ hs,hz]; simp
  · have hh := boundary (bary B C A β γ α) B C A (by rwa [det_cycle])
    have hz' : h (bary B C A β γ α) C A=0 := by
      rw [h,det_bary B C A β γ α (by linarith),hz]; simp
    simpa only [bary_cycle A B C α β γ,T_cycle _ A B C,S_cycle _ A B C] using hh hz'
  · have hh := boundary (bary C A B γ α β) C A B
      (by rwa [det_cycle B C A,det_cycle A B C])
    have hz' : h (bary C A B γ α β) A B=0 := by
      rw [h,det_bary C A B γ α β (by linarith),hz]; simp
    simpa only [bary_cycle B C A β γ α,bary_cycle A B C α β γ,
      T_cycle _ B C A,T_cycle _ A B C,S_cycle _ B C A,S_cycle _ A B C] using hh hz'

end Taxicab
