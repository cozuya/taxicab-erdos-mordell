module
public import Taxicab.Basic
public import Taxicab.Algebra

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Taxicab

/-- Inclusive betweenness; in particular coordinate ties are included. -/
def Between (a m b : ℝ) : Prop := (a ≤ m ∧ m ≤ b) ∨ (b ≤ m ∧ m ≤ a)
def Middle (m a b c : ℝ) : Prop :=
  (m=a ∧ Between b m c) ∨ (m=b ∧ Between a m c) ∨ (m=c ∧ Between a m b)

lemma exists_middle (a b c : ℝ) : ∃ m, Middle m a b c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ⟨b, Or.inr (Or.inl ⟨rfl, Or.inl ⟨hab,hbc⟩⟩)⟩
    · rcases le_total a c with hac | hca
      · exact ⟨c, Or.inr (Or.inr ⟨rfl, Or.inl ⟨hac,hcb⟩⟩)⟩
      · exact ⟨a, Or.inl ⟨rfl, Or.inr ⟨hca,hab⟩⟩⟩
  · rcases le_total a c with hac | hca
    · exact ⟨a, Or.inl ⟨rfl, Or.inl ⟨hba,hac⟩⟩⟩
    · rcases le_total b c with hbc | hcb
      · exact ⟨c, Or.inr (Or.inr ⟨rfl, Or.inr ⟨hbc,hca⟩⟩)⟩
      · exact ⟨b, Or.inr (Or.inl ⟨rfl, Or.inr ⟨hcb,hba⟩⟩)⟩

lemma between_symm {a m b : ℝ} (h : Between a m b) : Between b m a := h.elim Or.inr Or.inl
lemma between_sub {a m b : ℝ} (h : Between a m b) : Between (a-m) 0 (b-m) := by
  rcases h with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · exact Or.inl ⟨by linarith,by linarith⟩
  · exact Or.inr ⟨by linarith,by linarith⟩

lemma between_abs {a c : ℝ} (hh : Between a 0 c) :
    |c-a|=|a|+|c| ∧ |c| * a+|a| * c=0 := by
  rcases hh with ⟨ha,hc⟩ | ⟨hc,ha⟩
  · rw [abs_of_nonpos ha,abs_of_nonneg hc,abs_of_nonneg (by linarith : 0 ≤ c-a)]
    constructor <;> ring
  · rw [abs_of_nonneg ha,abs_of_nonpos hc,abs_of_nonpos (by linarith : c-a ≤ 0)]
    constructor <;> ring

lemma prod_div_max (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a*b/max a b=min a b := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab,min_eq_left hab,mul_div_cancel_right₀ _ (ne_of_gt hb)]
  · rw [max_eq_left hba,min_eq_right hba,mul_div_cancel_left₀ _ (ne_of_gt ha)]

lemma axes_median (a b c d' : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : Between a 0 c) (hy : Between b 0 d') :
    InTri (0,0) (a,0) (0,b) (c,d') ∧
    3*T (0,0) (a,0) (0,b) (c,d') ≤ 2*S (0,0) (a,0) (0,b) (c,d') := by
  obtain ⟨hxc,hx0⟩ := between_abs hx
  obtain ⟨hyd,hy0⟩ := between_abs hy
  have hap : 0 < |a| := abs_pos.mpr ha
  have hbp : 0 < |b| := abs_pos.mpr hb
  let D := |a| * |b|+|a| * |d'|+|b| * |c|
  have hD : 0 < D := by dsimp [D]; positivity
  have hD0 : D ≠ 0 := ne_of_gt hD
  constructor
  · refine ⟨|b| * |c| / D, |a| * |d'| / D, |a| * |b| / D,
      by positivity,by positivity,by positivity,?_,?_⟩
    · dsimp [D]
      field_simp
      ring
    · apply Prod.ext <;> dsimp [bary]
      · calc
          0 = (|b| * (|c| * a+|a| * c))/D := by rw [hx0]; simp
          _ = _ := by ring
      · calc
          0 = (|a| * (|d'| * b+|b| * d'))/D := by rw [hy0]; simp
          _ = _ := by ring
  · have he := median_algebra |a| |b| |c| |d'| hap hbp (abs_nonneg _) (abs_nonneg _)
    have hxc' : |a-c|=|a|+|c| := by rw [abs_sub_comm]; exact hxc
    have heT : T (0,0) (a,0) (0,b) (c,d') =
        min |a| |b| + |b| * |c| / max |c| (|b|+|d'|) +
        |a| * |d'| / max (|a|+|c|) |d'| := by
      have he₁ : det (0,b) (c,d') (0,0) = -(b*c) := by dsimp [det]; ring
      have he₂ : det (c,d') (a,0) (0,0) = -(a*d') := by dsimp [det]; ring
      have he₃ : det (a,0) (0,b) (0,0) = a*b := by dsimp [det]; ring
      simp only [T,h,he₁,he₂,he₃,sideDen,
        sub_zero,zero_sub,abs_neg,abs_mul]
      rw [hyd,hxc',prod_div_max |a| |b| hap hbp]
      ring
    have heS : S (0,0) (a,0) (0,b) (c,d') = |a|+|b|+|c|+|d'| := by
      simp [S,d]; ring
    rw [heT,heS]
    exact he

/-- Translation, without any arbitrary rotation. -/
def shift (M Q : Point) : Point := (Q.1-M.1,Q.2-M.2)
lemma d_shift (M P U : Point) : d (shift M P) (shift M U)=d P U := by
  dsimp [d,shift]
  congr 2 <;> ring
lemma det_shift (M A B C : Point) : det (shift M A) (shift M B) (shift M C)=det A B C := by
  dsimp [det,shift]; ring
lemma sideDen_shift (M U V : Point) : sideDen (shift M U) (shift M V)=sideDen U V := by
  dsimp [sideDen,shift]
  congr 2 <;> ring
lemma S_shift (M P A B C : Point) :
    S (shift M P) (shift M A) (shift M B) (shift M C)=S P A B C := by
  simp only [S,d_shift]
lemma T_shift (M P A B C : Point) :
    T (shift M P) (shift M A) (shift M B) (shift M C)=T P A B C := by
  simp only [T,h,det_shift,sideDen_shift]

lemma inTri_unshift (M A B C : Point)
    (hh : InTri (0,0) (shift M A) (shift M B) (shift M C)) : InTri M A B C := by
  obtain ⟨α,β,γ,ha,hb,hc,hs,he⟩ := hh
  refine ⟨α,β,γ,ha,hb,hc,hs,?_⟩
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  apply Prod.ext <;> dsimp [bary,shift] at *
  · nlinarith [congrArg (fun x : ℝ => x*M.1) hs]
  · nlinarith [congrArg (fun x : ℝ => x*M.2) hs]

lemma inTri_cycle (P A B C : Point) : InTri P B C A → InTri P A B C := by
  rintro ⟨β,γ,α,hb,hc,ha,hs,hP⟩
  exact ⟨α,β,γ,ha,hb,hc,by linarith,by rwa [bary_cycle A B C α β γ] at hP⟩
lemma inTri_swap (P A B C : Point) : InTri P B A C → InTri P A B C := by
  rintro ⟨β,α,γ,hb,ha,hc,hs,hP⟩
  refine ⟨α,β,γ,ha,hb,hc,by linarith,?_⟩
  convert hP using 1
  apply Prod.ext <;> dsimp [bary] <;> ring

/-- The median check when the median coordinates come from different vertices. -/
lemma axis_median (M A B C : Point) (hn : det A B C ≠ 0)
    (hAy : A.2=M.2) (hBx : B.1=M.1)
    (hx : Between A.1 M.1 C.1) (hy : Between B.2 M.2 C.2) :
    InTri M A B C ∧ 3*T M A B C ≤ 2*S M A B C := by
  by_cases ha : A.1=M.1
  · have he : M=A := Prod.ext ha.symm hAy.symm
    subst M
    refine ⟨inTri_vertex A B C,?_⟩
    have hd : det C A A=0 := by dsimp [det]; ring
    have hh := boundary A B C A (by rwa [det_cycle]) (by simp [h,hd])
    simpa only [S_cycle A A B C,T_cycle A A B C] using hh
  by_cases hb : B.2=M.2
  · have he : M=B := Prod.ext hBx.symm hb.symm
    subst M
    refine ⟨inTri_cycle B A B C (inTri_vertex B C A),?_⟩
    apply boundary B A B C hn
    simp [h,det]
  have hh := axes_median (A.1-M.1) (B.2-M.2) (C.1-M.1) (C.2-M.2)
    (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb) (between_sub hx) (between_sub hy)
  have hA : shift M A=(A.1-M.1,0) := by simp [shift,hAy]
  have hB : shift M B=(0,B.2-M.2) := by simp [shift,hBx]
  have hM : shift M M=(0,0) := by simp [shift]
  constructor
  · apply inTri_unshift M A B C
    rw [hA,hB]
    exact hh.1
  · have hg := hh.2
    rw [←hA,←hB,show (C.1-M.1,C.2-M.2)=shift M C from rfl,←hM] at hg
    rwa [T_shift,S_shift] at hg


private def Good (M A B C : Point) : Prop :=
  InTri M A B C ∧ 3*T M A B C ≤ 2*S M A B C
private lemma good_cycle (M A B C : Point) (hh : Good M B C A) : Good M A B C := by
  exact ⟨inTri_cycle M A B C hh.1, by simpa only [T_cycle M A B C,S_cycle M A B C] using hh.2⟩
private lemma good_swap (M A B C : Point) (hh : Good M B A C) : Good M A B C := by
  exact ⟨inTri_swap M A B C hh.1, by simpa only [T_swap M A B C,S_swap M A B C] using hh.2⟩
private lemma good_vertex (A B C : Point) (hn : det A B C ≠ 0) : Good A A B C := by
  have hd : det C A A=0 := by dsimp [det]; ring
  have hh := boundary A B C A (by rwa [det_cycle A B C]) (by simp [h,hd])
  exact ⟨inTri_vertex A B C, by simpa only [T_cycle A A B C,S_cycle A A B C] using hh⟩

/-- All nine choices of median-coordinate vertices, including ties. -/
theorem median_good (M A B C : Point) (hn : det A B C ≠ 0)
    (hx : Middle M.1 A.1 B.1 C.1) (hy : Middle M.2 A.2 B.2 C.2) :
    InTri M A B C ∧ 3*T M A B C ≤ 2*S M A B C := by
  have hnB : det B C A ≠ 0 := by rwa [det_cycle A B C]
  have hnC : det C A B ≠ 0 := by rwa [det_cycle B C A]
  have hnBA : det B A C ≠ 0 := by rw [det_swap A B C]; exact neg_ne_zero.mpr hn
  have hnCB : det C B A ≠ 0 := by rw [det_swap B C A]; exact neg_ne_zero.mpr hnB
  have hnAC : det A C B ≠ 0 := by rw [det_swap C A B]; exact neg_ne_zero.mpr hnC
  rcases hx with ⟨hx,hxb⟩ | ⟨hx,hxb⟩ | ⟨hx,hxb⟩ <;>
    rcases hy with ⟨hy,hyb⟩ | ⟨hy,hyb⟩ | ⟨hy,hyb⟩
  · have he : M=A := Prod.ext hx hy
    subst M
    exact good_vertex A B C hn
  · exact good_swap M A B C (axis_median M B A C hnBA hy.symm hx.symm hxb hyb)
  · exact good_cycle M A B C (good_cycle M B C A
      (axis_median M C A B hnC hy.symm hx.symm (between_symm hxb) hyb))
  · exact axis_median M A B C hn hy.symm hx.symm hxb hyb
  · have he : M=B := Prod.ext hx hy
    subst M
    exact good_cycle B A B C (good_vertex B C A hnB)
  · exact good_cycle M A B C (good_swap M B C A
      (axis_median M C B A hnCB hy.symm hx.symm (between_symm hxb) (between_symm hyb)))
  · exact good_swap M A B C (good_cycle M B A C
      (axis_median M A C B hnAC hy.symm hx.symm hxb (between_symm hyb)))
  · exact good_cycle M A B C
      (axis_median M B C A hnB hy.symm hx.symm (between_symm hxb) (between_symm hyb))
  · have he : M=C := Prod.ext hx hy
    subst M
    exact good_cycle C A B C (good_cycle C B C A (good_vertex C A B hnC))

/-- Existence and triangle membership of the coordinatewise median. -/
theorem exists_good_median (A B C : Point) (hn : det A B C ≠ 0) :
    ∃ M : Point, Middle M.1 A.1 B.1 C.1 ∧ Middle M.2 A.2 B.2 C.2 ∧
      InTri M A B C ∧ 3*T M A B C ≤ 2*S M A B C := by
  obtain ⟨x,hx⟩ := exists_middle A.1 B.1 C.1
  obtain ⟨y,hy⟩ := exists_middle A.2 B.2 C.2
  exact ⟨(x,y),hx,hy,median_good (x,y) A B C hn hx hy⟩

lemma sorted_scalar_sum (a b c q : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (haq : a ≤ q) (hqc : q ≤ c) :
    |q-a|+|q-b|+|q-c| = |b-a|+|b-b|+|b-c|+|q-b| := by
  rw [abs_of_nonneg (sub_nonneg.mpr haq),abs_of_nonpos (sub_nonpos.mpr hqc),
    abs_of_nonneg (sub_nonneg.mpr hab),abs_of_nonpos (sub_nonpos.mpr hbc)]
  simp only [sub_self,abs_zero]
  ring

/-- One-dimensional sum identity, for any ordering and ties. -/
lemma scalar_sum_identity (a b c m q : ℝ) (hm : Middle m a b c)
    (hq0 : min a (min b c) ≤ q) (hq1 : q ≤ max a (max b c)) :
    |q-a|+|q-b|+|q-c| = |m-a|+|m-b|+|m-c|+|q-m| := by
  rcases hm with ⟨hm,hh⟩ | ⟨hm,hh⟩ | ⟨hm,hh⟩ <;> subst m
  · rcases hh with ⟨hba,hac⟩ | ⟨hca,hab⟩
    · have hbq : b ≤ q := (le_min hba (le_min le_rfl (hba.trans hac))).trans hq0
      have hqc : q ≤ c := hq1.trans (max_le hac (max_le (hba.trans hac) le_rfl))
      have hh := sorted_scalar_sum b a c q hba hac hbq hqc
      linarith
    · have hcq : c ≤ q := (le_min hca (le_min (hca.trans hab) le_rfl)).trans hq0
      have hqb : q ≤ b := hq1.trans (max_le hab (max_le le_rfl (hca.trans hab)))
      have hh := sorted_scalar_sum c a b q hca hab hcq hqb
      linarith
  · rcases hh with ⟨hab,hbc⟩ | ⟨hcb,hba⟩
    · have haq : a ≤ q := (le_min le_rfl (le_min hab (hab.trans hbc))).trans hq0
      have hqc : q ≤ c := hq1.trans (max_le (hab.trans hbc) (max_le hbc le_rfl))
      exact sorted_scalar_sum a b c q hab hbc haq hqc
    · have hcq : c ≤ q := (le_min (hcb.trans hba) (le_min hcb le_rfl)).trans hq0
      have hqa : q ≤ a := hq1.trans (max_le le_rfl (max_le hba (hcb.trans hba)))
      have hh := sorted_scalar_sum c b a q hcb hba hcq hqa
      linarith
  · rcases hh with ⟨hac,hcb⟩ | ⟨hbc,hca⟩
    · have haq : a ≤ q := (le_min le_rfl (le_min (hac.trans hcb) hac)).trans hq0
      have hqb : q ≤ b := hq1.trans (max_le (hac.trans hcb) (max_le le_rfl hcb))
      have hh := sorted_scalar_sum a c b q hac hcb haq hqb
      linarith
    · have hbq : b ≤ q := (le_min (hbc.trans hca) (le_min le_rfl hbc)).trans hq0
      have hqa : q ≤ a := hq1.trans (max_le le_rfl (max_le (hbc.trans hca) hca))
      have hh := sorted_scalar_sum b c a q hbc hca hbq hqa
      linarith

lemma bary_scalar_bounds (a b c α β γ : ℝ) (ha : 0 ≤ α) (hb : 0 ≤ β)
    (hc : 0 ≤ γ) (hs : α+β+γ=1) :
    min a (min b c) ≤ α*a+β*b+γ*c ∧ α*a+β*b+γ*c ≤ max a (max b c) := by
  have hla := min_le_left a (min b c)
  have hlb := (min_le_right a (min b c)).trans (min_le_left b c)
  have hlc := (min_le_right a (min b c)).trans (min_le_right b c)
  have hua := le_max_left a (max b c)
  have hub := (le_max_left b c).trans (le_max_right a (max b c))
  have huc := (le_max_right b c).trans (le_max_right a (max b c))
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hla ha,mul_le_mul_of_nonneg_left hlb hb,
      mul_le_mul_of_nonneg_left hlc hc,congrArg (fun x : ℝ => x*min a (min b c)) hs]
  · nlinarith [mul_le_mul_of_nonneg_left hua ha,mul_le_mul_of_nonneg_left hub hb,
      mul_le_mul_of_nonneg_left huc hc,congrArg (fun x : ℝ => x*max a (max b c)) hs]

/-- The distance-sum identity used for radial interpolation. -/
theorem sum_identity (M Q A B C : Point)
    (hx : Middle M.1 A.1 B.1 C.1) (hy : Middle M.2 A.2 B.2 C.2)
    (hQ : InTri Q A B C) : S Q A B C = S M A B C+d Q M := by
  obtain ⟨α,β,γ,ha,hb,hc,hs,rfl⟩ := hQ
  obtain ⟨hxl,hxu⟩ := bary_scalar_bounds A.1 B.1 C.1 α β γ ha hb hc hs
  obtain ⟨hyl,hyu⟩ := bary_scalar_bounds A.2 B.2 C.2 α β γ ha hb hc hs
  have he₁ := scalar_sum_identity A.1 B.1 C.1 M.1 (α*A.1+β*B.1+γ*C.1) hx hxl hxu
  have he₂ := scalar_sum_identity A.2 B.2 C.2 M.2 (α*A.2+β*B.2+γ*C.2) hy hyl hyu
  dsimp [S,d,bary]
  linarith

lemma d_mix (M Q : Point) (t : ℝ) (ht : t ≤ 1) :
    d (mix t M Q) M=(1-t)*d Q M := by
  have h₁ : t*M.1+(1-t)*Q.1-M.1=(1-t)*(Q.1-M.1) := by ring
  have h₂ : t*M.2+(1-t)*Q.2-M.2=(1-t)*(Q.2-M.2) := by ring
  dsimp [d,mix]
  rw [h₁,h₂,abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht)]
  ring

end Taxicab
