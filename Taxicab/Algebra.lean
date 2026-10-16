module
public import Taxicab.Imports

@[expose] public section

set_option autoImplicit false

namespace Taxicab

/-- An affine function on an interval is bounded by its endpoint values. -/
lemma affine_bound (l r u A B K : ℝ) (hl : l ≤ u) (hr : u ≤ r)
    (h₁ : A*l+B ≤ K) (h₂ : A*r+B ≤ K) : A*u+B ≤ K := by
  by_cases hA : 0 ≤ A
  · nlinarith [mul_nonneg hA (sub_nonneg.mpr hr)]
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA) (sub_nonneg.mpr hl)]

/-- The three endpoint/breakpoint checks for the piecewise affine function. -/
lemma min_affine_bound (a s b L N K : ℝ) (_ha : 0 < a) (_hs : 0 < s)
    (hb : 0 ≤ b) (hbs : b ≤ s)
    (h0 : N ≤ K) (hs' : min a s + L*s+N ≤ K)
    (ha' : a ≤ s → a+L*a+N ≤ K) : min a b+L*b+N ≤ K := by
  by_cases hba : b ≤ a
  · rw [min_eq_right hba]
    by_cases has : a ≤ s
    · have h := affine_bound 0 a b (1+L) N K hb hba (by simpa using h0)
        (by nlinarith [ha' has])
      nlinarith
    · have hsa : s ≤ a := le_of_not_ge has
      rw [min_eq_right hsa] at hs'
      have h := affine_bound 0 s b (1+L) N K hb hbs (by simpa using h0)
        (by nlinarith [hs'])
      nlinarith
  · have hab : a ≤ b := le_of_not_ge hba
    have has : a ≤ s := hab.trans hbs
    rw [min_eq_left hab]
    rw [min_eq_left has] at hs'
    have h := affine_bound a s b L (a+N) K hab hbs (by nlinarith [ha' has])
      (by nlinarith [hs'])
    nlinarith

/-- The exact polynomial certificate at the breakpoint a=b. -/
lemma equal_intercepts (t c d : ℝ) (ht : 0 < t) (hd : 0 ≤ d) (hcd : d ≤ c) :
    3*(t + t*c / max c (t+d) + t*d/(t+c)) ≤ 2*(2*t+c+d) := by
  have hc : 0 ≤ c := hd.trans hcd
  have htc : 0 < t+c := by positivity
  have htd : 0 < t+d := by positivity
  by_cases hh : t+d ≤ c
  · rw [max_eq_left hh]
    have hc0 : c ≠ 0 := ne_of_gt (htd.trans_le hh)
    rw [mul_div_cancel_right₀ t hc0]
    have hh' : t*d/(t+c) ≤ d := (div_le_iff₀ htc).2 (by nlinarith [mul_nonneg hc hd])
    nlinarith
  · have hh' : c ≤ t+d := le_of_not_ge hh
    rw [max_eq_right hh']
    have cert :
        (t+c)*(t+d)*(2*(2*t+c+d) - 3*(t+t*c/(t+d)+t*d/(t+c))) =
        t*(t-c+d)*(t+c-d)+(3*t+2*c+2*d)*c*d := by
      field_simp
      ring
    have hnon : 0 ≤ t*(t-c+d)*(t+c-d)+(3*t+2*c+2*d)*c*d := by
      have h₁ : 0 ≤ t-c+d := by linarith
      have h₂ : 0 ≤ t+c-d := by linarith
      positivity
    have hprod : 0 < (t+c)*(t+d) := mul_pos htc htd
    have : 0 ≤ 2*(2*t+c+d) - 3*(t+t*c/(t+d)+t*d/(t+c)) :=
      (mul_nonneg_iff_of_pos_left hprod).mp (by rw [cert]; exact hnon)
    linarith

lemma median_algebra_ordered (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hws : b+d ≤ a+c) :
    3*(min a b + b*c/max c (b+d) + a*d/max (a+c) d) ≤ 2*(a+b+c+d) := by
  let w := a+c
  let s := b+d
  have hw : 0 < w := by dsimp [w]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hwne := ne_of_gt hw
  have hmax : 0 < max c s := lt_of_lt_of_le hs (le_max_right c s)
  have hds : d ≤ w := by dsimp [w]; linarith
  rw [max_eq_left hds]
  let L := c/max c s-a/w
  let N := a*s/w
  let K := 2*(w+s)/3
  have h0 : N ≤ K := by
    have hN : N ≤ s := by
      dsimp [N]
      apply (div_le_iff₀ hw).2
      dsimp [w]
      nlinarith [mul_nonneg hc (le_of_lt hs)]
    dsimp [K, w, s] at *
    linarith
  have hend : min a s + L*s+N ≤ K := by
    have heq : min a s + L*s+N = min a s+min c s := by
      dsimp [L,N]
      have hh : s*c/max c s = min c s := by
        rcases le_total c s with hh | hh
        · rw [max_eq_right hh, min_eq_left hh]
          field_simp
        · rw [max_eq_left hh, min_eq_right hh]
          have hcne : c ≠ 0 := ne_of_gt (hs.trans_le hh)
          field_simp
      calc
        _ = min a s + s*c/max c s := by ring
        _ = _ := by rw [hh]
    rw [heq]
    have hwbound : min a s+min c s ≤ w := by
      dsimp [w]; linarith [min_le_left a s, min_le_left c s]
    have hsbound : min a s+min c s ≤ 2*s := by
      linarith [min_le_right a s, min_le_right c s]
    dsimp [K]
    linarith
  have hmid : a ≤ s → a+L*a+N ≤ K := by
    intro has
    have hcd : s-a ≤ c := by dsimp [s] at *; linarith
    have he := equal_intercepts a c (s-a) ha (sub_nonneg.mpr has) hcd
    have heq : a+L*a+N = a+a*c/max c (a+(s-a))+a*(s-a)/(a+c) := by
      dsimp [L,N,w]
      rw [show a+(s-a)=s by ring]
      ring
    rw [heq]
    dsimp [K,w]
    linarith
  have hf := min_affine_bound a s b L N K ha hs (le_of_lt hb)
    (by dsimp [s]; linarith) h0 hend hmid
  have heq : min a b+L*b+N = min a b+b*c/max c (b+d)+a*d/(a+c) := by
    dsimp [L,N,w,s]
    ring
  rw [heq] at hf
  dsimp [K,w,s] at hf
  linarith

/-- The normal-form median inequality, with all four orientation parameters. -/
theorem median_algebra (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    3*(min a b + b*c/max c (b+d) + a*d/max (a+c) d) ≤ 2*(a+b+c+d) := by
  rcases le_total (b+d) (a+c) with hw | hw
  · exact median_algebra_ordered a b c d ha hb hc hd hw
  · have h := median_algebra_ordered b a d c hb ha hd hc hw
    rw [min_comm b a, max_comm d (a+c), max_comm (b+d) c] at h
    linarith

end Taxicab
