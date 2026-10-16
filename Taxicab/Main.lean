module
public import Taxicab.Median
public import Taxicab.Radial

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Taxicab

/-- Radial interpolation from the proved coordinatewise median to a triangle edge. -/
theorem main_bound (A B C : Point) (α β γ : ℝ) (hn : det A B C ≠ 0)
    (ha : 0 < α) (hb : 0 < β) (hc : 0 < γ) (hs : α+β+γ=1) :
    3*T (bary A B C α β γ) A B C ≤ 2*S (bary A B C α β γ) A B C := by
  obtain ⟨M,hmx,hmy,hMtri,hMbound⟩ := exists_good_median A B C hn
  obtain ⟨μ,ν,ρ,hμ,hν,hρ,hm,hMeq⟩ := hMtri
  have hPtri : InTri (bary A B C α β γ) A B C :=
    ⟨α,β,γ,le_of_lt ha,le_of_lt hb,le_of_lt hc,hs,rfl⟩
  rcases radial_weights α β γ μ ν ρ ha hb hc hμ hν hρ hs hm with
    he | ⟨t,x,y,z,ht0,ht1,hx,hy,hz,hxyz,hzero,hα,hβ,hγ⟩
  · obtain ⟨hα,hβ,hγ⟩ := he
    simpa only [hMeq,←hα,←hβ,←hγ] using hMbound
  · let Q := bary A B C x y z
    have hQtri : InTri Q A B C := ⟨x,y,z,hx,hy,hz,hxyz,rfl⟩
    have hQbound : 3*T Q A B C ≤ 2*S Q A B C :=
      boundary_bary A B C hn x y z hxyz hzero
    have hmix : bary A B C α β γ=mix t M Q := by
      rw [hMeq]
      apply Prod.ext <;> dsimp [bary,mix,Q] <;> rw [hα,hβ,hγ] <;> ring
    have hSp : S (bary A B C α β γ) A B C =
        t*S M A B C+(1-t)*S Q A B C := by
      rw [sum_identity M _ A B C hmx hmy hPtri,
        sum_identity M Q A B C hmx hmy hQtri,hmix,d_mix M Q t ht1]
      ring
    have hTp : T (bary A B C α β γ) A B C =
        t*T M A B C+(1-t)*T Q A B C := by
      rw [hMeq]
      dsimp [Q]
      rw [T_bary A B C α β γ (le_of_lt ha) (le_of_lt hb) (le_of_lt hc) hs,
        T_bary A B C μ ν ρ hμ hν hρ hm,T_bary A B C x y z hx hy hz hxyz]
      rw [hα,hβ,hγ]
      ring
    calc
      3*T (bary A B C α β γ) A B C =
          t*(3*T M A B C)+(1-t)*(3*T Q A B C) := by rw [hTp]; ring
      _ ≤ t*(2*S M A B C)+(1-t)*(2*S Q A B C) :=
          add_le_add (mul_le_mul_of_nonneg_left hMbound ht0)
            (mul_le_mul_of_nonneg_left hQbound (sub_nonneg.mpr ht1))
      _ = 2*S (bary A B C α β γ) A B C := by rw [hSp]; ring

/-- The exact strict-interior taxicab Erdős–Mordell theorem.
The coordinates are fixed. Noncollinearity is the explicit determinant condition;
all three supporting-line denominators are positive by `side_denominators_positive`. -/
theorem taxicab_erdos_mordell_strict (A B C : Point) (α β γ : ℝ)
    (noncollinear :
      (B.1-A.1)*(C.2-A.2)-(B.2-A.2)*(C.1-A.1) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (weights_sum : α+β+γ=1) :
    let P : Point := (α*A.1+β*B.1+γ*C.1, α*A.2+β*B.2+γ*C.2)
    2*(d P A+d P B+d P C) ≥ 3*(h P B C+h P C A+h P A B) := by
  exact main_bound A B C α β γ noncollinear hα hβ hγ weights_sum

end Taxicab
