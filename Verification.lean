module
public import Taxicab

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace TaxicabVerification

/-- Independent restatement using only pairs of real numbers and the raw formulas. -/
theorem exact_statement (A B C : ℝ × ℝ) (α β γ : ℝ)
    (noncollinear : (B.1-A.1)*(C.2-A.2)-(B.2-A.2)*(C.1-A.1) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (weights_sum : α+β+γ=1) :
    let P : ℝ × ℝ := (α*A.1+β*B.1+γ*C.1, α*A.2+β*B.2+γ*C.2)
    2*((|P.1-A.1|+|P.2-A.2|)+(|P.1-B.1|+|P.2-B.2|)+(|P.1-C.1|+|P.2-C.2|)) ≥
    3*(|(C.1-B.1)*(P.2-B.2)-(C.2-B.2)*(P.1-B.1)| / max |C.1-B.1| |C.2-B.2| +
       |(A.1-C.1)*(P.2-C.2)-(A.2-C.2)*(P.1-C.1)| / max |A.1-C.1| |A.2-C.2| +
       |(B.1-A.1)*(P.2-A.2)-(B.2-A.2)*(P.1-A.1)| / max |B.1-A.1| |B.2-A.2|) := by
  exact Taxicab.taxicab_erdos_mordell_strict A B C α β γ noncollinear hα hβ hγ weights_sum

/-- The divisions in the exact statement all have strictly positive denominators. -/
theorem exact_denominators_positive (A B C : ℝ × ℝ)
    (noncollinear : (B.1-A.1)*(C.2-A.2)-(B.2-A.2)*(C.1-A.1) ≠ 0) :
    0 < max |C.1-B.1| |C.2-B.2| ∧
    0 < max |A.1-C.1| |A.2-C.2| ∧
    0 < max |B.1-A.1| |B.2-A.2| :=
  Taxicab.side_denominators_positive A B C noncollinear

end TaxicabVerification

set_option format.width 120
#check @Taxicab.taxicab_erdos_mordell_strict
#print axioms Taxicab.taxicab_erdos_mordell_strict
#check @TaxicabVerification.exact_statement
#print axioms TaxicabVerification.exact_statement
#check @Taxicab.sharpness
#print axioms Taxicab.sharpness
#check @Taxicab.sharpness_distances
#print axioms Taxicab.sharpness_distances
#check @TaxicabVerification.exact_denominators_positive
#print axioms TaxicabVerification.exact_denominators_positive
