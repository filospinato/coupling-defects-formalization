import DivisorF.CumulativeBoundary
import DivisorF.MultiplicityCorollaries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Canonical paper-facing cumulative boundary statement

This module records the exact type-indexed equality that appears in Theorem 3.5
of the manuscript.  The crossing proof itself remains in `CumulativeBoundary`;
here we only identify the quotient-type fibres of the cumulative family and
package the theorem in the paper's notation.
-/

namespace DivisorF

/-- The paper term `t_s(N) d_s(N)`, including its empty-type convention. -/
noncomputable def paperTypeContribution (N s : ℕ) : ℤ :=
  (typeMultiplicity N s : ℤ) * paperTypeDefect N s

/-- Sum of the defects in one quotient class is exactly `t_s(N)d_s(N)`. -/
theorem sum_typePrimes_fibreDefect_eq_paperTypeContribution
    (N s : ℕ) :
    (∑ q ∈ typePrimes N s, fibreDefect q) = paperTypeContribution N s := by
  classical
  by_cases hocc : TypeOccupied N s
  · calc
      (∑ q ∈ typePrimes N s, fibreDefect q)
          = ∑ _q ∈ typePrimes N s, typeDefect hocc := by
              apply Finset.sum_congr rfl
              intro q hq
              exact fibreDefect_eq_typeDefect hocc hq
      _ = paperTypeContribution N s := by
            simp [paperTypeContribution, paperTypeDefect,
              typeMultiplicity, hocc]
  · have hempty : typePrimes N s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact hocc ⟨q, hq⟩
    simp [paperTypeContribution, paperTypeDefect,
      typeMultiplicity, hocc, hempty]

/--
The cumulative fibre sum is exactly the quotient-type sum
`Σ_{s=2}^K t_s(N)d_s(N)`.
-/
theorem cumulativeDefectSum_eq_paperTypeContributionSum
    (N K : ℕ) :
    cumulativeDefectSum N K
      = ∑ s ∈ Finset.Icc 2 K, paperTypeContribution N s := by
  classical
  have hmaps :
      ∀ q ∈ cumulativeFibres N K,
        q.quotientType ∈ Finset.Icc 2 K := by
    intro q hq
    exact Finset.mem_Icc.mpr (mem_cumulativeFibres.mp hq)
  have hfiber :
      ∀ s ∈ Finset.Icc 2 K,
        (cumulativeFibres N K).filter (fun q => q.quotientType = s)
          = typePrimes N s := by
    intro s hs
    ext q
    simp only [Finset.mem_filter, mem_cumulativeFibres, mem_typePrimes]
    constructor
    · intro h
      exact h.2
    · intro hqs
      refine ⟨?_, hqs⟩
      rw [hqs]
      exact Finset.mem_Icc.mp hs
  unfold cumulativeDefectSum
  symm
  calc
    ∑ s ∈ Finset.Icc 2 K, paperTypeContribution N s
        = ∑ s ∈ Finset.Icc 2 K,
            ∑ q ∈ (cumulativeFibres N K).filter
              (fun q => q.quotientType = s), fibreDefect q := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hfiber s hs,
            sum_typePrimes_fibreDefect_eq_paperTypeContribution]
    _ = ∑ q ∈ cumulativeFibres N K, fibreDefect q := by
          exact Finset.sum_fiberwise_of_maps_to
            hmaps (fun q : LargePrime N => fibreDefect q)

/--
**Theorem 3.5, canonical paper-facing form.**

The hypotheses are stated exactly as in the manuscript even though the
underlying finite inequality is valid in a slightly larger Lean range.
-/
theorem paperCumulativeBoundaryBudget
    {N K : ℕ}
    (_hN : 2 ≤ N)
    (_hK2 : 2 ≤ K)
    (_hKsqrt : K ≤ Nat.sqrt N) :
    (∑ s ∈ Finset.Icc 2 K, paperTypeContribution N s)
        = cumulativeDefectSum N K
      ∧ cumulativeDefectSum N K
        ≤ (cumulativeBoundaryCapacity K : ℤ) := by
  constructor
  · exact (cumulativeDefectSum_eq_paperTypeContributionSum N K).symm
  · exact cumulativeDefectSum_le

end DivisorF
