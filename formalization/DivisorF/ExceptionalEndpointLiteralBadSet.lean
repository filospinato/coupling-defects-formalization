import DivisorF.ExceptionalEndpointFixedError

set_option linter.style.header false

/-!
# Literal fixed-error bad endpoint sets for Lemma 6.1

The integer discretisation in the manuscript does not start from an arbitrary
finite set of centres: at each dyadic scale it takes *all* integers in
`[Y,2Y)` that violate the prescribed relative-error estimate.  This distinction
is semantically important.  A cardinality bound for an arbitrary subset of bad
points does not imply that points outside the eventual global exceptional set
are good.

This module makes the fixed-error set literal and records both directions of
its membership criterion.  It then specializes the fixed-error thickening
interface to those exact sets.  Thus the later diagonal exceptional set is
built from the complete bad traces used in the paper, not from caller-chosen
subsets.
-/

namespace DivisorF

/-- The literal relative-error condition is classically decidable; naming one
instance keeps every filter below on the same decision procedure. -/
noncomputable local instance realRelativeBadDecidablePred
    (A M : ℝ → ℝ) (delta : ℝ) :
    DecidablePred fun n : ℕ => RealRelativeBad A M delta (n : ℝ) :=
  fun _ => Classical.dec _

/-- All integer endpoints in `[Y,2Y)` that violate the literal relative-error
estimate with main term `x^eta`. -/
noncomputable def literalFixedErrorBadEndpoints
    (Y : ℕ) (A : ℝ → ℝ) (delta eta : ℝ) : Finset ℕ :=
  (Finset.Ico Y (2 * Y)).filter fun n =>
    RealRelativeBad A (fun x => x ^ eta) delta (n : ℝ)

/-- Exact membership criterion for the manuscript's fixed-error bad set. -/
theorem mem_literalFixedErrorBadEndpoints_iff
    {Y n : ℕ} {A : ℝ → ℝ} {delta eta : ℝ} :
    n ∈ literalFixedErrorBadEndpoints Y A delta eta ↔
      Y ≤ n ∧ n < 2 * Y ∧
        RealRelativeBad A (fun x => x ^ eta) delta (n : ℝ) := by
  simp [literalFixedErrorBadEndpoints, and_assoc]

/-- Literal fixed-error bad sets have exactly the dyadic support required by
the diagonal construction. -/
theorem literalFixedErrorBadEndpoints_supported
    {Y n : ℕ} {A : ℝ → ℝ} {delta eta : ℝ}
    (hn : n ∈ literalFixedErrorBadEndpoints Y A delta eta) :
    Y ≤ n ∧ n < 2 * Y := by
  have h := mem_literalFixedErrorBadEndpoints_iff.mp hn
  exact ⟨h.1, h.2.1⟩

/-- Completeness of the literal bad set: a point in the dyadic block that is
not selected is genuinely good at that error level.  This is the direction
missing from an arbitrary-subset interface. -/
theorem not_realRelativeBad_of_not_mem_literalFixedErrorBadEndpoints
    {Y n : ℕ} {A : ℝ → ℝ} {delta eta : ℝ}
    (hY : Y ≤ n) (h2Y : n < 2 * Y)
    (hn : n ∉ literalFixedErrorBadEndpoints Y A delta eta) :
    ¬ RealRelativeBad A (fun x => x ^ eta) delta (n : ℝ) := by
  intro hbad
  exact hn (mem_literalFixedErrorBadEndpoints_iff.mpr ⟨hY, h2Y, hbad⟩)

/-- Family of the exact fixed-error bad sets used by the manuscript. -/
noncomputable def literalFixedPrecisionBadEndpoints
    (A : ℕ → ℕ → ℝ → ℝ)
    (delta eta : ℕ → ℝ) (k Y : ℕ) : Finset ℕ :=
  literalFixedErrorBadEndpoints Y (A k Y) (delta k) (eta k)

/-- The literal family automatically satisfies the support condition consumed
by the dyadic diagonalisation. -/
theorem literalFixedPrecisionBadEndpoints_support
    {A : ℕ → ℕ → ℝ → ℝ} {delta eta : ℕ → ℝ} :
    FixedPrecisionExceptionalSupport
      (literalFixedPrecisionBadEndpoints A delta eta) := by
  intro k Y n hn
  exact literalFixedErrorBadEndpoints_supported hn

/-- Paper-shaped fixed-precision input: the thickening data are required for
the *complete* bad finset rather than for an arbitrary caller-supplied set. -/
def LiteralFixedPrecisionManuscriptDiscretisationBounds
    (radiusFraction : ℕ → ℝ)
    (A : ℕ → ℕ → ℝ → ℝ)
    (delta eta : ℕ → ℝ)
    (regime : ∀ k, ManuscriptRadiusRegime (eta k) (radiusFraction k))
    (threshold : ℕ → ℕ) : Prop :=
  FixedPrecisionManuscriptDiscretisationBounds
    (literalFixedPrecisionBadEndpoints A delta eta)
    radiusFraction A delta eta regime threshold

/-- The literal fixed-precision interface produces the manuscript's sparse
single global exceptional set.  Unlike the earlier generic version, its traces
are definitionally the full bad sets at the selected reciprocal precisions. -/
theorem eventuallySparseGlobalDyadicWindows_of_literalManuscriptDiscretisation
    {radiusFraction : ℕ → ℝ}
    {A : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {regime : ∀ k, ManuscriptRadiusRegime (eta k) (radiusFraction k)}
    {threshold : ℕ → ℕ}
    (h : LiteralFixedPrecisionManuscriptDiscretisationBounds
      radiusFraction A delta eta regime threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet
        (literalFixedPrecisionBadEndpoints A delta eta) threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_manuscriptDiscretisation
    literalFixedPrecisionBadEndpoints_support h

/-- On an exact dyadic block, exclusion from the global diagonal exceptional
set implies goodness at the precision selected for that block.

This is the semantic companion to the sparsity theorem: it records the
manuscript's crucial fact that the global set removes *all* points failing the
currently selected fixed-error estimate. -/
theorem good_at_diagonal_precision_of_not_mem_global
    {A : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    {j n : ℕ}
    (hnblock : n ∈ exceptionalDyadicBlock j)
    (hnglobal : n ∉ globalDiagonalExceptionalSet
      (literalFixedPrecisionBadEndpoints A delta eta) threshold) :
    ¬ RealRelativeBad
      (A (exceptionalDiagonalPrecision threshold (2 ^ j)) (2 ^ j))
      (fun x => x ^ eta (exceptionalDiagonalPrecision threshold (2 ^ j)))
      (delta (exceptionalDiagonalPrecision threshold (2 ^ j)))
      (n : ℝ) := by
  have hscale : exceptionalDyadicScale n = 2 ^ j :=
    exceptionalDyadicScale_eq_of_mem_block hnblock
  have hnnot :
      n ∉ literalFixedPrecisionBadEndpoints A delta eta
        (exceptionalDiagonalPrecision threshold (2 ^ j)) (2 ^ j) := by
    simpa [globalDiagonalExceptionalSet, diagonalExceptionalEndpoints, hscale] using hnglobal
  have hbounds : 2 ^ j ≤ n ∧ n < 2 * (2 ^ j) := by
    simpa [exceptionalDyadicBlock] using (Finset.mem_Ico.mp hnblock)
  exact not_realRelativeBad_of_not_mem_literalFixedErrorBadEndpoints
    hbounds.1 hbounds.2 hnnot

end DivisorF
