import DivisorF.ExceptionalEndpointDiagonalAccuracy

set_option linter.style.header false

/-!
# Lemma 6.1: project-owned integer-discretisation core

This module packages the two project-owned outputs of the manuscript's
real-to-integer argument for the von Mangoldt short-interval statistic:

1. one global exceptional set has `o(Y)` integer points in every `[Y,2Y)`;
2. outside that same set the relative error tends to zero.

The input remains deliberately narrow and faithful.  At reciprocal precision
`1/k`, the external real-variable theorem supplies small exceptional mass, and
the standard local shift estimates supply the von-Mangoldt and power-variation
majorants.  The project's thickening, finite-overlap counting, radius
normalisation, dyadic diagonalisation and global-set bookkeeping then produce
the conclusion below.

Passing from the von Mangoldt asymptotic to a prime-count asymptotic by removing
proper prime powers is standard analytic support and is not made a separate
formalization target.
-/

namespace DivisorF

/-- The single global exceptional set generated from the literal reciprocal
bad traces of one fixed statistic `A` and exponent `eta`. -/
def integerDiscretisationExceptionalSet
    (A : ℝ → ℝ) (eta : ℝ) (threshold : ℕ → ℕ) : Set ℕ :=
  globalDiagonalExceptionalSet (reciprocalBadEndpoints A eta) threshold

/-- Division-free machine-checked form of the project-owned core conclusion of
Lemma 6.1: sparse integer exceptional windows and relative `o(1)` accuracy
outside the same set. -/
def IntegerDiscretisationCore
    (S : Set ℕ) (A : ℝ → ℝ) (eta : ℝ) : Prop :=
  EventuallySparseGlobalDyadicWindows S ∧
    EventuallyRelativeAccurateOutside S A eta

/-- **Lemma 6.1, integer-discretisation core.**

Assume the fixed-precision manuscript data for the complete `1/k`-bad traces.
Then the project's real-to-integer machinery constructs one global exceptional
set which is sparse in every dyadic window and outside which the relative error
of `A(x)` from `x^eta` tends to zero.

The hypothesis contains the external/support inputs explicitly; the conclusion
is the project-owned discretisation result. -/
theorem integerDiscretisationCore_of_manuscript
    {A : ℝ → ℝ} {eta : ℝ}
    {radiusFraction : ℕ → ℝ}
    {regime : ∀ k, ManuscriptRadiusRegime eta (radiusFraction k)}
    {threshold : ℕ → ℕ}
    (h : LiteralFixedPrecisionManuscriptDiscretisationBounds
      radiusFraction
      (fun _ _ => A)
      reciprocalError
      (fun _ => eta)
      regime threshold) :
    IntegerDiscretisationCore
      (integerDiscretisationExceptionalSet A eta threshold) A eta := by
  constructor
  · exact eventuallySparseGlobalDyadicWindows_of_literalManuscriptDiscretisation h
  · exact eventuallyRelativeAccurateOutside_globalDiagonal

end DivisorF
