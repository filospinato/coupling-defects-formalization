import DivisorF.ExceptionalEndpointDiagonal
import DivisorF.TranslatedEndpointCompleteBounds

set_option linter.style.header false

/-!
# Diagonal exceptional sets for the concrete translated endpoint

This module composes two project-owned pieces of Section 6:

1. fixed-precision integer exceptional estimates are diagonalised to one
   dyadically sparse scale family;
2. the manuscript map

   `nu_eta(X) = floor(X - 3 X^eta)`

   has uniformly bounded fibres and dyadic comparability, already proved from
   the concrete scalar bounds for `0 < eta < 1`.

The only input deliberately left here is the fixed-precision integer estimate
produced by the preceding real-to-integer thickening argument of Lemma 6.1.
No Gafni--Tao statement is asserted in Lean.
-/

namespace DivisorF

/-- **Section 6 diagonal-to-translated-endpoint transfer.**

Suppose that for every reciprocal precision `1/k` the real-to-integer stage has
produced finite integer exceptional sets `E k Y` that eventually contain at
most `Y/k` points in the relevant dyadic scale.  Then one may choose thresholds
so that, after diagonalising and pulling the resulting exceptional sets back
through the actual manuscript map `nu_eta`, the irregular translated endpoints
still form an `o(Y)` family.

Thus the only missing predecessor of this theorem is the fixed-precision
real-to-integer estimate itself; the diagonalisation and the bounded-
multiplicity translated pullback are both discharged inside Lean. -/
theorem exists_eventuallyDyadicallySparse_concreteTranslatedPullback_of_fixedPrecision
    {eta : ℝ} {E : ℕ → ℕ → Finset ℕ}
    (heta : 0 < eta) (heta1 : eta < 1)
    (hfixed : ∀ k : ℕ, 1 ≤ k → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      (E k Y).card * k ≤ Y) :
    ∃ threshold : ℕ → ℕ,
      EventuallyDyadicallySparse
        (fun Y => pulledBackBadEndpoints Y (translatedEndpointMap eta)
          (diagonalExceptionalEndpoints E threshold Y)) := by
  rcases exists_eventuallyDyadicallySparse_diagonal_of_fixedPrecision hfixed with
    ⟨threshold, hsparse⟩
  refine ⟨threshold, ?_⟩
  exact eventuallyDyadicallySparse_pulledBack_translatedEndpointMap_concrete
    heta heta1 hsparse

/-- Version for an already chosen threshold function.  This is useful when the
real-to-integer proof records quantitative thresholds rather than merely their
existence. -/
theorem eventuallyDyadicallySparse_concreteTranslatedPullback_of_bounds
    {eta : ℝ} {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (heta : 0 < eta) (heta1 : eta < 1)
    (hfixed : FixedPrecisionExceptionalBounds E threshold) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y (translatedEndpointMap eta)
        (diagonalExceptionalEndpoints E threshold Y)) := by
  exact eventuallyDyadicallySparse_pulledBack_translatedEndpointMap_concrete
    heta heta1
    (eventuallyDyadicallySparse_diagonalExceptionalEndpoints hfixed)

end DivisorF
