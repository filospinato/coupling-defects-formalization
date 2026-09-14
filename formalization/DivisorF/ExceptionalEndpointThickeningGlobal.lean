import DivisorF.ExceptionalEndpointThickening
import DivisorF.ExceptionalEndpointGlobalWindow

set_option linter.style.header false

/-!
# Real thickening to the manuscript's global integer exceptional set

This module composes the project-owned pieces of Lemma 6.1 that sit downstream
of the literal Lebesgue thickening estimate.  Starting from the explicit
fixed-error real-thickening certificates, Lean now obtains the single global
integer exceptional set constructed by dyadic diagonalisation and proves the
paper's full cardinality conclusion on every window `[Y,2Y)`.

The external almost-all prime theorem is still absent.  The only remaining
upstream obligation is to construct the certificates themselves from the
manuscript's shift/symmetric-difference estimate and bounded-overlap measure
double count.
-/

namespace DivisorF

/-- **Lemma 6.1, global exceptional-set counting conclusion.**

Fixed-error real-thickening certificates, together with the literal support of
the integer bad sets on `[Y,2Y)`, produce one global set `E_eta ⊆ ℕ` satisfying
`|E_eta ∩ [Y,2Y)| = o(Y)` in division-free form.  This composes the fixed-error
count, dyadic diagonalisation, exact global-set realization, and the final
arbitrary-window two-block argument. -/
theorem eventuallySparseGlobalDyadicWindows_of_realThickening
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (hthick : FixedPrecisionRealThickeningBounds E threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_fixedPrecision hsupp
    (fixedPrecisionExceptionalBounds_of_realThickening hthick)

end DivisorF
