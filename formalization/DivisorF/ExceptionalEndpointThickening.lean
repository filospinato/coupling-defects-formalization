import DivisorF.ExceptionalEndpointConcreteDiagonal
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-error real-to-integer exceptional-endpoint transfer

The first step of Lemma 6.1 in the manuscript converts the external real-variable
almost-all estimate into a fixed-precision bound for bad integer endpoints.  The
analytic theorem itself is external and is not formalized here.  The project-owned
part is the thickening/bounded-overlap conversion: a bad integer forces a whole
real interval of nearby points to remain bad, while each real point belongs to
only `2h + O(1)` such intervals.

Rather than hiding that conversion inside the Gafni--Tao input, this module
records the exact quantitative output of the geometric double count and proves
its conversion to the division-free fixed-precision integer bound consumed by
`ExceptionalEndpointDiagonal`.

The remaining upstream obligation is deliberately narrow: for the concrete
Lebesgue exceptional set and `h = c_delta Y^eta / log Y`, establish the
`doubleCount` and `exceptionalMassSmall` fields below.  Those fields contain no
prime-number conclusion; they are precisely the manuscript's thickening and
real-measure estimates after enlarging to the adjacent dyadic blocks.
-/

namespace DivisorF

/-- A fixed-error thickening certificate at one dyadic scale.

`exceptionalMass` is the Lebesgue mass of the enlarged real exceptional set,
expressed abstractly as a nonnegative real number.  The inequality

`2 h * #bad <= (2 h + 1) * exceptionalMass`

is the bounded-overlap double count from Lemma 6.1, with the harmless `O(1)`
absorbed by `+1` after taking `h >= 1`.  The final field asks for the real
exceptional mass at twice the requested reciprocal precision; this factor
absorbs the overlap loss when passing back to integer cardinality. -/
structure FixedErrorRealThickeningCertificate
    (bad : Finset ℕ) (Y k : ℕ) where
  h : ℝ
  exceptionalMass : ℝ
  hLarge : 1 ≤ h
  exceptionalMass_nonneg : 0 ≤ exceptionalMass
  doubleCount :
    (2 * h) * (bad.card : ℝ) ≤ (2 * h + 1) * exceptionalMass
  exceptionalMassSmall :
    exceptionalMass * (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- The manuscript's bounded-overlap inequality loses at most a factor two:
under `h >= 1`, the number of bad integer centres is at most twice the enlarged
real exceptional mass. -/
theorem bad_card_le_two_mul_exceptionalMass
    {bad : Finset ℕ} {Y k : ℕ}
    (cert : FixedErrorRealThickeningCertificate bad Y k) :
    (bad.card : ℝ) ≤ 2 * cert.exceptionalMass := by
  have hoverlap :
      (2 * cert.h + 1) * cert.exceptionalMass ≤
        (4 * cert.h) * cert.exceptionalMass := by
    have hcoef : 2 * cert.h + 1 ≤ 4 * cert.h := by
      nlinarith [cert.hLarge]
    exact mul_le_mul_of_nonneg_right hcoef cert.exceptionalMass_nonneg
  have hcount :
      (2 * cert.h) * (bad.card : ℝ) ≤
        (4 * cert.h) * cert.exceptionalMass :=
    cert.doubleCount.trans hoverlap
  nlinarith [cert.hLarge, cert.exceptionalMass_nonneg]

/-- **Lemma 6.1, fixed-error real-to-integer counting transfer.**

A thickening certificate at reciprocal precision `1/k` implies the exact
integer cardinality estimate required by the later dyadic diagonalisation,
written without division as `#bad * k <= Y`. -/
theorem card_mul_precision_le_of_realThickening
    {bad : Finset ℕ} {Y k : ℕ}
    (cert : FixedErrorRealThickeningCertificate bad Y k) :
    bad.card * k ≤ Y := by
  have hbad : (bad.card : ℝ) ≤ 2 * cert.exceptionalMass :=
    bad_card_le_two_mul_exceptionalMass cert
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hmul :
      (bad.card : ℝ) * (k : ℝ) ≤
        (2 * cert.exceptionalMass) * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hbad hk
  have hreal : ((bad.card * k : ℕ) : ℝ) ≤ (Y : ℝ) := by
    calc
      ((bad.card * k : ℕ) : ℝ)
          = (bad.card : ℝ) * (k : ℝ) := by norm_num
      _ ≤ (2 * cert.exceptionalMass) * (k : ℝ) := hmul
      _ = cert.exceptionalMass * (2 * (k : ℝ)) := by ring
      _ ≤ (Y : ℝ) := cert.exceptionalMassSmall
  exact_mod_cast hreal

/-- Eventual fixed-precision thickening certificates, with exactly the quantifier
order used before diagonalisation in Lemma 6.1. -/
def FixedPrecisionRealThickeningBounds
    (E : ℕ → ℕ → Finset ℕ) (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    Nonempty (FixedErrorRealThickeningCertificate (E k Y) Y k)

/-- The real-thickening interface discharges the previously abstract
`FixedPrecisionExceptionalBounds` interface. -/
theorem fixedPrecisionExceptionalBounds_of_realThickening
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hthick : FixedPrecisionRealThickeningBounds E threshold) :
    FixedPrecisionExceptionalBounds E threshold := by
  intro k hk Y hY
  rcases hthick k hk Y hY with ⟨cert⟩
  exact card_mul_precision_le_of_realThickening cert

/-- Fixed-error thickening followed by the manuscript's dyadic diagonalisation
produces one integer exceptional family of relative density zero. -/
theorem eventuallyDyadicallySparse_diagonal_of_realThickening
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hthick : FixedPrecisionRealThickeningBounds E threshold) :
    EventuallyDyadicallySparse (diagonalExceptionalEndpoints E threshold) := by
  exact eventuallyDyadicallySparse_diagonalExceptionalEndpoints
    (fixedPrecisionExceptionalBounds_of_realThickening hthick)

/-- The same thickening input realizes the manuscript's *single global*
exceptional set, provided the finite bad sets have the literal support
`[Y,2Y)` from the discretisation.  This closes the fidelity gap between the
scale-indexed implementation and the global `E_eta ⊆ ℕ` used in the paper. -/
theorem eventuallySparseGlobalDyadicBlocks_of_realThickening
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (hthick : FixedPrecisionRealThickeningBounds E threshold) :
    EventuallySparseGlobalDyadicBlocks
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicBlocks_of_fixedPrecision hsupp
    (fixedPrecisionExceptionalBounds_of_realThickening hthick)

/-- End-to-end project-owned Section 6 transfer through the concrete translated
endpoint map `nu_eta(X)=floor(X-3X^eta)`: once the external real-variable input
has been converted into the explicit thickening certificates above, the bad
translated quotient endpoints are `o(Y)`.

This theorem composes the fixed-error real-to-integer count, diagonalisation,
and the already formalized bounded-multiplicity geometry of `nu_eta`. -/
theorem eventuallyDyadicallySparse_concreteTranslatedPullback_of_realThickening
    {eta : ℝ} {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (heta : 0 < eta) (heta1 : eta < 1)
    (hthick : FixedPrecisionRealThickeningBounds E threshold) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y (translatedEndpointMap eta)
        (diagonalExceptionalEndpoints E threshold Y)) := by
  exact eventuallyDyadicallySparse_concreteTranslatedPullback_of_bounds
    heta heta1 (fixedPrecisionExceptionalBounds_of_realThickening hthick)

end DivisorF
