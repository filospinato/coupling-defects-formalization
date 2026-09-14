import DivisorF.ExceptionalEndpointQuantitativeShift
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Manuscript-scale shift package for Lemma 6.1

The quantitative layer already separates the external/raw shift estimates from
the project-owned normalization.  This module instantiates that normalization
with the two scales that occur literally in the manuscript:

* `(H + 1) * logScale` for the von-Mangoldt interval shift;
* `H * variationScale` for the variation of the main term.

The intended specialization is

* `radiusScale = Y^eta / log Y`,
* `logScale = log Y`,
* `variationScale = Y^(eta - 1)`,
* `lowerScale` comparable with `Y^eta`.

No prime-distribution theorem is proved here.  The two raw shift inequalities
remain explicit hypotheses.  What is machine-checked is the manuscript's own
algebraic passage from one radius choice to the normalized `delta / 8` shift
package consumed by the real-to-integer thickening argument.
-/

namespace DivisorF

open scoped ENNReal

/-- Literal-scale data for the shift step in Lemma 6.1.

`radiusFraction` is the single small constant represented by `c_delta` in the
paper.  The two `radiusScale_mul_...` hypotheses are the elementary scale
comparisons which, under the intended specialization, read

`(Y^eta / log Y) * log Y <= lowerScale`

and

`(Y^eta / log Y) * Y^(eta - 1) <= lowerScale`.

Thus this structure leaves the actual short-interval estimate external while
formalizing the one-radius bookkeeping of the project. -/
structure IntegerExceptionalManuscriptShiftData
    (bad : Finset ℕ) (H : ℕ)
    (A M : ℝ → ℝ) (delta : ℝ) where
  delta_nonneg : 0 ≤ delta
  lowerScale : ℝ
  lowerScale_nonneg : 0 ≤ lowerScale
  radiusFraction : ℝ
  radiusFraction_nonneg : 0 ≤ radiusFraction
  radiusScale : ℝ
  radiusScale_nonneg : 0 ≤ radiusScale
  logScale : ℝ
  logScale_nonneg : 0 ≤ logScale
  variationScale : ℝ
  variationScale_nonneg : 0 ≤ variationScale
  statisticCoeff : ℝ
  statisticCoeff_nonneg : 0 ≤ statisticCoeff
  mainCoeff : ℝ
  mainCoeff_nonneg : 0 ≤ mainCoeff
  radiusBound : (H : ℝ) + 1 ≤ radiusFraction * radiusScale
  radiusScale_mul_log_le : radiusScale * logScale ≤ lowerScale
  radiusScale_mul_variation_le : radiusScale * variationScale ≤ lowerScale
  statisticCoeff_small : statisticCoeff * radiusFraction ≤ delta / 8
  mainCoeff_small : mainCoeff * radiusFraction ≤ delta / 8
  main_nonneg : ∀ n ∈ bad, 0 ≤ M (n : ℝ)
  main_lower : ∀ n ∈ bad, lowerScale ≤ M (n : ℝ)
  badAtCentre : ∀ n ∈ bad, RealRelativeBad A M delta (n : ℝ)
  statisticShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |A (n : ℝ) - A u| ≤ statisticCoeff * (((H : ℝ) + 1) * logScale)
  mainShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |M (n : ℝ) - M u| ≤ mainCoeff * ((H : ℝ) * variationScale)
  localScale : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    M u ≤ (3 / 2 : ℝ) * M (n : ℝ)

/-- The literal `(H+1) log Y` scale is controlled by the one radius fraction. -/
theorem IntegerExceptionalManuscriptShiftData.statisticScale_le
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalManuscriptShiftData bad H A M delta) :
    ((H : ℝ) + 1) * data.logScale ≤
      data.radiusFraction * data.lowerScale := by
  calc
    ((H : ℝ) + 1) * data.logScale ≤
        (data.radiusFraction * data.radiusScale) * data.logScale :=
      mul_le_mul_of_nonneg_right data.radiusBound data.logScale_nonneg
    _ = data.radiusFraction * (data.radiusScale * data.logScale) := by ring
    _ ≤ data.radiusFraction * data.lowerScale :=
      mul_le_mul_of_nonneg_left data.radiusScale_mul_log_le
        data.radiusFraction_nonneg

/-- The literal `H * Y^(eta-1)` scale is controlled by the same radius
fraction.  The harmless replacement `H <= H+1` lets the same radius bound serve
both estimates. -/
theorem IntegerExceptionalManuscriptShiftData.mainScale_le
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalManuscriptShiftData bad H A M delta) :
    (H : ℝ) * data.variationScale ≤
      data.radiusFraction * data.lowerScale := by
  have hH : (H : ℝ) ≤ (H : ℝ) + 1 := by linarith
  have hrad : (H : ℝ) ≤ data.radiusFraction * data.radiusScale :=
    hH.trans data.radiusBound
  calc
    (H : ℝ) * data.variationScale ≤
        (data.radiusFraction * data.radiusScale) * data.variationScale :=
      mul_le_mul_of_nonneg_right hrad data.variationScale_nonneg
    _ = data.radiusFraction * (data.radiusScale * data.variationScale) := by ring
    _ ≤ data.radiusFraction * data.lowerScale :=
      mul_le_mul_of_nonneg_left data.radiusScale_mul_variation_le
        data.radiusFraction_nonneg

/-- The manuscript-shaped scale package specializes the generic one-radius
interface without introducing any normalized pointwise shift hypothesis. -/
def IntegerExceptionalManuscriptShiftData.toRadiusShiftData
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalManuscriptShiftData bad H A M delta) :
    IntegerExceptionalRadiusShiftData bad H A M delta where
  delta_nonneg := data.delta_nonneg
  lowerScale := data.lowerScale
  lowerScale_nonneg := data.lowerScale_nonneg
  radiusFraction := data.radiusFraction
  radiusFraction_nonneg := data.radiusFraction_nonneg
  statisticScale := ((H : ℝ) + 1) * data.logScale
  mainScale := (H : ℝ) * data.variationScale
  statisticScale_nonneg :=
    mul_nonneg (by positivity) data.logScale_nonneg
  mainScale_nonneg :=
    mul_nonneg (by positivity) data.variationScale_nonneg
  statisticCoeff := data.statisticCoeff
  mainCoeff := data.mainCoeff
  statisticCoeff_nonneg := data.statisticCoeff_nonneg
  mainCoeff_nonneg := data.mainCoeff_nonneg
  statisticScale_le := data.statisticScale_le
  mainScale_le := data.mainScale_le
  statisticCoeff_small := data.statisticCoeff_small
  mainCoeff_small := data.mainCoeff_small
  main_nonneg := data.main_nonneg
  main_lower := data.main_lower
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw
  localScale := data.localScale

/-- One-scale Lemma 6.1 transfer from the literal manuscript scales to the
fixed-error real-to-integer thickening certificate. -/
noncomputable def fixedErrorRealThickeningCertificate_of_manuscriptShift
    {bad : Finset ℕ} {H Y k : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalManuscriptShiftData bad H A M delta)
    (radiusLarge : 1 ≤ H)
    (exceptionalFinite :
      MeasureTheory.volume {u : ℝ | RealRelativeBad A M (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A M (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_radiusShift
    data.toRadiusShiftData radiusLarge exceptionalFinite exceptionalMassSmall

/-- Family-level interface whose local scale terms have exactly the form used
in the manuscript.  Only the raw shift estimates and the external exceptional
set mass input remain upstream. -/
def FixedPrecisionManuscriptShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radius : ℕ → ℕ → ℕ)
    (A M : ℕ → ℕ → ℝ → ℝ)
    (delta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    let H := radius k Y
    ∃ _data : IntegerExceptionalManuscriptShiftData
        bad H (A k Y) (M k Y) (delta k),
      1 ≤ H ∧
      MeasureTheory.volume
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} ≠ ∞ ∧
      MeasureTheory.volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- The literal manuscript-scale family discharges the generic radius family
already consumed by the downstream thickening and diagonalisation chain. -/
theorem fixedPrecisionRadiusShiftLebesgueBounds_of_manuscript
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionManuscriptShiftLebesgueBounds
      E radius A M delta threshold) :
    FixedPrecisionRadiusShiftLebesgueBounds E radius A M delta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionManuscriptShiftLebesgueBounds] at h
  rcases h k hk Y hY with ⟨data, hH, hfinite, hmass⟩
  exact ⟨data.toRadiusShiftData, hH, hfinite, hmass⟩

/-- **Lemma 6.1 manuscript-scale global-window chain.**

Once the raw estimates are supplied in their literal `(H+1) log Y` and
`H Y^(eta-1)` forms, together with the standard scale comparisons for the
chosen radius, all remaining real-to-integer thickening, finite-overlap,
diagonalisation and global-window bookkeeping is project-owned and already
machine-checked by this chain. -/
theorem eventuallySparseGlobalDyadicWindows_of_manuscriptShiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionManuscriptShiftLebesgueBounds
      E radius A M delta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_radiusShiftLebesgue hsupp
    (fixedPrecisionRadiusShiftLebesgueBounds_of_manuscript h)

end DivisorF
