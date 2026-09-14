import DivisorF.ExceptionalEndpointManuscriptShift
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal manuscript radius scale for Lemma 6.1

The preceding shift layer keeps the two scale comparisons

`radiusScale * logScale <= lowerScale`

and

`radiusScale * variationScale <= lowerScale`

explicit.  In the manuscript the radius scale is not arbitrary: it is exactly
`Y^eta / log Y`, while the common lower main scale is comparable with `Y^eta`.
This module discharges the algebra attached to that literal choice.

No short-interval prime theorem is proved here.  The raw von-Mangoldt shift
estimate and the smallness of the real exceptional set remain external inputs.
The only remaining elementary comparison on the variation side is that the
variation scale is at most the logarithmic scale in the sufficiently-large
range; under the intended specialization this reads `Y^(eta-1) <= log Y`.
-/

namespace DivisorF

open scoped ENNReal

/-- The radius scale used literally in the manuscript, expressed relative to a
common lower main scale and the logarithmic scale. -/
noncomputable def manuscriptRadiusScale (lowerScale logScale : ℝ) : ℝ :=
  lowerScale / logScale

/-- Positivity of the literal radius scale. -/
theorem manuscriptRadiusScale_nonneg
    {lowerScale logScale : ℝ}
    (hlower : 0 ≤ lowerScale) (hlog : 0 < logScale) :
    0 ≤ manuscriptRadiusScale lowerScale logScale := by
  exact div_nonneg hlower (le_of_lt hlog)

/-- Multiplying the literal radius scale by the logarithmic scale recovers the
common lower scale exactly. -/
theorem manuscriptRadiusScale_mul_log
    {lowerScale logScale : ℝ}
    (hlog : 0 < logScale) :
    manuscriptRadiusScale lowerScale logScale * logScale = lowerScale := by
  dsimp [manuscriptRadiusScale]
  exact div_mul_cancel₀ lowerScale (ne_of_gt hlog)

/-- If the power-variation scale is dominated by the logarithmic scale, then
the second manuscript scale comparison follows automatically from the same
literal radius choice. -/
theorem manuscriptRadiusScale_mul_variation_le
    {lowerScale logScale variationScale : ℝ}
    (hlower : 0 ≤ lowerScale) (hlog : 0 < logScale)
    (hvariation : variationScale ≤ logScale) :
    manuscriptRadiusScale lowerScale logScale * variationScale ≤ lowerScale := by
  have hradius : 0 ≤ manuscriptRadiusScale lowerScale logScale :=
    manuscriptRadiusScale_nonneg hlower hlog
  calc
    manuscriptRadiusScale lowerScale logScale * variationScale ≤
        manuscriptRadiusScale lowerScale logScale * logScale :=
      mul_le_mul_of_nonneg_left hvariation hradius
    _ = lowerScale := manuscriptRadiusScale_mul_log hlog

/-- Literal-scale data for the project-owned normalization in Lemma 6.1.

Compared with `IntegerExceptionalManuscriptShiftData`, this structure removes
both free scale-comparison fields.  The radius scale is definitionally
`lowerScale / logScale`; the logarithmic comparison becomes an equality, while
the variation comparison is reduced to the single elementary inequality
`variationScale <= logScale`.
-/
structure IntegerExceptionalLiteralScaleData
    (bad : Finset ℕ) (H : ℕ)
    (A M : ℝ → ℝ) (delta : ℝ) where
  delta_nonneg : 0 ≤ delta
  lowerScale : ℝ
  lowerScale_nonneg : 0 ≤ lowerScale
  logScale : ℝ
  logScale_pos : 0 < logScale
  variationScale : ℝ
  variationScale_nonneg : 0 ≤ variationScale
  variationScale_le_log : variationScale ≤ logScale
  radiusFraction : ℝ
  radiusFraction_nonneg : 0 ≤ radiusFraction
  statisticCoeff : ℝ
  statisticCoeff_nonneg : 0 ≤ statisticCoeff
  mainCoeff : ℝ
  mainCoeff_nonneg : 0 ≤ mainCoeff
  radiusBound :
    (H : ℝ) + 1 ≤
      radiusFraction * manuscriptRadiusScale lowerScale logScale
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

/-- The literal manuscript scale specializes the previous manuscript-shaped
interface and discharges both scale-comparison obligations. -/
noncomputable def IntegerExceptionalLiteralScaleData.toManuscriptShiftData
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalLiteralScaleData bad H A M delta) :
    IntegerExceptionalManuscriptShiftData bad H A M delta where
  delta_nonneg := data.delta_nonneg
  lowerScale := data.lowerScale
  lowerScale_nonneg := data.lowerScale_nonneg
  radiusFraction := data.radiusFraction
  radiusFraction_nonneg := data.radiusFraction_nonneg
  radiusScale := manuscriptRadiusScale data.lowerScale data.logScale
  radiusScale_nonneg :=
    manuscriptRadiusScale_nonneg data.lowerScale_nonneg data.logScale_pos
  logScale := data.logScale
  logScale_nonneg := le_of_lt data.logScale_pos
  variationScale := data.variationScale
  variationScale_nonneg := data.variationScale_nonneg
  statisticCoeff := data.statisticCoeff
  statisticCoeff_nonneg := data.statisticCoeff_nonneg
  mainCoeff := data.mainCoeff
  mainCoeff_nonneg := data.mainCoeff_nonneg
  radiusBound := data.radiusBound
  radiusScale_mul_log_le := by
    exact le_of_eq (manuscriptRadiusScale_mul_log data.logScale_pos)
  radiusScale_mul_variation_le :=
    manuscriptRadiusScale_mul_variation_le data.lowerScale_nonneg
      data.logScale_pos data.variationScale_le_log
  statisticCoeff_small := data.statisticCoeff_small
  mainCoeff_small := data.mainCoeff_small
  main_nonneg := data.main_nonneg
  main_lower := data.main_lower
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw
  localScale := data.localScale

/-- One-scale Lemma 6.1 transfer from the literal quotient-by-log radius scale
to the fixed-error real-to-integer thickening certificate. -/
noncomputable def fixedErrorRealThickeningCertificate_of_literalScale
    {bad : Finset ℕ} {H Y k : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalLiteralScaleData bad H A M delta)
    (radiusLarge : 1 ≤ H)
    (exceptionalFinite :
      MeasureTheory.volume {u : ℝ | RealRelativeBad A M (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A M (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_manuscriptShift
    data.toManuscriptShiftData radiusLarge exceptionalFinite exceptionalMassSmall

/-- Family-level literal-scale interface.  The only scale comparison left to
the caller is `variationScale <= logScale`; the quotient-by-log identity and
both radius-scale products are discharged internally. -/
def FixedPrecisionLiteralScaleShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radius : ℕ → ℕ → ℕ)
    (A M : ℕ → ℕ → ℝ → ℝ)
    (delta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    let H := radius k Y
    ∃ _data : IntegerExceptionalLiteralScaleData
        bad H (A k Y) (M k Y) (delta k),
      1 ≤ H ∧
      MeasureTheory.volume
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} ≠ ∞ ∧
      MeasureTheory.volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- Literal-scale families specialize the manuscript-shift family already
consumed by the global exceptional-set construction. -/
theorem fixedPrecisionManuscriptShiftLebesgueBounds_of_literalScale
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionLiteralScaleShiftLebesgueBounds
      E radius A M delta threshold) :
    FixedPrecisionManuscriptShiftLebesgueBounds E radius A M delta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionLiteralScaleShiftLebesgueBounds] at h
  rcases h k hk Y hY with ⟨data, hH, hfinite, hmass⟩
  exact ⟨data.toManuscriptShiftData, hH, hfinite, hmass⟩

/-- **Lemma 6.1 literal-radius global-window chain.**

Once the raw local estimates are supplied at the literal quotient-by-log
radius scale, the remaining project-owned normalization, Lebesgue thickening,
diagonalisation and arbitrary-window sparsity are all discharged. -/
theorem eventuallySparseGlobalDyadicWindows_of_literalScaleShiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionLiteralScaleShiftLebesgueBounds
      E radius A M delta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_manuscriptShiftLebesgue hsupp
    (fixedPrecisionManuscriptShiftLebesgueBounds_of_literalScale h)

end DivisorF
