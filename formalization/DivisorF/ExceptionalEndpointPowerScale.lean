import DivisorF.ExceptionalEndpointManuscriptScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Power/log specialization of the Lemma 6.1 radius scale

This module specializes the remaining elementary scales to the literal ones in
the manuscript:

* lower main scale `Y^eta`;
* logarithmic scale `log Y`;
* variation scale `Y^(eta - 1)`;
* radius scale `Y^eta / log Y`.

For sufficiently large `Y` the only nontrivial comparison needed by the
previous layer is immediate: if `eta <= 1` and `1 <= log Y`, then
`Y^(eta-1) <= 1 <= log Y`.  Thus the power-variation comparison is no longer an
upstream field.  The raw von-Mangoldt shift majorant remains an explicit
analytic input, as required by the trust boundary.
-/

namespace DivisorF

open scoped ENNReal

/-- Literal main scale `Y^eta`. -/
noncomputable def manuscriptPowerMainScale (Y : ℕ) (eta : ℝ) : ℝ :=
  (Y : ℝ) ^ eta

/-- Literal power-variation scale `Y^(eta-1)`. -/
noncomputable def manuscriptPowerVariationScale (Y : ℕ) (eta : ℝ) : ℝ :=
  (Y : ℝ) ^ (eta - 1)

/-- Literal thickening-radius scale `Y^eta / log Y`. -/
noncomputable def manuscriptPowerRadiusScale (Y : ℕ) (eta : ℝ) : ℝ :=
  manuscriptRadiusScale (manuscriptPowerMainScale Y eta) (Real.log (Y : ℝ))

/-- The power-variation scale is at most one when `Y >= 1` and `eta <= 1`. -/
theorem manuscriptPowerVariationScale_le_one
    {Y : ℕ} {eta : ℝ}
    (hY : 1 ≤ Y) (heta : eta ≤ 1) :
    manuscriptPowerVariationScale Y eta ≤ 1 := by
  have hbase : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hexp : eta - 1 ≤ 0 := by linarith
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase hexp

/-- In the sufficiently-large range `1 <= log Y`, the manuscript's
`Y^(eta-1)` variation scale is automatically dominated by the logarithmic
scale. -/
theorem manuscriptPowerVariationScale_le_log
    {Y : ℕ} {eta : ℝ}
    (hY : 1 ≤ Y) (heta : eta ≤ 1)
    (hlog : 1 ≤ Real.log (Y : ℝ)) :
    manuscriptPowerVariationScale Y eta ≤ Real.log (Y : ℝ) := by
  exact (manuscriptPowerVariationScale_le_one hY heta).trans hlog

/-- The main power scale is nonnegative. -/
theorem manuscriptPowerMainScale_nonneg
    (Y : ℕ) (eta : ℝ) :
    0 ≤ manuscriptPowerMainScale Y eta := by
  exact Real.rpow_nonneg (by positivity) eta

/-- Literal power/log data for the project-owned shift normalization.

All three manuscript scales are now fixed definitionally.  The caller no
longer supplies either scale-comparison inequality: `eta <= 1`, `Y >= 1`, and
`1 <= log Y` imply the variation comparison, while division by `log Y`
discharges the statistic comparison exactly.
-/
structure IntegerExceptionalPowerScaleData
    (bad : Finset ℕ) (H Y : ℕ)
    (A M : ℝ → ℝ) (delta eta : ℝ) where
  delta_nonneg : 0 ≤ delta
  eta_le_one : eta ≤ 1
  Y_pos : 1 ≤ Y
  log_large : 1 ≤ Real.log (Y : ℝ)
  radiusFraction : ℝ
  radiusFraction_nonneg : 0 ≤ radiusFraction
  statisticCoeff : ℝ
  statisticCoeff_nonneg : 0 ≤ statisticCoeff
  mainCoeff : ℝ
  mainCoeff_nonneg : 0 ≤ mainCoeff
  radiusBound :
    (H : ℝ) + 1 ≤ radiusFraction * manuscriptPowerRadiusScale Y eta
  statisticCoeff_small : statisticCoeff * radiusFraction ≤ delta / 8
  mainCoeff_small : mainCoeff * radiusFraction ≤ delta / 8
  main_nonneg : ∀ n ∈ bad, 0 ≤ M (n : ℝ)
  main_lower : ∀ n ∈ bad, manuscriptPowerMainScale Y eta ≤ M (n : ℝ)
  badAtCentre : ∀ n ∈ bad, RealRelativeBad A M delta (n : ℝ)
  statisticShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |A (n : ℝ) - A u| ≤
      statisticCoeff * (((H : ℝ) + 1) * Real.log (Y : ℝ))
  mainShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |M (n : ℝ) - M u| ≤
      mainCoeff * ((H : ℝ) * manuscriptPowerVariationScale Y eta)
  localScale : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    M u ≤ (3 / 2 : ℝ) * M (n : ℝ)

/-- The literal power/log package specializes the quotient-by-log scale layer. -/
noncomputable def IntegerExceptionalPowerScaleData.toLiteralScaleData
    {bad : Finset ℕ} {H Y : ℕ}
    {A M : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalPowerScaleData bad H Y A M delta eta) :
    IntegerExceptionalLiteralScaleData bad H A M delta where
  delta_nonneg := data.delta_nonneg
  lowerScale := manuscriptPowerMainScale Y eta
  lowerScale_nonneg := manuscriptPowerMainScale_nonneg Y eta
  logScale := Real.log (Y : ℝ)
  logScale_pos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) data.log_large
  variationScale := manuscriptPowerVariationScale Y eta
  variationScale_nonneg := Real.rpow_nonneg (by positivity) (eta - 1)
  variationScale_le_log :=
    manuscriptPowerVariationScale_le_log data.Y_pos data.eta_le_one data.log_large
  radiusFraction := data.radiusFraction
  radiusFraction_nonneg := data.radiusFraction_nonneg
  statisticCoeff := data.statisticCoeff
  statisticCoeff_nonneg := data.statisticCoeff_nonneg
  mainCoeff := data.mainCoeff
  mainCoeff_nonneg := data.mainCoeff_nonneg
  radiusBound := data.radiusBound
  statisticCoeff_small := data.statisticCoeff_small
  mainCoeff_small := data.mainCoeff_small
  main_nonneg := data.main_nonneg
  main_lower := data.main_lower
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw
  localScale := data.localScale

/-- One-scale Lemma 6.1 transfer with the manuscript's actual `Y^eta`,
`log Y`, and `Y^(eta-1)` scales fixed definitionally. -/
noncomputable def fixedErrorRealThickeningCertificate_of_powerScale
    {bad : Finset ℕ} {H Y k : ℕ}
    {A M : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalPowerScaleData bad H Y A M delta eta)
    (radiusLarge : 1 ≤ H)
    (exceptionalFinite :
      MeasureTheory.volume {u : ℝ | RealRelativeBad A M (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A M (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_literalScale
    data.toLiteralScaleData radiusLarge exceptionalFinite exceptionalMassSmall

/-- Family-level power/log specialization. -/
def FixedPrecisionPowerScaleShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radius : ℕ → ℕ → ℕ)
    (A M : ℕ → ℕ → ℝ → ℝ)
    (delta eta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    let H := radius k Y
    ∃ _data : IntegerExceptionalPowerScaleData
        bad H Y (A k Y) (M k Y) (delta k) (eta k),
      1 ≤ H ∧
      MeasureTheory.volume
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} ≠ ∞ ∧
      MeasureTheory.volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- Power/log families specialize the literal-scale family. -/
theorem fixedPrecisionLiteralScaleShiftLebesgueBounds_of_powerScale
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionPowerScaleShiftLebesgueBounds
      E radius A M delta eta threshold) :
    FixedPrecisionLiteralScaleShiftLebesgueBounds E radius A M delta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionPowerScaleShiftLebesgueBounds] at h
  rcases h k hk Y hY with ⟨data, hH, hfinite, hmass⟩
  exact ⟨data.toLiteralScaleData, hH, hfinite, hmass⟩

/-- **Lemma 6.1 power/log global-window chain.**

At this point the entire project-owned normalization uses the exact scales from
the paper.  Upstream remain the raw short-interval statistic estimate, the
standard local power-variation estimate encoded in the data, and the external
smallness of the real exceptional set. -/
theorem eventuallySparseGlobalDyadicWindows_of_powerScaleShiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionPowerScaleShiftLebesgueBounds
      E radius A M delta eta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_literalScaleShiftLebesgue hsupp
    (fixedPrecisionLiteralScaleShiftLebesgueBounds_of_powerScale h)

end DivisorF
