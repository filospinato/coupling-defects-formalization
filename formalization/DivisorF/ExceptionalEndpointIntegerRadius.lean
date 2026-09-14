import DivisorF.ExceptionalEndpointPowerScale
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Integer-radius specialization of the Lemma 6.1 thickening

The manuscript chooses a real thickening scale

`c_delta * Y^eta / log Y`

but the real-to-integer counting layer uses an integer radius `H` and the raw
von-Mangoldt shift majorant contains `(H+1) * log Y`.  This module makes the
project-owned rounding step explicit.  We choose

`H = floor(c_delta * Y^eta / log Y) - 1`.

As soon as the real scale has natural floor at least two, this gives both
`1 <= H` and the exact absorption

`H + 1 <= c_delta * Y^eta / log Y`.

Thus the `+1` is no longer an upstream scale hypothesis.  The analytic raw
short-interval estimate itself remains an explicit input, as required by the
trust boundary.
-/

namespace DivisorF

open scoped ENNReal

/-- Integer thickening radius corresponding to the manuscript's real radius
fraction times `Y^eta / log Y`.  Subtracting one is deliberate: it absorbs the
`+1` appearing in the symmetric-difference estimate. -/
noncomputable def manuscriptPowerIntegerRadius
    (Y : ℕ) (eta radiusFraction : ℝ) : ℕ :=
  ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊ - 1

/-- Once the unshifted natural floor is at least two, the concrete integer
radius is positive. -/
theorem manuscriptPowerIntegerRadius_pos
    {Y : ℕ} {eta radiusFraction : ℝ}
    (hlarge :
      2 ≤ ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊) :
    1 ≤ manuscriptPowerIntegerRadius Y eta radiusFraction := by
  dsimp [manuscriptPowerIntegerRadius]
  omega

/-- The reason for subtracting one: `H+1` is bounded by the real manuscript
radius with no extra asymptotic loss. -/
theorem manuscriptPowerIntegerRadius_add_one_le
    {Y : ℕ} {eta radiusFraction : ℝ}
    (hnonneg :
      0 ≤ radiusFraction * manuscriptPowerRadiusScale Y eta)
    (hlarge :
      1 ≤ ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊) :
    ((manuscriptPowerIntegerRadius Y eta radiusFraction : ℕ) : ℝ) + 1 ≤
      radiusFraction * manuscriptPowerRadiusScale Y eta := by
  have hfloor :
      (((⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊ : ℕ) : ℝ) ≤
        radiusFraction * manuscriptPowerRadiusScale Y eta) :=
    Nat.floor_le hnonneg
  have hadd :
      manuscriptPowerIntegerRadius Y eta radiusFraction + 1 =
        ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊ := by
    dsimp [manuscriptPowerIntegerRadius]
    exact Nat.sub_add_cancel hlarge
  rw [← Nat.cast_one, ← Nat.cast_add, hadd]
  exact hfloor

/-- The concrete radius product is nonnegative whenever the radius fraction is
nonnegative and the logarithmic scale is positive. -/
theorem manuscriptPowerRadiusProduct_nonneg
    {Y : ℕ} {eta radiusFraction : ℝ}
    (hradius : 0 ≤ radiusFraction)
    (hlog : 0 < Real.log (Y : ℝ)) :
    0 ≤ radiusFraction * manuscriptPowerRadiusScale Y eta := by
  apply mul_nonneg hradius
  exact manuscriptRadiusScale_nonneg
    (manuscriptPowerMainScale_nonneg Y eta) hlog

/-- Literal power-scale data with the integer radius fixed definitionally.

Compared with `IntegerExceptionalPowerScaleData`, there is no free natural
radius and no `radiusBound` field.  The single floor-largeness condition is the
exact discrete condition needed to make the chosen radius nonzero and to absorb
the manuscript's `(H+1)` term. -/
structure IntegerExceptionalIntegerRadiusData
    (bad : Finset ℕ) (Y : ℕ)
    (A M : ℝ → ℝ) (delta eta : ℝ) where
  delta_nonneg : 0 ≤ delta
  eta_le_one : eta ≤ 1
  Y_pos : 1 ≤ Y
  log_large : 1 ≤ Real.log (Y : ℝ)
  radiusFraction : ℝ
  radiusFraction_nonneg : 0 ≤ radiusFraction
  radiusFloorLarge :
    2 ≤ ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊
  statisticCoeff : ℝ
  statisticCoeff_nonneg : 0 ≤ statisticCoeff
  mainCoeff : ℝ
  mainCoeff_nonneg : 0 ≤ mainCoeff
  statisticCoeff_small : statisticCoeff * radiusFraction ≤ delta / 8
  mainCoeff_small : mainCoeff * radiusFraction ≤ delta / 8
  main_nonneg : ∀ n ∈ bad, 0 ≤ M (n : ℝ)
  main_lower : ∀ n ∈ bad, manuscriptPowerMainScale Y eta ≤ M (n : ℝ)
  badAtCentre : ∀ n ∈ bad, RealRelativeBad A M delta (n : ℝ)
  statisticShiftRaw : ∀ n ∈ bad,
    ∀ u ∈ integerThickeningInterval n
      (manuscriptPowerIntegerRadius Y eta radiusFraction),
      |A (n : ℝ) - A u| ≤
        statisticCoeff *
          ((((manuscriptPowerIntegerRadius Y eta radiusFraction : ℕ) : ℝ) + 1) *
            Real.log (Y : ℝ))
  mainShiftRaw : ∀ n ∈ bad,
    ∀ u ∈ integerThickeningInterval n
      (manuscriptPowerIntegerRadius Y eta radiusFraction),
      |M (n : ℝ) - M u| ≤
        mainCoeff *
          (((manuscriptPowerIntegerRadius Y eta radiusFraction : ℕ) : ℝ) *
            manuscriptPowerVariationScale Y eta)
  localScale : ∀ n ∈ bad,
    ∀ u ∈ integerThickeningInterval n
      (manuscriptPowerIntegerRadius Y eta radiusFraction),
      M u ≤ (3 / 2 : ℝ) * M (n : ℝ)

/-- The concrete integer-radius package specializes the preceding literal
power-scale interface. -/
def IntegerExceptionalIntegerRadiusData.toPowerScaleData
    {bad : Finset ℕ} {Y : ℕ}
    {A M : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalIntegerRadiusData bad Y A M delta eta) :
    IntegerExceptionalPowerScaleData bad
      (manuscriptPowerIntegerRadius Y eta data.radiusFraction)
      Y A M delta eta where
  delta_nonneg := data.delta_nonneg
  eta_le_one := data.eta_le_one
  Y_pos := data.Y_pos
  log_large := data.log_large
  radiusFraction := data.radiusFraction
  radiusFraction_nonneg := data.radiusFraction_nonneg
  statisticCoeff := data.statisticCoeff
  statisticCoeff_nonneg := data.statisticCoeff_nonneg
  mainCoeff := data.mainCoeff
  mainCoeff_nonneg := data.mainCoeff_nonneg
  radiusBound := manuscriptPowerIntegerRadius_add_one_le
    (manuscriptPowerRadiusProduct_nonneg data.radiusFraction_nonneg
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) data.log_large))
    (le_trans (by omega : 1 ≤ 2) data.radiusFloorLarge)
  statisticCoeff_small := data.statisticCoeff_small
  mainCoeff_small := data.mainCoeff_small
  main_nonneg := data.main_nonneg
  main_lower := data.main_lower
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw
  localScale := data.localScale

/-- One-scale Lemma 6.1 transfer with the manuscript's integer radius fixed
rather than supplied by the caller. -/
noncomputable def fixedErrorRealThickeningCertificate_of_integerRadius
    {bad : Finset ℕ} {Y k : ℕ}
    {A M : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalIntegerRadiusData bad Y A M delta eta)
    (exceptionalFinite :
      MeasureTheory.volume {u : ℝ | RealRelativeBad A M (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A M (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_powerScale
    data.toPowerScaleData
    (manuscriptPowerIntegerRadius_pos data.radiusFloorLarge)
    exceptionalFinite exceptionalMassSmall

/-- Family-level interface with the radius fraction explicit but the integer
radius fixed by the manuscript rounding rule. -/
def FixedPrecisionIntegerRadiusShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radiusFraction : ℕ → ℕ → ℝ)
    (A M : ℕ → ℕ → ℝ → ℝ)
    (delta eta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    ∃ data : IntegerExceptionalIntegerRadiusData
        bad Y (A k Y) (M k Y) (delta k) (eta k),
      radiusFraction k Y = data.radiusFraction ∧
      MeasureTheory.volume
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} ≠ ∞ ∧
      MeasureTheory.volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- Concrete-radius families specialize the preceding power-scale family. -/
theorem fixedPrecisionPowerScaleShiftLebesgueBounds_of_integerRadius
    {E : ℕ → ℕ → Finset ℕ}
    {radiusFraction : ℕ → ℕ → ℝ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionIntegerRadiusShiftLebesgueBounds
      E radiusFraction A M delta eta threshold) :
    FixedPrecisionPowerScaleShiftLebesgueBounds E
      (fun k Y => manuscriptPowerIntegerRadius Y (eta k) (radiusFraction k Y))
      A M delta eta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionIntegerRadiusShiftLebesgueBounds] at h
  rcases h k hk Y hY with ⟨data, hradius, hfinite, hmass⟩
  refine ⟨?_, ?_, hfinite, hmass⟩
  · simpa [hradius] using data.toPowerScaleData
  · simpa [hradius] using
      (manuscriptPowerIntegerRadius_pos data.radiusFloorLarge)

/-- **Lemma 6.1 concrete integer-radius global-window chain.**

After the raw local estimates and external exceptional-set mass input are
instantiated for the actual rounded radius, every remaining project-owned step
from one-radius normalization through the single global sparse exceptional set
is discharged. -/
theorem eventuallySparseGlobalDyadicWindows_of_integerRadiusShiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radiusFraction : ℕ → ℕ → ℝ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionIntegerRadiusShiftLebesgueBounds
      E radiusFraction A M delta eta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_powerScaleShiftLebesgue hsupp
    (fixedPrecisionPowerScaleShiftLebesgueBounds_of_integerRadius h)

end DivisorF
