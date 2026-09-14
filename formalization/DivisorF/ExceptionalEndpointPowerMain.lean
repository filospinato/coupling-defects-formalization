import DivisorF.ExceptionalEndpointIntegerRadius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal `x^eta` main-term geometry for Lemma 6.1

The integer-radius layer still accepted three pieces of elementary information
about the manuscript main term `M(x)=x^eta`: nonnegativity, the lower comparison
`Y^eta <= n^eta` for a bad centre `n in [Y,2Y)`, and the local comparison
`u^eta <= (3/2)n^eta` throughout the thickening interval.

These are project-owned bookkeeping, not analytic input.  This module discharges
all three from the literal dyadic support and the elementary radius condition
`2H <= Y`.  The genuine upstream inputs are thereby narrowed to the raw
von-Mangoldt shift estimate and the elementary quantitative power-difference
majorant itself.
-/

namespace DivisorF

open scoped ENNReal

/-- A point in the radius-`H` thickening of a centre `n >= Y` stays nonnegative
when `2H <= Y`. -/
theorem integerThickeningInterval_nonneg_of_two_mul_radius_le
    {n H Y : ℕ} {u : ℝ}
    (hY : Y ≤ n) (hH : 2 * H ≤ Y)
    (hu : u ∈ integerThickeningInterval n H) :
    0 ≤ u := by
  have hmem := Set.mem_Icc.mp hu
  have hYreal : (Y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hY
  have hHreal : 2 * (H : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hH
  linarith

/-- The dyadic lower endpoint gives the manuscript main-scale lower bound at
every bad integer centre. -/
theorem manuscriptPowerMainScale_le_center
    {Y n : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta) (hn : Y ≤ n) :
    manuscriptPowerMainScale Y eta ≤ (n : ℝ) ^ eta := by
  have hcast : (Y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact Real.rpow_le_rpow (by positivity) hcast heta

/-- If the thickening radius is at most half the dyadic scale, then the literal
main term varies by at most the harmless multiplicative factor `3/2` required
by the shift-stability layer.

This is deliberately a coarse bound: the manuscript only needs local
comparability of the main scale here; the sharper additive power-variation
estimate is handled separately. -/
theorem manuscriptPowerMain_localScale
    {n H Y : ℕ} {u eta : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hn : Y ≤ n) (hH : 2 * H ≤ Y)
    (hu : u ∈ integerThickeningInterval n H) :
    u ^ eta ≤ (3 / 2 : ℝ) * (n : ℝ) ^ eta := by
  have hu0 : 0 ≤ u :=
    integerThickeningInterval_nonneg_of_two_mul_radius_le hn hH hu
  have hmem := Set.mem_Icc.mp hu
  have hnreal : (Y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hHreal : 2 * (H : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hH
  have huupper : u ≤ (3 / 2 : ℝ) * (n : ℝ) := by
    linarith
  have hpow :
      u ^ eta ≤ ((3 / 2 : ℝ) * (n : ℝ)) ^ eta :=
    Real.rpow_le_rpow hu0 huupper heta0
  have hfactor : (3 / 2 : ℝ) ^ eta ≤ (3 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ (3 / 2 : ℝ) by norm_num) heta1
    simpa using h
  calc
    u ^ eta ≤ ((3 / 2 : ℝ) * (n : ℝ)) ^ eta := hpow
    _ = (3 / 2 : ℝ) ^ eta * (n : ℝ) ^ eta := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    _ ≤ (3 / 2 : ℝ) * (n : ℝ) ^ eta :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by positivity) eta)

/-- Literal integer-radius data specialized to the actual manuscript main term
`M(x)=x^eta`.

Compared with `IntegerExceptionalIntegerRadiusData`, the caller no longer
supplies `main_nonneg`, `main_lower`, or `localScale`.  They follow from the
support condition `Y <= n` and the concrete half-scale radius bound. -/
structure IntegerExceptionalIntegerRadiusPowerMainData
    (bad : Finset ℕ) (Y : ℕ)
    (A : ℝ → ℝ) (delta eta : ℝ) where
  delta_nonneg : 0 ≤ delta
  eta_nonneg : 0 ≤ eta
  eta_le_one : eta ≤ 1
  Y_pos : 1 ≤ Y
  log_large : 1 ≤ Real.log (Y : ℝ)
  radiusFraction : ℝ
  radiusFraction_nonneg : 0 ≤ radiusFraction
  radiusFloorLarge :
    2 ≤ ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊
  radiusHalfScale :
    2 * manuscriptPowerIntegerRadius Y eta radiusFraction ≤ Y
  support_lower : ∀ n ∈ bad, Y ≤ n
  statisticCoeff : ℝ
  statisticCoeff_nonneg : 0 ≤ statisticCoeff
  mainCoeff : ℝ
  mainCoeff_nonneg : 0 ≤ mainCoeff
  statisticCoeff_small : statisticCoeff * radiusFraction ≤ delta / 8
  mainCoeff_small : mainCoeff * radiusFraction ≤ delta / 8
  badAtCentre : ∀ n ∈ bad,
    RealRelativeBad A (fun x => x ^ eta) delta (n : ℝ)
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
      |(n : ℝ) ^ eta - u ^ eta| ≤
        mainCoeff *
          (((manuscriptPowerIntegerRadius Y eta radiusFraction : ℕ) : ℝ) *
            manuscriptPowerVariationScale Y eta)

/-- The specialized power-main package supplies all elementary main-term fields
of the existing integer-radius transfer. -/
def IntegerExceptionalIntegerRadiusPowerMainData.toIntegerRadiusData
    {bad : Finset ℕ} {Y : ℕ}
    {A : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalIntegerRadiusPowerMainData bad Y A delta eta) :
    IntegerExceptionalIntegerRadiusData bad Y A (fun x => x ^ eta) delta eta where
  delta_nonneg := data.delta_nonneg
  eta_le_one := data.eta_le_one
  Y_pos := data.Y_pos
  log_large := data.log_large
  radiusFraction := data.radiusFraction
  radiusFraction_nonneg := data.radiusFraction_nonneg
  radiusFloorLarge := data.radiusFloorLarge
  statisticCoeff := data.statisticCoeff
  statisticCoeff_nonneg := data.statisticCoeff_nonneg
  mainCoeff := data.mainCoeff
  mainCoeff_nonneg := data.mainCoeff_nonneg
  statisticCoeff_small := data.statisticCoeff_small
  mainCoeff_small := data.mainCoeff_small
  main_nonneg := by
    intro n hn
    exact Real.rpow_nonneg (by positivity) eta
  main_lower := by
    intro n hn
    exact manuscriptPowerMainScale_le_center data.eta_nonneg (data.support_lower n hn)
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw
  localScale := by
    intro n hn u hu
    exact manuscriptPowerMain_localScale data.eta_nonneg data.eta_le_one
      (data.support_lower n hn) data.radiusHalfScale hu

/-- One-scale fixed-error thickening certificate with the literal power main
term and all of its coarse geometry discharged. -/
noncomputable def fixedErrorRealThickeningCertificate_of_integerRadius_powerMain
    {bad : Finset ℕ} {Y k : ℕ}
    {A : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalIntegerRadiusPowerMainData bad Y A delta eta)
    (exceptionalFinite :
      MeasureTheory.volume
        {u : ℝ | RealRelativeBad A (fun x => x ^ eta) (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A (fun x => x ^ eta) (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_integerRadius
    data.toIntegerRadiusData exceptionalFinite exceptionalMassSmall

/-- Fixed-precision family interface after specializing the main term to the
literal power `x^eta`.  In particular, the family no longer carries separate
coarse main-term nonnegativity/lower/local-comparability hypotheses. -/
def FixedPrecisionIntegerRadiusPowerMainShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radiusFraction : ℕ → ℕ → ℝ)
    (A : ℕ → ℕ → ℝ → ℝ)
    (delta eta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    ∃ data : IntegerExceptionalIntegerRadiusPowerMainData
        bad Y (A k Y) (delta k) (eta k),
      radiusFraction k Y = data.radiusFraction ∧
      MeasureTheory.volume
          {u : ℝ |
            RealRelativeBad (A k Y) (fun x => x ^ eta k) (delta k / 2) u} ≠ ∞ ∧
      MeasureTheory.volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (fun x => x ^ eta k) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- Literal power-main families specialize the concrete integer-radius family
consumed by the previously formalized global exceptional-set chain. -/
theorem fixedPrecisionIntegerRadiusShiftLebesgueBounds_of_powerMain
    {E : ℕ → ℕ → Finset ℕ}
    {radiusFraction : ℕ → ℕ → ℝ}
    {A : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionIntegerRadiusPowerMainShiftLebesgueBounds
      E radiusFraction A delta eta threshold) :
    FixedPrecisionIntegerRadiusShiftLebesgueBounds E radiusFraction A
      (fun k _Y x => x ^ eta k) delta eta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionIntegerRadiusPowerMainShiftLebesgueBounds] at h
  rcases h k hk Y hY with ⟨data, hradius, hfinite, hmass⟩
  exact ⟨data.toIntegerRadiusData, hradius, hfinite, hmass⟩

/-- **Lemma 6.1 literal-power global-window chain.**

Once the two raw local shift majorants and the external small exceptional-set
mass are supplied, the main-term positivity, dyadic lower scale, local
comparability, radius normalization, Lebesgue overlap, diagonalisation and
single-global-set bookkeeping are all discharged by the project formalization. -/
theorem eventuallySparseGlobalDyadicWindows_of_integerRadius_powerMain
    {E : ℕ → ℕ → Finset ℕ}
    {radiusFraction : ℕ → ℕ → ℝ}
    {A : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionIntegerRadiusPowerMainShiftLebesgueBounds
      E radiusFraction A delta eta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_integerRadiusShiftLebesgue hsupp
    (fixedPrecisionIntegerRadiusShiftLebesgueBounds_of_powerMain h)

end DivisorF
