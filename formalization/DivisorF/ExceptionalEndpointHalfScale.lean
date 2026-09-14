import DivisorF.ExceptionalEndpointPowerMain
import DivisorF.RegularEndpointPowerBounds
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Automatic half-scale control for the Lemma 6.1 radius

The literal power-main layer still asks for the coarse geometric condition

`2 * H <= Y`

in order to keep the whole integer-centred thickening interval inside the
positive, dyadically comparable range.  For the manuscript radius

`H = floor(c_delta * Y^eta / log Y) - 1`

this condition is not an analytic input.  It follows eventually from
`eta < 1`, `c_delta <= 1`, and `log Y >= 1`.

This module discharges that project-owned asymptotic bookkeeping.  The only
prime-distribution input in the downstream Lemma 6.1 chain remains the raw
short-interval statistic estimate and the smallness of the real exceptional
set.
-/

namespace DivisorF

open scoped ENNReal

/-- The concrete integer manuscript radius is bounded by `Y^eta` once the
radius fraction is at most one and `log Y >= 1`.

No floor-largeness assumption is needed: even when the natural floor is zero or
one, the truncated subtraction in the definition of the radius only makes the
left-hand side smaller. -/
theorem manuscriptPowerIntegerRadius_le_mainScale
    {Y : ℕ} {eta radiusFraction : ℝ}
    (hradius0 : 0 ≤ radiusFraction) (hradius1 : radiusFraction ≤ 1)
    (hlog : 1 ≤ Real.log (Y : ℝ)) :
    (manuscriptPowerIntegerRadius Y eta radiusFraction : ℝ) ≤
      manuscriptPowerMainScale Y eta := by
  have hlogPos : 0 < Real.log (Y : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hlog
  have hmain0 : 0 ≤ manuscriptPowerMainScale Y eta :=
    manuscriptPowerMainScale_nonneg Y eta
  have hscale0 : 0 ≤ manuscriptPowerRadiusScale Y eta :=
    manuscriptRadiusScale_nonneg hmain0 hlogPos
  have hproduct0 :
      0 ≤ radiusFraction * manuscriptPowerRadiusScale Y eta :=
    mul_nonneg hradius0 hscale0
  have hHfloor :
      manuscriptPowerIntegerRadius Y eta radiusFraction ≤
        ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊ := by
    dsimp [manuscriptPowerIntegerRadius]
    omega
  have hHfloorReal :
      (manuscriptPowerIntegerRadius Y eta radiusFraction : ℝ) ≤
        (⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊ : ℝ) := by
    exact_mod_cast hHfloor
  have hfloor :
      (⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊ : ℝ) ≤
        radiusFraction * manuscriptPowerRadiusScale Y eta :=
    Nat.floor_le hproduct0
  have hfrac :
      radiusFraction * manuscriptPowerRadiusScale Y eta ≤
        manuscriptPowerRadiusScale Y eta := by
    nlinarith
  have hscale :
      manuscriptPowerRadiusScale Y eta ≤ manuscriptPowerMainScale Y eta := by
    dsimp [manuscriptPowerRadiusScale, manuscriptRadiusScale]
    rw [div_le_iff₀ hlogPos]
    nlinarith
  exact hHfloorReal.trans (hfloor.trans (hfrac.trans hscale))

/-- A single explicit power domination inequality implies the exact natural
half-scale condition needed by the literal power-main geometry. -/
theorem manuscriptPowerIntegerRadius_two_mul_le_of_ten_mul_rpow_le_self
    {Y : ℕ} {eta radiusFraction : ℝ}
    (hradius0 : 0 ≤ radiusFraction) (hradius1 : radiusFraction ≤ 1)
    (hlog : 1 ≤ Real.log (Y : ℝ))
    (hpow : 10 * (Y : ℝ) ^ eta ≤ (Y : ℝ)) :
    2 * manuscriptPowerIntegerRadius Y eta radiusFraction ≤ Y := by
  have hH :
      (manuscriptPowerIntegerRadius Y eta radiusFraction : ℝ) ≤
        manuscriptPowerMainScale Y eta :=
    manuscriptPowerIntegerRadius_le_mainScale hradius0 hradius1 hlog
  have hreal :
      ((2 * manuscriptPowerIntegerRadius Y eta radiusFraction : ℕ) : ℝ) ≤
        (Y : ℝ) := by
    push_cast
    dsimp [manuscriptPowerMainScale] at hH
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (Y : ℝ) by positivity) eta]
  exact_mod_cast hreal

/-- **Automatic half-scale radius.**  For every fixed `0 <= eta < 1` and every
fixed manuscript radius fraction `0 <= c_delta <= 1`, the concrete integer
radius satisfies `2H <= Y` for all sufficiently large dyadic scales for which
`log Y >= 1`.

The proof reuses the generic sublinear-power domination already needed by the
translated-endpoint arithmetic, rather than introducing a second asymptotic
framework. -/
theorem eventually_manuscriptPowerIntegerRadius_two_mul_le
    {eta radiusFraction : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hradius0 : 0 ≤ radiusFraction) (hradius1 : radiusFraction ≤ 1) :
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      1 ≤ Real.log (Y : ℝ) →
      2 * manuscriptPowerIntegerRadius Y eta radiusFraction ≤ Y := by
  rcases eventually_ten_mul_rpow_le_self heta0 heta1 with ⟨Y₀, hpow⟩
  refine ⟨Y₀, ?_⟩
  intro Y hY hlog
  exact manuscriptPowerIntegerRadius_two_mul_le_of_ten_mul_rpow_le_self
    hradius0 hradius1 hlog (hpow Y hY)

/-- Power-main data in which the half-scale condition is replaced by the
strict manuscript exponent inequality and the harmless normalization
`c_delta <= 1`, together with the one-scale power-domination fact generated
by the preceding eventual theorem.

This is the useful finite package for the downstream thickening theorem: the
caller no longer has to formulate the geometric condition `2H <= Y` itself. -/
structure IntegerExceptionalAutomaticHalfScalePowerMainData
    (bad : Finset ℕ) (Y : ℕ)
    (A : ℝ → ℝ) (delta eta : ℝ) where
  delta_nonneg : 0 ≤ delta
  eta_nonneg : 0 ≤ eta
  eta_lt_one : eta < 1
  Y_pos : 1 ≤ Y
  log_large : 1 ≤ Real.log (Y : ℝ)
  radiusFraction : ℝ
  radiusFraction_nonneg : 0 ≤ radiusFraction
  radiusFraction_le_one : radiusFraction ≤ 1
  radiusFloorLarge :
    2 ≤ ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊
  powerDominated : 10 * (Y : ℝ) ^ eta ≤ (Y : ℝ)
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

/-- The automatic-half-scale package specializes the existing literal
power-main package. -/
def IntegerExceptionalAutomaticHalfScalePowerMainData.toPowerMainData
    {bad : Finset ℕ} {Y : ℕ}
    {A : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalAutomaticHalfScalePowerMainData bad Y A delta eta) :
    IntegerExceptionalIntegerRadiusPowerMainData bad Y A delta eta where
  delta_nonneg := data.delta_nonneg
  eta_nonneg := data.eta_nonneg
  eta_le_one := le_of_lt data.eta_lt_one
  Y_pos := data.Y_pos
  log_large := data.log_large
  radiusFraction := data.radiusFraction
  radiusFraction_nonneg := data.radiusFraction_nonneg
  radiusFloorLarge := data.radiusFloorLarge
  radiusHalfScale :=
    manuscriptPowerIntegerRadius_two_mul_le_of_ten_mul_rpow_le_self
      data.radiusFraction_nonneg data.radiusFraction_le_one data.log_large
      data.powerDominated
  support_lower := data.support_lower
  statisticCoeff := data.statisticCoeff
  statisticCoeff_nonneg := data.statisticCoeff_nonneg
  mainCoeff := data.mainCoeff
  mainCoeff_nonneg := data.mainCoeff_nonneg
  statisticCoeff_small := data.statisticCoeff_small
  mainCoeff_small := data.mainCoeff_small
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw

/-- One-scale Lemma 6.1 transfer with the half-scale geometry discharged from
the actual manuscript radius and sublinear exponent domination. -/
noncomputable def fixedErrorRealThickeningCertificate_of_automaticHalfScale_powerMain
    {bad : Finset ℕ} {Y k : ℕ}
    {A : ℝ → ℝ} {delta eta : ℝ}
    (data : IntegerExceptionalAutomaticHalfScalePowerMainData bad Y A delta eta)
    (exceptionalFinite :
      MeasureTheory.volume
        {u : ℝ | RealRelativeBad A (fun x => x ^ eta) (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A (fun x => x ^ eta) (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_integerRadius_powerMain
    data.toPowerMainData exceptionalFinite exceptionalMassSmall

end DivisorF
