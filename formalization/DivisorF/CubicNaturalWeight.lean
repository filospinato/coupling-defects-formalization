import DivisorF.CubicNaturalMass
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Canonical endpoint-weight comparison for cubic natural density

This module closes the last elementary quantitative step in Corollary 6.4.
The exact natural pair space already has canonical lower mass at cutoff
`floor(Y^delta)`, while the exceptional-endpoint upper count uses the dyadic
cutoff `ceil((2Y)^delta)`.  Since the endpoint weight is the triangular sum
`sum_{2 <= s <= K} s`, a constant-factor comparison of the two cutoffs gives a
constant-factor comparison of their endpoint weights.

For the cubic range `0 < delta < 1/2`, the canonical floor cutoff is eventually
at least two, and `ceil((2Y)^delta) <= 3 floor(Y^delta)`.  Thus all remaining
mass/weight bookkeeping is project-owned and explicit.  No prime-distribution
theorem enters this layer.
-/

namespace DivisorF

/-- Exact doubled triangular formula for the endpoint weight.  We keep the
identity division-free because the surrounding density bookkeeping is also
formulated over natural numbers without division. -/
theorem two_mul_endpointPairWeight_eq
    (K : ℕ) (hK : 2 ≤ K) :
    2 * endpointPairWeight K = K * (K + 1) - 2 := by
  revert hK
  induction K with
  | zero =>
      intro hK
      omega
  | succ K ih =>
      intro hK
      by_cases hprev : 2 ≤ K
      · have hstep :
          endpointPairWeight (K + 1) = endpointPairWeight K + (K + 1) := by
            unfold endpointPairWeight
            rw [Finset.sum_Icc_succ_top (by omega)]
        have hexpand :
            (K + 1) * (K + 1 + 1) = K * (K + 1) + 2 * (K + 1) := by
          ring
        have hbase : 2 * 1 ≤ K * (K + 1) :=
          Nat.mul_le_mul hprev (by omega)
        rw [hstep, Nat.mul_add, ih hprev, hexpand]
        omega
      · have hK1 : K = 1 := by omega
        subst K
        norm_num [endpointPairWeight]

/-- The endpoint weight is at least quadratic up to the harmless factor two. -/
theorem endpointPairWeight_quadratic_lower
    (K : ℕ) (hK : 2 ≤ K) :
    K * K ≤ 2 * endpointPairWeight K := by
  rw [two_mul_endpointPairWeight_eq K hK]
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The doubled endpoint weight is bounded by the corresponding full triangular
numerator. -/
theorem endpointPairWeight_quadratic_upper
    (K : ℕ) (hK : 2 ≤ K) :
    2 * endpointPairWeight K ≤ K * (K + 1) := by
  rw [two_mul_endpointPairWeight_eq K hK]
  exact Nat.sub_le _ _

/-- A constant-factor cutoff comparison gives a quadratic constant-factor
endpoint-weight comparison.  The explicit constant `c(c+1)` is deliberately
coarse; only its independence of `Y` matters for Corollary 6.4. -/
theorem endpointPairWeight_le_mul_of_cutoff_le_mul
    {L U c : ℕ}
    (hL : 2 ≤ L) (_hc : 1 ≤ c) (hcut : U ≤ c * L) :
    endpointPairWeight U ≤ c * (c + 1) * endpointPairWeight L := by
  by_cases hU : 2 ≤ U
  · have hupper := endpointPairWeight_quadratic_upper U hU
    have hlower := endpointPairWeight_quadratic_lower L hL
    have hsecond : U + 1 ≤ (c + 1) * L := by
      calc
        U + 1 ≤ c * L + 1 := Nat.add_le_add_right hcut 1
        _ ≤ c * L + L :=
          Nat.add_le_add_left (le_trans (by decide : 1 ≤ 2) hL) (c * L)
        _ = (c + 1) * L := by simp [Nat.add_mul]
    have hquad : U * (U + 1) ≤ (c * L) * ((c + 1) * L) :=
      Nat.mul_le_mul hcut hsecond
    have hscaled :
        2 * endpointPairWeight U ≤
          2 * (c * (c + 1) * endpointPairWeight L) := by
      calc
        2 * endpointPairWeight U ≤ U * (U + 1) := hupper
        _ ≤ (c * L) * ((c + 1) * L) := hquad
        _ = c * (c + 1) * (L * L) := by ac_rfl
        _ ≤ c * (c + 1) * (2 * endpointPairWeight L) :=
          Nat.mul_le_mul_left (c * (c + 1)) hlower
        _ = 2 * (c * (c + 1) * endpointPairWeight L) := by ac_rfl
    omega
  · have hUle : U ≤ 1 := by omega
    interval_cases U <;> simp [endpointPairWeight]

/-- Eventual constant-factor comparison between the actual dyadic upper cutoff
and the canonical lower-core cutoff. -/
def EventuallyCubicNaturalCutoffComparison
    (gamma : ℝ) (c : ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    2 ≤ cubicNaturalCoreCutoff gamma Y ∧
      cubicNaturalDyadicCutoff gamma Y ≤
        c * cubicNaturalCoreCutoff gamma Y

/-- A positive cubic endpoint exponent makes the canonical floor cutoff
`floor(Y^delta)` eventually at least two.  The threshold is explicit. -/
theorem eventually_two_le_cubicNaturalCoreCutoff
    {gamma : ℝ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      2 ≤ cubicNaturalCoreCutoff gamma Y := by
  let delta := cubicEndpointExponent gamma
  have hdelta : 0 < delta := cubicEndpointExponent_pos hgamma hgammaUpper
  let threshold : ℝ := (2 : ℝ) ^ delta⁻¹
  let Y₀ : ℕ := max 1 ⌈threshold⌉₊
  refine ⟨Y₀, ?_⟩
  intro Y hY
  have hceilY : ⌈threshold⌉₊ ≤ Y :=
    le_trans (Nat.le_max_right _ _) hY
  have hceilCast : (⌈threshold⌉₊ : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast hceilY
  have hthresholdY : threshold ≤ (Y : ℝ) :=
    (Nat.le_ceil threshold).trans hceilCast
  have hthresholdNonneg : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hmono :=
    Real.rpow_le_rpow hthresholdNonneg hthresholdY (le_of_lt hdelta)
  have hthresholdPower : threshold ^ delta = (2 : ℝ) := by
    dsimp [threshold]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hinv : delta⁻¹ * delta = (1 : ℝ) := by
      field_simp [hdelta.ne']
    rw [hinv, Real.rpow_one]
  have htwo : (2 : ℝ) ≤ (Y : ℝ) ^ delta := by
    rw [← hthresholdPower]
    exact hmono
  unfold cubicNaturalCoreCutoff
  dsimp [delta] at htwo
  exact Nat.le_floor htwo

/-- Once the lower floor cutoff is at least two, the dyadic upper cutoff is at
most three times as large.  The factor three absorbs both the dyadic factor
`2^delta <= 2` (here `delta < 1/2`) and the unit floor/ceiling losses. -/
theorem cubicNaturalDyadicCutoff_le_three_mul_coreCutoff
    {gamma : ℝ} {Y : ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hcore : 2 ≤ cubicNaturalCoreCutoff gamma Y) :
    cubicNaturalDyadicCutoff gamma Y ≤
      3 * cubicNaturalCoreCutoff gamma Y := by
  let delta := cubicEndpointExponent gamma
  let L := cubicNaturalCoreCutoff gamma Y
  have hdeltaPos : 0 < delta := cubicEndpointExponent_pos hgamma hgammaUpper
  have hdeltaHalf : delta < (1 : ℝ) / 2 :=
    cubicEndpointExponent_lt_half hgamma hgammaUpper
  have hdeltaOne : delta ≤ 1 := by linarith
  have htwoPow : (2 : ℝ) ^ delta ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) hdeltaOne
  have hYpowNonneg : 0 ≤ (Y : ℝ) ^ delta := Real.rpow_nonneg (by positivity) _
  have hfloorLt : (Y : ℝ) ^ delta < (L : ℝ) + 1 := by
    dsimp [L, cubicNaturalCoreCutoff, delta]
    exact Nat.lt_floor_add_one _
  have hdyadicReal :
      (((2 * Y : ℕ) : ℝ) ^ delta) ≤ (3 * L : ℕ) := by
    have hmul :
        (((2 * Y : ℕ) : ℝ) ^ delta) =
          (2 : ℝ) ^ delta * (Y : ℝ) ^ delta := by
      rw [show (((2 * Y : ℕ) : ℝ)) = (2 : ℝ) * (Y : ℝ) by norm_num]
      exact Real.mul_rpow (by norm_num) (by positivity)
    rw [hmul]
    calc
      (2 : ℝ) ^ delta * (Y : ℝ) ^ delta
          ≤ 2 * (Y : ℝ) ^ delta :=
        mul_le_mul_of_nonneg_right htwoPow hYpowNonneg
      _ ≤ 2 * ((L : ℝ) + 1) := by
        exact le_of_lt (mul_lt_mul_of_pos_left hfloorLt (by norm_num))
      _ ≤ (3 * L : ℕ) := by
        exact_mod_cast (show 2 * (L + 1) ≤ 3 * L by
          dsimp [L] at hcore ⊢
          omega)
  unfold cubicNaturalDyadicCutoff
  dsimp [delta] at hdyadicReal
  calc
    ⌈(((2 * Y : ℕ) : ℝ) ^ cubicEndpointExponent gamma)⌉₊
        ≤ ⌈((3 * L : ℕ) : ℝ)⌉₊ := Nat.ceil_le_ceil hdyadicReal
    _ = 3 * L := Nat.ceil_natCast _
    _ = 3 * cubicNaturalCoreCutoff gamma Y := rfl

/-- The manuscript's two canonical integral cutoffs therefore have a uniform
factor-three comparison. -/
theorem eventuallyCubicNaturalCutoffComparison_three
    {gamma : ℝ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    EventuallyCubicNaturalCutoffComparison gamma 3 := by
  rcases eventually_two_le_cubicNaturalCoreCutoff hgamma hgammaUpper with
    ⟨Y₀, hcore⟩
  refine ⟨Y₀, ?_⟩
  intro Y hY
  have hcoreY := hcore Y hY
  exact ⟨hcoreY,
    cubicNaturalDyadicCutoff_le_three_mul_coreCutoff
      hgamma hgammaUpper hcoreY⟩

/-- The cutoff comparison is exactly what is needed to discharge the abstract
one-endpoint weight bound in `CubicNaturalDensity`. -/
theorem eventuallyCubicNaturalEndpointWeightBound_of_cutoffComparison
    {gamma : ℝ} {c : ℕ}
    (hc : 1 ≤ c)
    (hcut : EventuallyCubicNaturalCutoffComparison gamma c) :
    EventuallyCubicNaturalEndpointWeightBound gamma
      (fun Y => endpointPairWeight (cubicNaturalCoreCutoff gamma Y))
      (c * (c + 1)) := by
  rcases hcut with ⟨Y₀, hcut⟩
  refine ⟨Y₀, ?_⟩
  intro Y hY
  rcases hcut Y hY with ⟨hcore, hcompare⟩
  exact endpointPairWeight_le_mul_of_cutoff_le_mul hcore hc hcompare

/-- At the canonical cubic scale, the one-endpoint upper weight is automatically
bounded by twelve times the lower-core weight. -/
theorem eventuallyCubicNaturalEndpointWeightBound_canonical
    {gamma : ℝ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    EventuallyCubicNaturalEndpointWeightBound gamma
      (fun Y => endpointPairWeight (cubicNaturalCoreCutoff gamma Y)) 12 := by
  simpa using
    (eventuallyCubicNaturalEndpointWeightBound_of_cutoffComparison
      (gamma := gamma) (c := 3) (by norm_num)
      (eventuallyCubicNaturalCutoffComparison_three hgamma hgammaUpper))

/-- Canonical Corollary 6.4 transfer with all combinatorial mass and weight
bookkeeping discharged.  Beyond regularity/sparsity of exceptional endpoints,
only the scalar cutoff comparison remains. -/
theorem cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints_and_cutoffComparison
    {gamma : ℝ} {E : ℕ → Finset ℕ} {c : ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hc : 1 ≤ c)
    (hzero : EventuallyZeroOutsideBadEndpointsNatural gamma E)
    (hsparse : EventuallySparseBadEndpoints E)
    (hcut : EventuallyCubicNaturalCutoffComparison gamma c) :
    CubicNaturalRelativeDensityZero gamma := by
  have hA : 1 ≤ c * (c + 1) := by
    have hcpos : 0 < c := Nat.zero_lt_of_lt hc
    have hcp : 0 < c + 1 := by omega
    exact Nat.mul_pos hcpos hcp
  exact cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints_canonical
    hgamma hgammaUpper hA hzero hsparse
    (eventuallyCubicNaturalEndpointWeightBound_of_cutoffComparison hc hcut)

/-- **Corollary 6.4, project-owned transfer layer.**

For every `0 < gamma < 1/3`, eventual zero defect outside a sparse exceptional
endpoint set implies relative weighted density zero in the exact natural
`N^gamma` pair space.  The source of regularity/sparsity (Gafni--Tao in the
manuscript) remains an explicit external input; all exponent conversion,
quotient-block sandwich, integral cutoffs, weighted mass and exceptional-weight
bookkeeping are discharged inside Lean. -/
theorem cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints_cubicScale
    {gamma : ℝ} {E : ℕ → Finset ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hzero : EventuallyZeroOutsideBadEndpointsNatural gamma E)
    (hsparse : EventuallySparseBadEndpoints E) :
    CubicNaturalRelativeDensityZero gamma := by
  exact cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints_canonical
    hgamma hgammaUpper (by norm_num) hzero hsparse
    (eventuallyCubicNaturalEndpointWeightBound_canonical hgamma hgammaUpper)

end DivisorF
