import DivisorF.ConcreteTranslatedEndpointScalar
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Power bounds for the translated regular-endpoint cone

The Section 6 translated-endpoint construction ultimately takes the simultaneous
type cutoff to be `floor(X^rho)`.  The finite endpoint machinery has already
reduced quotient placement to

`(K+1) * ceil(3 X^eta + 1) <= X+1`.

This module discharges that inequality from the strict exponent relation
`rho + eta < 1`.  It is project-owned bookkeeping; no prime-distribution input
appears here.
-/

namespace DivisorF

/-- The manuscript's canonical integer type cutoff `floor(X^rho)`. -/
noncomputable def regularEndpointPowerCutoff (rho : ℝ) (X : ℕ) : ℕ :=
  ⌊(X : ℝ) ^ rho⌋₊

/-- A concrete support lemma: every nonnegative real power strictly below the
linear exponent is eventually beaten by `X/10`.

The explicit threshold avoids introducing an asymptotic interface into the
finite endpoint arithmetic. -/
theorem eventually_ten_mul_rpow_le_self
    {e : ℝ} (_he0 : 0 ≤ e) (he1 : e < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      10 * (X : ℝ) ^ e ≤ (X : ℝ) := by
  let gap : ℝ := 1 - e
  have hgap : 0 < gap := sub_pos.mpr he1
  let threshold : ℝ := (10 : ℝ) ^ ((1 : ℝ) / gap)
  let X₀ : ℕ := max 1 ⌈threshold⌉₊
  refine ⟨X₀, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hceilX : ⌈threshold⌉₊ ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hceilCast : (⌈threshold⌉₊ : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hceilX
  have hthresholdX : threshold ≤ (X : ℝ) :=
    (Nat.le_ceil threshold).trans hceilCast
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hX1)
  have hthresholdNonneg : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hten_le_gap : (10 : ℝ) ≤ (X : ℝ) ^ gap := by
    have hmono := Real.rpow_le_rpow hthresholdNonneg hthresholdX (le_of_lt hgap)
    calc
      (10 : ℝ) = threshold ^ gap := by
        dsimp [threshold]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10), one_div,
          inv_mul_cancel₀ hgap.ne', Real.rpow_one]
      _ ≤ (X : ℝ) ^ gap := hmono
  calc
    10 * (X : ℝ) ^ e ≤ (X : ℝ) ^ gap * (X : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right hten_le_gap (Real.rpow_nonneg (by positivity) _)
    _ = (X : ℝ) ^ (gap + e) := (Real.rpow_add hXpos gap e).symm
    _ = (X : ℝ) := by
      have hsum : gap + e = 1 := by
        dsimp [gap]
        ring
      rw [hsum, Real.rpow_one]

/-- For positive exponent, the canonical floor cutoff is bounded by `X^rho`
and is at least one once `X>=1`. -/
theorem regularEndpointPowerCutoff_bounds
    {rho : ℝ} {X : ℕ} (hrho : 0 < rho) (hX : 1 ≤ X) :
    (regularEndpointPowerCutoff rho X : ℝ) ≤ (X : ℝ) ^ rho ∧
      1 ≤ regularEndpointPowerCutoff rho X := by
  have hXreal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hpowNonneg : 0 ≤ (X : ℝ) ^ rho := Real.rpow_nonneg (by positivity) _
  have hpowOne : (1 : ℝ) ≤ (X : ℝ) ^ rho := by
    simpa using Real.one_le_rpow hXreal (le_of_lt hrho)
  constructor
  · exact Nat.floor_le hpowNonneg
  · have : (1 : ℕ) ≤ ⌊(X : ℝ) ^ rho⌋₊ := by
      rw [Nat.le_floor_iff hpowNonneg]
      norm_num at hpowOne ⊢
      exact hpowOne
    simpa [regularEndpointPowerCutoff] using this

/-- The explicit translated-endpoint radius is at most `5 X^eta` for positive
`eta` and `X>=1`.  The generous constant absorbs both ceiling and floor-unit
errors while keeping the later exponent calculation transparent. -/
theorem concreteTranslatedEndpointRadius_le_five_rpow
    {eta : ℝ} {X : ℕ} (heta : 0 < eta) (hX : 1 ≤ X) :
    (concreteTranslatedEndpointRadius eta X : ℝ) ≤
      5 * (X : ℝ) ^ eta := by
  have hXreal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hpowOne : (1 : ℝ) ≤ (X : ℝ) ^ eta := by
    simpa using Real.one_le_rpow hXreal (le_of_lt heta)
  have hbaseNonneg : 0 ≤ 3 * (X : ℝ) ^ eta + 1 := by positivity
  have hceil :
      (concreteTranslatedEndpointRadius eta X : ℝ) <
        (3 * (X : ℝ) ^ eta + 1) + 1 := by
    simpa [concreteTranslatedEndpointRadius] using
      (Nat.ceil_lt_add_one hbaseNonneg)
  have hrough :
      (concreteTranslatedEndpointRadius eta X : ℝ) ≤
        3 * (X : ℝ) ^ eta + 2 := by linarith
  nlinarith

/-- **Section 6 width comparison from exponent slack.**

If `0<rho`, `0<eta` and `rho+eta<1`, then the canonical simultaneous type
cutoff and the concrete translated radius satisfy the exact finite quotient
placement inequality eventually. -/
theorem eventually_concreteTranslatedEndpoint_width_of_exponent_slack
    {rho eta : ℝ}
    (hrho : 0 < rho) (heta : 0 < eta) (hsum : rho + eta < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (regularEndpointPowerCutoff rho X + 1) *
          concreteTranslatedEndpointRadius eta X ≤ X + 1 := by
  have he0 : 0 ≤ rho + eta := by linarith
  rcases eventually_ten_mul_rpow_le_self he0 hsum with ⟨Xpow, hpow⟩
  refine ⟨max Xpow 1, ?_⟩
  intro X hX
  have hXpow : Xpow ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hcut := regularEndpointPowerCutoff_bounds (rho := rho) (X := X) hrho hX1
  have hradius := concreteTranslatedEndpointRadius_le_five_rpow
    (eta := eta) (X := X) heta hX1
  have hpowRhoOne : (1 : ℝ) ≤ (X : ℝ) ^ rho := by
    have hXreal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
    simpa using Real.one_le_rpow hXreal (le_of_lt hrho)
  have hcutSucc :
      ((regularEndpointPowerCutoff rho X : ℝ) + 1) ≤
        2 * (X : ℝ) ^ rho := by
    linarith [hcut.1]
  have hmulReal :
      (((regularEndpointPowerCutoff rho X + 1) *
          concreteTranslatedEndpointRadius eta X : ℕ) : ℝ) ≤
        10 * (X : ℝ) ^ (rho + eta) := by
    push_cast
    calc
      ((regularEndpointPowerCutoff rho X : ℝ) + 1) *
          (concreteTranslatedEndpointRadius eta X : ℝ)
          ≤ (2 * (X : ℝ) ^ rho) * (5 * (X : ℝ) ^ eta) :=
        mul_le_mul hcutSucc hradius (by positivity) (by positivity)
      _ = 10 * (X : ℝ) ^ (rho + eta) := by
        rw [Real.rpow_add (by positivity : (0 : ℝ) < (X : ℝ))]
        ring
  have hreal :
      (((regularEndpointPowerCutoff rho X + 1) *
          concreteTranslatedEndpointRadius eta X : ℕ) : ℝ) ≤ (X : ℝ) :=
    hmulReal.trans (hpow X hXpow)
  have hnat :
      (regularEndpointPowerCutoff rho X + 1) *
          concreteTranslatedEndpointRadius eta X ≤ X := by
    exact_mod_cast hreal
  omega

/-- The width half of `EventuallyConcreteTranslatedEndpointRadiusBounds` is
therefore automatic for the manuscript choice `rho < eta < 1-rho`, since its
right inequality is exactly `rho+eta<1`. -/
theorem eventually_concreteTranslatedEndpoint_width_of_rho_lt_one_sub_eta
    {rho eta : ℝ}
    (hrho : 0 < rho) (heta : 0 < eta) (hetaUpper : eta < 1 - rho) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (regularEndpointPowerCutoff rho X + 1) *
          concreteTranslatedEndpointRadius eta X ≤ X + 1 := by
  apply eventually_concreteTranslatedEndpoint_width_of_exponent_slack hrho heta
  linarith

end DivisorF
