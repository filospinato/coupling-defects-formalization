import DivisorF.RegularEndpointPowerBounds
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Canonical scalar package for Section 6 regular endpoints

The manuscript takes the simultaneous endpoint cutoff to be
`K(X)=floor(X^rho)`, with

`0 < rho < eta < 1-rho`.

The preceding layer discharged the quotient-width inequality from
`rho+eta<1`.  This module discharges the remaining two pieces of
`EventuallyConcreteTranslatedEndpointRadiusBounds`: eventual nonnegativity of
`g_eta(X)=X-3X^eta`, and the square-root-cutoff inequality

`K(X)(X+1) <= floor(X/2)^2`.

Thus the entire finite scalar geometry of the translated endpoint construction
is obtained from the manuscript's strict exponent inequalities alone.
-/

namespace DivisorF

/-- A second explicit support estimate, with enough constant room for the
square-cutoff comparison. -/
theorem eventually_thirtytwo_mul_rpow_le_self
    {e : ℝ} (_he0 : 0 ≤ e) (he1 : e < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      32 * (X : ℝ) ^ e ≤ (X : ℝ) := by
  let gap : ℝ := 1 - e
  have hgap : 0 < gap := sub_pos.mpr he1
  let threshold : ℝ := (32 : ℝ) ^ ((1 : ℝ) / gap)
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
  have hthirtytwo_le_gap : (32 : ℝ) ≤ (X : ℝ) ^ gap := by
    have hmono := Real.rpow_le_rpow hthresholdNonneg hthresholdX (le_of_lt hgap)
    calc
      (32 : ℝ) = threshold ^ gap := by
        dsimp [threshold]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32), one_div,
          inv_mul_cancel₀ hgap.ne', Real.rpow_one]
      _ ≤ (X : ℝ) ^ gap := hmono
  calc
    32 * (X : ℝ) ^ e ≤ (X : ℝ) ^ gap * (X : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right hthirtytwo_le_gap (Real.rpow_nonneg (by positivity) _)
    _ = (X : ℝ) ^ (gap + e) := (Real.rpow_add hXpos gap e).symm
    _ = (X : ℝ) := by
      have hsum : gap + e = 1 := by
        dsimp [gap]
        ring
      rw [hsum, Real.rpow_one]

/-- `g_eta(X)=X-3X^eta` is eventually nonnegative for every `0<=eta<1`.
This is the exact sign condition needed by the natural-floor endpoint map. -/
theorem eventually_translatedEndpointReal_nonneg
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      0 ≤ translatedEndpointReal eta X := by
  rcases eventually_ten_mul_rpow_le_self heta0 heta1 with ⟨X₀, hX₀⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  have hten := hX₀ X hX
  have hpow : 0 ≤ (X : ℝ) ^ eta := Real.rpow_nonneg (by positivity) _
  dsimp [translatedEndpointReal]
  linarith

/-- The canonical cutoff `floor(X^rho)` makes the large-prime square cutoff
inactive eventually whenever `0<rho<1`.  Section 6 uses only the stronger
`rho<1/2`. -/
theorem eventually_regularEndpointPowerCutoff_square
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      regularEndpointPowerCutoff rho X * (X + 1) ≤
        (X / 2) * (X / 2) := by
  rcases eventually_thirtytwo_mul_rpow_le_self
      (le_of_lt hrho) hrho1 with ⟨Xpow, hpow⟩
  refine ⟨max Xpow 2, ?_⟩
  intro X hX
  have hXpow : Xpow ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hX2 : 2 ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hX1 : 1 ≤ X := by omega
  have hcut := regularEndpointPowerCutoff_bounds
    (rho := rho) (X := X) hrho hX1
  have h32pow := hpow X hXpow
  have h32cut :
      32 * (regularEndpointPowerCutoff rho X : ℝ) ≤ (X : ℝ) := by
    calc
      32 * (regularEndpointPowerCutoff rho X : ℝ)
          ≤ 32 * (X : ℝ) ^ rho :=
        mul_le_mul_of_nonneg_left hcut.1 (by norm_num)
      _ ≤ (X : ℝ) := h32pow
  have hcutDiv :
      (regularEndpointPowerCutoff rho X : ℝ) ≤ (X : ℝ) / 32 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    simpa [mul_comm] using h32cut
  have hsuccNat : X + 1 ≤ 2 * X := by omega
  have hsucc : ((X + 1 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    exact_mod_cast hsuccNat
  have hleft :
      ((regularEndpointPowerCutoff rho X : ℝ) * ((X + 1 : ℕ) : ℝ)) ≤
        (X : ℝ) * (X : ℝ) / 16 := by
    calc
      (regularEndpointPowerCutoff rho X : ℝ) * ((X + 1 : ℕ) : ℝ)
          ≤ ((X : ℝ) / 32) * (2 * (X : ℝ)) :=
        mul_le_mul hcutDiv hsucc (by positivity) (by positivity)
      _ = (X : ℝ) * (X : ℝ) / 16 := by ring
  have hhalfNat : X ≤ 4 * (X / 2) := by omega
  have hhalf : (X : ℝ) ≤ 4 * ((X / 2 : ℕ) : ℝ) := by
    exact_mod_cast hhalfNat
  have hdiff : 0 ≤ 4 * ((X / 2 : ℕ) : ℝ) - (X : ℝ) := sub_nonneg.mpr hhalf
  have hsum : 0 ≤ 4 * ((X / 2 : ℕ) : ℝ) + (X : ℝ) := by positivity
  have hprod :
      0 ≤ (4 * ((X / 2 : ℕ) : ℝ) - (X : ℝ)) *
        (4 * ((X / 2 : ℕ) : ℝ) + (X : ℝ)) :=
    mul_nonneg hdiff hsum
  have hright :
      (X : ℝ) * (X : ℝ) / 16 ≤
        ((X / 2 : ℕ) : ℝ) * ((X / 2 : ℕ) : ℝ) := by
    nlinarith
  have hreal :
      ((regularEndpointPowerCutoff rho X : ℝ) * ((X + 1 : ℕ) : ℝ)) ≤
        ((X / 2 : ℕ) : ℝ) * ((X / 2 : ℕ) : ℝ) :=
    hleft.trans hright
  exact_mod_cast hreal

/-- **Canonical Section 6 scalar package.**

For the manuscript exponents `0<rho<eta<1-rho`, all three finite scalar
requirements of the true translated endpoint are automatic eventually:
nonnegativity of `g_eta`, quotient placement, and inactivity of the square-root
large-prime cutoff. -/
theorem eventuallyConcreteTranslatedEndpointRadiusBounds_powerCutoff
    {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho) :
    EventuallyConcreteTranslatedEndpointRadiusBounds eta
      (regularEndpointPowerCutoff rho) := by
  have heta : 0 < eta := lt_trans hrho hrhoEta
  have heta1 : eta < 1 := by linarith
  have hrho1 : rho < 1 := by linarith
  rcases eventually_translatedEndpointReal_nonneg
      (le_of_lt heta) heta1 with ⟨Xnonneg, hnonneg⟩
  rcases eventually_concreteTranslatedEndpoint_width_of_rho_lt_one_sub_eta
      hrho heta hetaUpper with ⟨Xwidth, hwidth⟩
  rcases eventually_regularEndpointPowerCutoff_square hrho hrho1 with
    ⟨Xsquare, hsquare⟩
  refine ⟨max Xnonneg (max Xwidth Xsquare), ?_⟩
  intro X hX
  have hN : Xnonneg ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hWS : max Xwidth Xsquare ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hW : Xwidth ≤ X := le_trans (Nat.le_max_left _ _) hWS
  have hS : Xsquare ≤ X := le_trans (Nat.le_max_right _ _) hWS
  exact ⟨hnonneg X hN, hwidth X hW, hsquare X hS⟩

/-- The concrete translated-endpoint data therefore needs no independent scalar
hypothesis once the canonical power cutoff is chosen.  Only prime richness of
the actual packet remains as the analytic input at this stage. -/
theorem eventuallyConcreteTranslatedEndpointData_powerCutoff
    {rho eta : ℝ} {E : ℕ → Finset ℕ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho)
    (hprime :
      EventuallyConcreteTranslatedEndpointPrimeRich eta
        (regularEndpointPowerCutoff rho) E) :
    EventuallyConcreteTranslatedEndpointData eta
      (regularEndpointPowerCutoff rho) E := by
  exact eventuallyConcreteTranslatedEndpointData_of_radiusBounds
    (eventuallyConcreteTranslatedEndpointRadiusBounds_powerCutoff
      hrho hrhoEta hetaUpper)
    hprime

end DivisorF
