import DivisorF.TranslatedEndpointElementaryBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Complete paper bounds for the concrete translated endpoint

This module closes the remaining scalar estimate for

`g_eta(X)=X-3X^eta`, `0<eta<1`.

Bernoulli's inequality for real powers gives

`(X+1)^eta-X^eta <= eta X^(eta-1)`.

The explicit tail estimate `10 X^eta <= X` from the previous layer therefore
makes the power increment at most `1/10`, hence the translated increment at
least `7/10`, stronger than the manuscript's required `1/2`.  Combining this
with the already proved elementary upper-step and envelope estimates yields the
full `EventuallyTranslatedEndpointPaperBounds` with no remaining scalar
hypothesis.
-/

namespace DivisorF

/-- Bernoulli plus the explicit sublinear-power tail controls one discrete power
increment. -/
theorem rpow_succ_sub_rpow_le_one_tenth_eventually
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((X + 1 : ℕ) : ℝ) ^ eta - (X : ℝ) ^ eta) ≤ (1 : ℝ) / 10 := by
  rcases eventually_ten_mul_rpow_le_self (le_of_lt heta) heta1 with
    ⟨X₀, hpow⟩
  refine ⟨max X₀ 1, ?_⟩
  intro X hX
  have hX₀ : X₀ ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hX1)
  have hten := hpow X hX₀
  have huNonneg : 0 ≤ (1 : ℝ) / (X : ℝ) := by positivity
  have huLower : -(1 : ℝ) ≤ (1 : ℝ) / (X : ℝ) := by linarith
  have hbern :
      (1 + (1 : ℝ) / (X : ℝ)) ^ eta ≤
        1 + eta * ((1 : ℝ) / (X : ℝ)) :=
    rpow_one_add_le_one_add_mul_self huLower (le_of_lt heta) (le_of_lt heta1)
  have hfactor :
      (((X + 1 : ℕ) : ℝ)) =
        (X : ℝ) * (1 + (1 : ℝ) / (X : ℝ)) := by
    push_cast
    field_simp
  have hsucc :
      (((X + 1 : ℕ) : ℝ) ^ eta) ≤
        (X : ℝ) ^ eta *
          (1 + eta * ((1 : ℝ) / (X : ℝ))) := by
    rw [hfactor, Real.mul_rpow (le_of_lt hXpos) (by positivity)]
    exact mul_le_mul_of_nonneg_left hbern (Real.rpow_nonneg (by positivity) _)
  have hdiff :
      (((X + 1 : ℕ) : ℝ) ^ eta - (X : ℝ) ^ eta) ≤
        eta * ((X : ℝ) ^ eta / (X : ℝ)) := by
    calc
      (((X + 1 : ℕ) : ℝ) ^ eta - (X : ℝ) ^ eta)
          ≤ (X : ℝ) ^ eta *
              (1 + eta * ((1 : ℝ) / (X : ℝ))) -
                (X : ℝ) ^ eta := sub_le_sub_right hsucc _
      _ = eta * ((X : ℝ) ^ eta / (X : ℝ)) := by
        field_simp [hXpos.ne']
        ring
  have hratioNonneg :
      0 ≤ (X : ℝ) ^ eta / (X : ℝ) := by positivity
  have hratio :
      (X : ℝ) ^ eta / (X : ℝ) ≤ (1 : ℝ) / 10 := by
    rw [div_le_iff₀ hXpos]
    nlinarith
  have hetaLe : eta ≤ 1 := le_of_lt heta1
  have hetaratio :
      eta * ((X : ℝ) ^ eta / (X : ℝ)) ≤ (1 : ℝ) / 10 := by
    calc
      eta * ((X : ℝ) ^ eta / (X : ℝ))
          ≤ 1 * ((X : ℝ) ^ eta / (X : ℝ)) :=
        mul_le_mul_of_nonneg_right hetaLe hratioNonneg
      _ = (X : ℝ) ^ eta / (X : ℝ) := one_mul _
      _ ≤ (1 : ℝ) / 10 := hratio
  exact hdiff.trans hetaratio

/-- The manuscript's lower one-step bound follows, with room to spare. -/
theorem eventuallyTranslatedEndpointLowerStep_of_eta
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    EventuallyTranslatedEndpointLowerStep eta := by
  rcases rpow_succ_sub_rpow_le_one_tenth_eventually heta heta1 with
    ⟨X₀, hdiff⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  have hd := hdiff X hX
  dsimp [translatedEndpointReal]
  push_cast at hd ⊢
  linarith

/-- **Complete concrete paper package.**

For every `0<eta<1`, the actual function `X-3X^eta` satisfies all scalar
bounds used in Section 6 eventually. -/
theorem eventuallyTranslatedEndpointPaperBounds_concrete
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    EventuallyTranslatedEndpointPaperBounds eta := by
  exact eventuallyTranslatedEndpointPaperBounds_of_lowerStep
    heta heta1 (eventuallyTranslatedEndpointLowerStep_of_eta heta heta1)

/-- Consequently the concrete translated map has the paper's bounded fibre
multiplicity and dyadic exceptional-set pullback for every `0<eta<1`. -/
theorem eventuallyDyadicallySparse_pulledBack_translatedEndpointMap_concrete
    {eta : ℝ} {target : ℕ → Finset ℕ}
    (heta : 0 < eta) (heta1 : eta < 1)
    (hsparse : EventuallyDyadicallySparse target) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y (translatedEndpointMap eta) (target Y)) := by
  exact eventuallyDyadicallySparse_pulledBack_translatedEndpointMap_of_paperBounds
    hsparse (eventuallyTranslatedEndpointPaperBounds_concrete heta heta1)

/-- End-to-end translated-endpoint weighted-density transfer with the entire
project-owned scalar geometry discharged from `0<rho<eta<1-rho`.  The only
remaining inputs here are prime richness of the concrete packet and the
exceptional-endpoint weight/sparsity data supplied downstream from the
real-to-integer discretisation. -/
theorem weightedRelativeDensityZero_of_concreteTranslatedEndpoint_powerCutoff
    {rho eta : ℝ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho)
    (hprime :
      EventuallyConcreteTranslatedEndpointPrimeRich eta
        (regularEndpointPowerCutoff rho) E)
    (hweight :
      EventuallyEndpointWeightBound (regularEndpointPowerCutoff rho) W)
    (hsmall :
      EventuallyNegligibleBadEndpointBurden
        (regularEndpointPowerCutoff rho) E W) :
    WeightedRelativeDensityZero (regularEndpointPowerCutoff rho) := by
  have heta : 0 < eta := lt_trans hrho hrhoEta
  have heta1 : eta < 1 := by linarith
  exact weightedRelativeDensityZero_of_concreteTranslatedEndpoint
    heta
    (eventuallyTranslatedEndpointPaperBounds_concrete heta heta1)
    (eventuallyConcreteTranslatedEndpointData_powerCutoff
      hrho hrhoEta hetaUpper hprime)
    hweight hsmall

end DivisorF
