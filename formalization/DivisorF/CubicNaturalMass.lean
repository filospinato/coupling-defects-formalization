import DivisorF.CubicNaturalDensity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Canonical lower mass for the cubic natural pair space

This module discharges the project-owned combinatorial lower-mass step in
Corollary 6.4.  The exact natural pair space contains every quotient block whose
type lies in a common endpoint-core cutoff at the left endpoint `Y`.  Since
there are exactly `Y` quotient endpoints in `[Y,2Y)` and each endpoint has
weight `endpointPairWeight K`, this gives the required lower mass

`Y * endpointPairWeight K`.

The canonical integral choice is the floor of `Y^delta`, with
`delta = gamma/(1-gamma)`.  The only remaining scalar comparison is therefore
between the dyadic upper endpoint weight and this canonical lower-core weight.
No prime-distribution theorem enters here.
-/

namespace DivisorF

open scoped BigOperators

/-- The canonical integral lower cutoff `floor(Y^delta)`. -/
noncomputable def cubicNaturalCoreCutoff (gamma : ℝ) (Y : ℕ) : ℕ :=
  ⌊(Y : ℝ) ^ cubicEndpointExponent gamma⌋₊

/-- A lower cutoff is eventually contained in the canonical endpoint
`delta = gamma/(1-gamma)` core at the left edge of each dyadic block. -/
def EventuallyCubicNaturalCoreCutoff
    (gamma : ℝ) (K : ℕ → ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ s : ℕ, 2 ≤ s → s ≤ K Y →
      EndpointPowerCone (cubicEndpointExponent gamma) Y s

/-- The floor cutoff is pointwise contained in the canonical endpoint core. -/
theorem cubicNaturalCoreCutoff_mem_endpointCore
    (gamma : ℝ) (Y : ℕ) :
    EndpointPowerCone (cubicEndpointExponent gamma) Y
      (cubicNaturalCoreCutoff gamma Y) := by
  unfold EndpointPowerCone cubicNaturalCoreCutoff
  have hnonneg : 0 ≤ (Y : ℝ) ^ cubicEndpointExponent gamma :=
    Real.rpow_nonneg (by positivity) _
  exact Nat.floor_le hnonneg

/-- Hence the canonical floor cutoff satisfies the eventual core-cutoff
interface with no asymptotic loss. -/
theorem eventuallyCubicNaturalCoreCutoff_canonical
    (gamma : ℝ) :
    EventuallyCubicNaturalCoreCutoff gamma (cubicNaturalCoreCutoff gamma) := by
  refine ⟨0, ?_⟩
  intro Y _ s _ hs
  unfold EndpointPowerCone
  have hcast : (s : ℝ) ≤ (cubicNaturalCoreCutoff gamma Y : ℝ) := by
    exact_mod_cast hs
  exact hcast.trans (cubicNaturalCoreCutoff_mem_endpointCore gamma Y)

/-- Every constant-cutoff weighted pair over `[Y,2Y)` lies in the exact natural
`N^gamma` pair space once the cutoff lies in the endpoint core at `Y`.

This is the lower half of the manuscript's cubic sandwich, used uniformly over
all endpoints in the dyadic block. -/
theorem weightedPairSpace_subset_cubicNaturalPairSpace_of_core_cutoff
    {Y K : ℕ} {gamma : ℝ}
    (hY : 1 ≤ Y) (hgamma : 0 < gamma)
    (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hcoreY : ∀ s : ℕ, 2 ≤ s → s ≤ K →
      EndpointPowerCone (cubicEndpointExponent gamma) Y s) :
    weightedPairSpace Y (fun _ => K) ⊆ cubicNaturalPairSpace Y gamma := by
  intro p hp
  rcases p with ⟨N, s⟩
  have hw := (mem_weightedPairSpace.mp hp)
  have hYX : Y ≤ N / s := hw.1
  have hX2Y : N / s < 2 * Y := hw.2.1
  have hs2 : 2 ≤ s := hw.2.2.1
  have hsK : s ≤ K := by simpa using hw.2.2.2
  let X := N / s
  have hspos : 0 < s := by omega
  have hX1 : 1 ≤ X := by
    dsimp [X]
    exact le_trans hY hYX
  have hlo : s * X ≤ N := by
    dsimp [X]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N s
  have hhi : N < s * X + s := by
    have h := (Nat.div_lt_iff_lt_mul hspos).1 (Nat.lt_succ_self (N / s))
    dsimp [X]
    calc
      N < (N / s + 1) * s := h
      _ = (N / s) * s + s := by rw [Nat.add_mul, one_mul]
      _ = s * (N / s) + s := by rw [Nat.mul_comm (N / s) s]
  have hblock : (N, s) ∈ quotientBlockPairs X s :=
    mem_quotientBlockPairs.mpr ⟨rfl, hlo, hhi⟩
  have hdeltaPos := cubicEndpointExponent_pos hgamma hgammaUpper
  have hcoreAtY := hcoreY s hs2 hsK
  have hYnonneg : (0 : ℝ) ≤ (Y : ℝ) := by positivity
  have hYXreal : (Y : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hYX
  have hpowerMono :
      (Y : ℝ) ^ cubicEndpointExponent gamma ≤
        (X : ℝ) ^ cubicEndpointExponent gamma :=
    Real.rpow_le_rpow hYnonneg hYXreal (le_of_lt hdeltaPos)
  have hcoreAtX : EndpointPowerCone (cubicEndpointExponent gamma) X s := by
    unfold EndpointPowerCone at hcoreAtY ⊢
    exact le_trans hcoreAtY hpowerMono
  have hnatural : NaturalPowerCone gamma N s :=
    endpointCoreContainedInNaturalCone_cubic hgamma hgammaUpper
      X s N hX1 hs2 hblock hcoreAtX
  apply (mem_cubicNaturalPairSpace hY hgamma hgammaUpper).2
  simpa [X] using ⟨hYX, hX2Y, hs2, hnatural⟩

/-- The constant-cutoff weighted space over `[Y,2Y)` has exactly
`Y * endpointPairWeight K` pairs. -/
theorem weightedPairSpace_const_cutoff_card
    (Y K : ℕ) :
    (weightedPairSpace Y (fun _ => K)).card =
      Y * endpointPairWeight K := by
  rw [weightedPairSpace_card]
  calc
    (∑ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight K)
        = (Finset.Ico Y (2 * Y)).card * endpointPairWeight K := by simp
    _ = Y * endpointPairWeight K := by
      rw [Nat.card_Ico]
      have hdiff : 2 * Y - Y = Y := by omega
      rw [hdiff]

/-- Finite canonical lower-mass bound for the exact natural pair space. -/
theorem cubicNaturalPairSpace_card_lower_of_core_cutoff
    {Y K : ℕ} {gamma : ℝ}
    (hY : 1 ≤ Y) (hgamma : 0 < gamma)
    (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hcoreY : ∀ s : ℕ, 2 ≤ s → s ≤ K →
      EndpointPowerCone (cubicEndpointExponent gamma) Y s) :
    Y * endpointPairWeight K ≤ (cubicNaturalPairSpace Y gamma).card := by
  have hsubset :=
    weightedPairSpace_subset_cubicNaturalPairSpace_of_core_cutoff
      hY hgamma hgammaUpper hcoreY
  have hcard := Finset.card_le_card hsubset
  rwa [weightedPairSpace_const_cutoff_card] at hcard

/-- Eventual endpoint-core cutoffs automatically supply the exact
`Omega(Y W(Y))` hypothesis used by `CubicNaturalDensity`, with
`W(Y)=endpointPairWeight (K Y)`. -/
theorem eventuallyCubicNaturalTotalWeightLower_of_core_cutoff
    {gamma : ℝ} {K : ℕ → ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hcore : EventuallyCubicNaturalCoreCutoff gamma K) :
    EventuallyCubicNaturalTotalWeightLower gamma
      (fun Y => endpointPairWeight (K Y)) := by
  rcases hcore with ⟨Ycore, hcore⟩
  refine ⟨max 1 Ycore, ?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYcore : Ycore ≤ Y := le_trans (Nat.le_max_right _ _) hY
  exact cubicNaturalPairSpace_card_lower_of_core_cutoff
    hY1 hgamma hgammaUpper (hcore Y hYcore)

/-- The manuscript's canonical floor scale gives the exact lower-mass input
without any additional asymptotic hypothesis. -/
theorem eventuallyCubicNaturalTotalWeightLower_canonical
    {gamma : ℝ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    EventuallyCubicNaturalTotalWeightLower gamma
      (fun Y => endpointPairWeight (cubicNaturalCoreCutoff gamma Y)) := by
  exact eventuallyCubicNaturalTotalWeightLower_of_core_cutoff
    hgamma hgammaUpper (eventuallyCubicNaturalCoreCutoff_canonical gamma)

/-- Corollary 6.4 with the total-mass hypothesis discharged by a canonical
endpoint-core cutoff.  The remaining quantitative input is only the comparison
between the dyadic upper endpoint weight and this lower-core weight. -/
theorem cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints_and_core_cutoff
    {gamma : ℝ} {E : ℕ → Finset ℕ} {K : ℕ → ℕ} {A : ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hA : 1 ≤ A)
    (hzero : EventuallyZeroOutsideBadEndpointsNatural gamma E)
    (hsparse : EventuallySparseBadEndpoints E)
    (hcore : EventuallyCubicNaturalCoreCutoff gamma K)
    (hweight : EventuallyCubicNaturalEndpointWeightBound gamma
      (fun Y => endpointPairWeight (K Y)) A) :
    CubicNaturalRelativeDensityZero gamma := by
  exact cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints
    hgamma hgammaUpper hA hzero hsparse hweight
    (eventuallyCubicNaturalTotalWeightLower_of_core_cutoff
      hgamma hgammaUpper hcore)

/-- Canonical-scale form: after the exact lower mass is discharged, only the
upper/lower endpoint-weight comparison remains as elementary scalar input. -/
theorem cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints_canonical
    {gamma : ℝ} {E : ℕ → Finset ℕ} {A : ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hA : 1 ≤ A)
    (hzero : EventuallyZeroOutsideBadEndpointsNatural gamma E)
    (hsparse : EventuallySparseBadEndpoints E)
    (hweight : EventuallyCubicNaturalEndpointWeightBound gamma
      (fun Y => endpointPairWeight (cubicNaturalCoreCutoff gamma Y)) A) :
    CubicNaturalRelativeDensityZero gamma := by
  exact cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints
    hgamma hgammaUpper hA hzero hsparse hweight
    (eventuallyCubicNaturalTotalWeightLower_canonical hgamma hgammaUpper)

end DivisorF
