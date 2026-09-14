import DivisorF.WeightedRelativeDensity
import DivisorF.AsymptoticPrimeTransfer
import Mathlib.Tactic

set_option linter.style.header false

namespace DivisorF

noncomputable def cubicEndpointExponent (gamma : ℝ) : ℝ :=
  gamma / (1 - gamma)

theorem cubicEndpointExponent_pos
    {gamma : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    0 < cubicEndpointExponent gamma := by
  unfold cubicEndpointExponent
  have hden : 0 < 1 - gamma := by linarith
  exact div_pos hgamma hden

theorem cubicEndpointExponent_lt_half
    {gamma : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    cubicEndpointExponent gamma < (1 : ℝ) / 2 := by
  unfold cubicEndpointExponent
  have hden : 0 < 1 - gamma := by linarith
  rw [div_lt_iff₀ hden]
  linarith

theorem gamma_eq_cubicEndpointExponent_div_one_add
    {gamma : ℝ} (hgammaUpper : gamma < 1) :
    gamma = cubicEndpointExponent gamma / (1 + cubicEndpointExponent gamma) := by
  unfold cubicEndpointExponent
  have hden : 1 - gamma ≠ 0 := by linarith
  field_simp [hden]
  ring

theorem exists_rho_for_cubic_density
    {gamma : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    ∃ rho : ℝ,
      cubicEndpointExponent gamma < rho ∧ rho < (1 : ℝ) / 2 := by
  have hdelta := cubicEndpointExponent_lt_half hgamma hgammaUpper
  refine ⟨(cubicEndpointExponent gamma + (1 : ℝ) / 2) / 2, ?_, ?_⟩ <;>
    linarith

def EndpointPowerCone (alpha : ℝ) (X s : ℕ) : Prop :=
  (s : ℝ) ≤ (X : ℝ) ^ alpha

theorem endpoint_rpow_le_natural_rpow
    {X s N delta gamma : ℝ}
    (hX : 1 ≤ X) (hs : 1 ≤ s) (hN : s * X ≤ N)
    (hdelta : 0 < delta)
    (hgamma : gamma = delta / (1 + delta))
    (hcone : s ≤ X ^ delta) :
    s ≤ N ^ gamma := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hprodPos : 0 < s * X := mul_pos hspos hXpos
  have hNpos : 0 < N := lt_of_lt_of_le hprodPos hN
  have honeDelta : 0 < 1 + delta := by linarith
  have hlogCone : Real.log s ≤ delta * Real.log X :=
    (Real.le_rpow_iff_log_le hspos hXpos).1 hcone
  have hlogProduct : Real.log (s * X) = Real.log s + Real.log X := by
    rw [Real.log_mul hspos.ne' hXpos.ne']
  have hlogN : Real.log (s * X) ≤ Real.log N :=
    Real.strictMonoOn_log.monotoneOn hprodPos hNpos hN
  have hscaled : (1 + delta) * Real.log s ≤ delta * Real.log N := by
    rw [hlogProduct] at hlogN
    nlinarith [mul_le_mul_of_nonneg_left hlogN (le_of_lt hdelta)]
  have hlogGoal : Real.log s ≤ gamma * Real.log N := by
    rw [hgamma, div_mul_eq_mul_div]
    apply (le_div_iff₀ honeDelta).2
    simpa [mul_comm] using hscaled
  exact (Real.le_rpow_iff_log_le hspos hNpos).2 hlogGoal

theorem natural_rpow_le_succ_endpoint_rpow
    {X s N delta gamma : ℝ}
    (hX : 0 ≤ X) (hs : 1 ≤ s) (hNpos : 0 < N)
    (hN : N ≤ s * (X + 1))
    (hdelta : 0 < delta)
    (hgamma : gamma = delta / (1 + delta))
    (hcone : s ≤ N ^ gamma) :
    s ≤ (X + 1) ^ delta := by
  have hXp : 0 < X + 1 := by linarith
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hprodPos : 0 < s * (X + 1) := mul_pos hspos hXp
  have honeDelta : 0 < 1 + delta := by linarith
  have hgammaPos : 0 < gamma := by
    rw [hgamma]
    exact div_pos hdelta honeDelta
  have hlogCone : Real.log s ≤ gamma * Real.log N :=
    (Real.le_rpow_iff_log_le hspos hNpos).1 hcone
  have hlogN : Real.log N ≤ Real.log (s * (X + 1)) :=
    Real.strictMonoOn_log.monotoneOn hNpos hprodPos hN
  have hlogProduct :
      Real.log (s * (X + 1)) = Real.log s + Real.log (X + 1) := by
    rw [Real.log_mul hspos.ne' hXp.ne']
  have hupper : Real.log s ≤ gamma * (Real.log s + Real.log (X + 1)) := by
    calc
      Real.log s ≤ gamma * Real.log N := hlogCone
      _ ≤ gamma * Real.log (s * (X + 1)) :=
        mul_le_mul_of_nonneg_left hlogN (le_of_lt hgammaPos)
      _ = gamma * (Real.log s + Real.log (X + 1)) := by rw [hlogProduct]
  have hlogGoal : Real.log s ≤ delta * Real.log (X + 1) := by
    rw [hgamma] at hupper
    have hscaled := mul_le_mul_of_nonneg_left hupper (le_of_lt honeDelta)
    field_simp [honeDelta.ne'] at hscaled
    nlinarith
  exact (Real.le_rpow_iff_log_le hspos hXp).2 hlogGoal

def EndpointCoreContainedInNaturalCone
    (gamma delta : ℝ) : Prop :=
  ∀ X s N : ℕ, 1 ≤ X → 2 ≤ s →
    (N, s) ∈ quotientBlockPairs X s →
    EndpointPowerCone delta X s → NaturalPowerCone gamma N s

def EventuallyNaturalConeContainedInEndpointCone
    (gamma rho : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ s N : ℕ, 2 ≤ s →
    (N, s) ∈ quotientBlockPairs X s →
    NaturalPowerCone gamma N s → EndpointPowerCone rho X s

theorem endpointCoreContainedInNaturalCone_cubic
    {gamma : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    EndpointCoreContainedInNaturalCone gamma (cubicEndpointExponent gamma) := by
  intro X s N hX hs hblock hcore
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hs)
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hNXnat : s * X ≤ N := (mem_quotientBlockPairs.mp hblock).2.1
  have hNX : (s : ℝ) * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNXnat
  exact endpoint_rpow_le_natural_rpow hX1 hs1 hNX
    (cubicEndpointExponent_pos hgamma hgammaUpper)
    (gamma_eq_cubicEndpointExponent_div_one_add (lt_trans hgammaUpper (by norm_num)))
    hcore

def EventuallySuccEndpointPowerAbsorbed (delta rho : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ((X + 1 : ℕ) : ℝ) ^ delta ≤ (X : ℝ) ^ rho

theorem eventuallySuccEndpointPowerAbsorbed_of_lt
    {delta rho : ℝ} (hdelta : 0 < delta) (hdeltaRho : delta < rho) :
    EventuallySuccEndpointPowerAbsorbed delta rho := by
  let eps : ℝ := rho - delta
  have heps : 0 < eps := sub_pos.mpr hdeltaRho
  let threshold : ℝ := (2 : ℝ) ^ (delta / eps)
  let X₀ : ℕ := max 1 ⌈threshold⌉₊
  refine ⟨X₀, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hceilX : ⌈threshold⌉₊ ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hceilCast : (⌈threshold⌉₊ : ℝ) ≤ (X : ℝ) := by exact_mod_cast hceilX
  have hthresholdX : threshold ≤ (X : ℝ) :=
    (Nat.le_ceil threshold).trans hceilCast
  have hXnonneg : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX1)
  have hsuccNat : X + 1 ≤ 2 * X := by omega
  have hsucc : (((X + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * (X : ℝ)) := by exact_mod_cast hsuccNat
  have hthresholdNonneg : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have htwoDelta : (2 : ℝ) ^ delta ≤ (X : ℝ) ^ eps := by
    have hmono := Real.rpow_le_rpow hthresholdNonneg hthresholdX (le_of_lt heps)
    calc
      (2 : ℝ) ^ delta = threshold ^ eps := by
        dsimp [threshold]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        field_simp [heps.ne']
      _ ≤ (X : ℝ) ^ eps := hmono
  calc
    (((X + 1 : ℕ) : ℝ) ^ delta)
        ≤ ((2 : ℝ) * (X : ℝ)) ^ delta :=
      Real.rpow_le_rpow (by positivity) hsucc (le_of_lt hdelta)
    _ = (2 : ℝ) ^ delta * (X : ℝ) ^ delta :=
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXnonneg
    _ ≤ (X : ℝ) ^ eps * (X : ℝ) ^ delta :=
      mul_le_mul_of_nonneg_right htwoDelta (Real.rpow_nonneg hXnonneg delta)
    _ = (X : ℝ) ^ (eps + delta) := (Real.rpow_add hXpos eps delta).symm
    _ = (X : ℝ) ^ rho := by
      congr 1
      dsimp [eps]
      ring

theorem eventuallyNaturalConeContainedInEndpointCone_of_succ_absorption
    {gamma rho : ℝ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (habsorb : EventuallySuccEndpointPowerAbsorbed (cubicEndpointExponent gamma) rho) :
    EventuallyNaturalConeContainedInEndpointCone gamma rho := by
  rcases habsorb with ⟨X₀, hX₀⟩
  refine ⟨max X₀ 1, ?_⟩
  intro X hX s N hs hblock hcone
  have hXX₀ : X₀ ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hs)
  have hNlowerNat : s * X ≤ N := (mem_quotientBlockPairs.mp hblock).2.1
  have hNposNat : 0 < N := by
    have : 0 < s * X := Nat.mul_pos (by omega) hX1
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hupperNat : N ≤ s * (X + 1) := by
    have hlt : N < s * X + s := (mem_quotientBlockPairs.mp hblock).2.2
    have : N < s * (X + 1) := by simpa [Nat.mul_add] using hlt
    omega
  have hupper : (N : ℝ) ≤ (s : ℝ) * ((X : ℝ) + 1) := by exact_mod_cast hupperNat
  have hpre : (s : ℝ) ≤ ((X : ℝ) + 1) ^ cubicEndpointExponent gamma :=
    natural_rpow_le_succ_endpoint_rpow (by positivity) hs1 hNpos hupper
      (cubicEndpointExponent_pos hgamma hgammaUpper)
      (gamma_eq_cubicEndpointExponent_div_one_add (lt_trans hgammaUpper (by norm_num)))
      hcone
  calc
    (s : ℝ) ≤ ((X : ℝ) + 1) ^ cubicEndpointExponent gamma := hpre
    _ = (((X + 1 : ℕ) : ℝ) ^ cubicEndpointExponent gamma) := by norm_num
    _ ≤ (X : ℝ) ^ rho := hX₀ X hXX₀

theorem eventuallyNaturalConeContainedInEndpointCone_cubic
    {gamma rho : ℝ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hdeltaRho : cubicEndpointExponent gamma < rho) :
    EventuallyNaturalConeContainedInEndpointCone gamma rho := by
  exact eventuallyNaturalConeContainedInEndpointCone_of_succ_absorption
    hgamma hgammaUpper
    (eventuallySuccEndpointPowerAbsorbed_of_lt
      (cubicEndpointExponent_pos hgamma hgammaUpper) hdeltaRho)

def CubicDensityRangePackage (gamma : ℝ) : Prop :=
  ∃ delta rho : ℝ,
    delta = cubicEndpointExponent gamma ∧
    0 < delta ∧ delta < rho ∧ rho < (1 : ℝ) / 2 ∧
    EndpointCoreContainedInNaturalCone gamma delta ∧
    EventuallyNaturalConeContainedInEndpointCone gamma rho

theorem cubicDensityRangePackage_of_containments
    {gamma : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hlower : EndpointCoreContainedInNaturalCone gamma (cubicEndpointExponent gamma))
    (hupper :
      ∃ rho : ℝ,
        cubicEndpointExponent gamma < rho ∧ rho < (1 : ℝ) / 2 ∧
        EventuallyNaturalConeContainedInEndpointCone gamma rho) :
    CubicDensityRangePackage gamma := by
  rcases hupper with ⟨rho, hdeltaRho, hrhoHalf, hcontain⟩
  refine ⟨cubicEndpointExponent gamma, rho, rfl,
    cubicEndpointExponent_pos hgamma hgammaUpper,
    hdeltaRho, hrhoHalf, hlower, hcontain⟩

theorem cubicDensityRangePackage_of_rho_containments
    {gamma rho : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hdeltaRho : cubicEndpointExponent gamma < rho)
    (hrhoHalf : rho < (1 : ℝ) / 2)
    (hlower : EndpointCoreContainedInNaturalCone gamma (cubicEndpointExponent gamma))
    (hupper : EventuallyNaturalConeContainedInEndpointCone gamma rho) :
    CubicDensityRangePackage gamma := by
  exact cubicDensityRangePackage_of_containments hgamma hgammaUpper hlower
    ⟨rho, hdeltaRho, hrhoHalf, hupper⟩

theorem cubicDensityRangePackage_of_succ_absorption
    {gamma rho : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hdeltaRho : cubicEndpointExponent gamma < rho)
    (hrhoHalf : rho < (1 : ℝ) / 2)
    (habsorb : EventuallySuccEndpointPowerAbsorbed (cubicEndpointExponent gamma) rho) :
    CubicDensityRangePackage gamma := by
  exact cubicDensityRangePackage_of_rho_containments hgamma hgammaUpper
    hdeltaRho hrhoHalf
    (endpointCoreContainedInNaturalCone_cubic hgamma hgammaUpper)
    (eventuallyNaturalConeContainedInEndpointCone_of_succ_absorption
      hgamma hgammaUpper habsorb)

theorem cubicDensityRangePackage
    {gamma : ℝ} (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3) :
    CubicDensityRangePackage gamma := by
  rcases exists_rho_for_cubic_density hgamma hgammaUpper with
    ⟨rho, hdeltaRho, hrhoHalf⟩
  exact cubicDensityRangePackage_of_rho_containments hgamma hgammaUpper
    hdeltaRho hrhoHalf
    (endpointCoreContainedInNaturalCone_cubic hgamma hgammaUpper)
    (eventuallyNaturalConeContainedInEndpointCone_cubic
      hgamma hgammaUpper hdeltaRho)

end DivisorF
