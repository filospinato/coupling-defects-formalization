import DivisorF.QuotientPrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.header false

namespace DivisorF

noncomputable def realCubeRoot (x : ℝ) : ℝ :=
  x ^ ((3 : ℝ)⁻¹)

noncomputable def zeroCubicBarrierBase : ℝ :=
  realCubeRoot (1 / 2)

@[simp]
theorem realCubeRoot_cube {x : ℝ} (hx : 0 ≤ x) :
    (realCubeRoot x) ^ 3 = x := by
  unfold realCubeRoot
  simpa using
    (Real.rpow_inv_natCast_pow hx (n := 3) (by decide : (3 : ℕ) ≠ 0))

theorem realCubeRoot_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ realCubeRoot x := by
  unfold realCubeRoot
  positivity

private theorem cube_le_cube {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 3 ≤ b ^ 3 := by
  have hb : 0 ≤ b := le_trans ha hab
  have hprod : 0 ≤ (b - a) * (b ^ 2 + b * a + a ^ 2) := by positivity
  nlinarith

private theorem cube_lt_cube {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ 3 < b ^ 3 := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hprod : 0 < (b - a) * (b ^ 2 + b * a + a ^ 2) := by positivity
  nlinarith

/-- Every occupied large-prime quotient type satisfies `s^2 ≤ N`. -/
theorem occupied_type_sq_le
    {N s : ℕ} (hocc : TypeOccupied N s) :
    s ^ 2 ≤ N := by
  rcases hocc with ⟨q, hq⟩
  have htype : q.quotientType = s := mem_typePrimes.mp hq
  have hsq : s * q.val ≤ N := by
    rw [← htype]
    exact Nat.div_mul_le_self N q.val
  have hsltq : s < q.val := by
    by_contra hnot
    have hqles : q.val ≤ s := Nat.le_of_not_gt hnot
    have hqq : q.val * q.val ≤ s * q.val :=
      Nat.mul_le_mul_right q.val hqles
    exact (not_le_of_gt q.large) (le_trans hqq hsq)
  have hss : s * s ≤ s * q.val :=
    Nat.mul_le_mul_left s (Nat.le_of_lt hsltq)
  simpa [pow_two] using le_trans hss hsq

noncomputable def cubeRootThreshold (x : ℝ) : ℕ :=
  max 1 (Nat.ceil (x ^ 3))

theorem le_realCubeRoot_of_threshold
    {x : ℝ} (hx : 0 ≤ x) {N : ℕ}
    (hN : cubeRootThreshold x ≤ N) :
    x ≤ realCubeRoot (N : ℝ) := by
  have hceil : Nat.ceil (x ^ 3) ≤ N :=
    le_trans (le_max_right 1 _) hN
  have hx3N : x ^ 3 ≤ (N : ℝ) := by
    exact le_trans (Nat.le_ceil (x ^ 3)) (by exact_mod_cast hceil)
  have hrpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ x ^ 3) hx3N (by positivity : 0 ≤ (3 : ℝ)⁻¹)
  have hleft : (x ^ 3) ^ ((3 : ℝ)⁻¹) = x := by
    simpa using
      (Real.pow_rpow_inv_natCast hx (n := 3) (by decide : (3 : ℕ) ≠ 0))
  simpa [realCubeRoot, hleft] using hrpow

noncomputable def binaryCubicBarrierN₀ (δ : ℝ) : ℕ := by
  let c := 1 + δ
  let a := c ^ 3 - 1
  exact cubeRootThreshold (1 / (a * c))

noncomputable def zeroCubicBarrierN₀ (δ : ℝ) : ℕ := by
  let c := zeroCubicBarrierBase + δ
  let a := 2 * c ^ 3 - 1
  exact cubeRootThreshold (2 / (a * c))

theorem binary_cubic_exponent_ceiling
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ {N s : ℕ},
      binaryCubicBarrierN₀ δ ≤ N →
      (hocc : TypeOccupied N s) →
      (1 + δ) * realCubeRoot (N : ℝ) ≤ (s : ℝ) →
      ¬ BudgetForcesBinary s (typeMultiplicity N s) := by
  intro N s hN hocc hscale
  let c : ℝ := 1 + δ
  let a : ℝ := c ^ 3 - 1
  let x : ℝ := 1 / (a * c)
  have hc : 0 < c := by dsimp [c]; linarith
  have ha : 0 < a := by
    dsimp [a, c]
    nlinarith [sq_nonneg δ]
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hroot : x ≤ realCubeRoot (N : ℝ) := by
    apply le_realCubeRoot_of_threshold hx
    simpa [binaryCubicBarrierN₀, c, a, x] using hN
  have hcx : c * x ≤ (s : ℝ) := by
    exact le_trans (mul_le_mul_of_nonneg_left hroot hc.le) (by simpa [c] using hscale)
  have hacx : a * c * x = 1 := by
    dsimp [x]
    field_simp [ne_of_gt ha, ne_of_gt hc]
  have has : 1 ≤ a * (s : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hcx ha.le
    nlinarith
  have hsqNat := occupied_type_sq_le hocc
  have hsq : (s : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hsqNat
  have haNs : (s : ℝ) ≤ a * (N : ℝ) := by
    have h1 : (s : ℝ) ≤ (a * (s : ℝ)) * (s : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right has (by positivity : (0 : ℝ) ≤ s)
    have h2 : a * (s : ℝ) ^ 2 ≤ a * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hsq ha.le
    nlinarith
  have hrootnonneg : 0 ≤ realCubeRoot (N : ℝ) := realCubeRoot_nonneg (by positivity)
  have hcuberoot : (realCubeRoot (N : ℝ)) ^ 3 = (N : ℝ) := realCubeRoot_cube (by positivity)
  have hcubescale : (c * realCubeRoot (N : ℝ)) ^ 3 ≤ (s : ℝ) ^ 3 :=
    cube_le_cube (mul_nonneg hc.le hrootnonneg) (by simpa [c] using hscale)
  have hcN : c ^ 3 * (N : ℝ) ≤ (s : ℝ) ^ 3 := by nlinarith
  have htotalR : (N : ℝ) + (s : ℝ) ≤ (s : ℝ) ^ 3 := by
    dsimp [a] at haNs
    nlinarith
  have htotal : N + s ≤ s ^ 3 := by exact_mod_cast htotalR
  have hspos := typeOccupied_type_pos hocc
  have hs2one : 1 ≤ s ^ 2 := by nlinarith
  have hsub := Nat.sub_add_cancel hs2one
  apply binary_defect_multiplicity_barrier hocc
  nlinarith [htotal]

theorem zero_cubic_exponent_ceiling
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ {N s : ℕ},
      zeroCubicBarrierN₀ δ ≤ N →
      (hocc : TypeOccupied N s) →
      (zeroCubicBarrierBase + δ) * realCubeRoot (N : ℝ) ≤ (s : ℝ) →
      ¬ BudgetForcesZero s (typeMultiplicity N s) := by
  intro N s hN hocc hscale
  let c₀ : ℝ := zeroCubicBarrierBase
  let c : ℝ := c₀ + δ
  let a : ℝ := 2 * c ^ 3 - 1
  let x : ℝ := 2 / (a * c)
  have hc₀ : 0 < c₀ := by
    dsimp [c₀, zeroCubicBarrierBase, realCubeRoot]
    positivity
  have hc₀cube : c₀ ^ 3 = 1 / 2 := by
    dsimp [c₀, zeroCubicBarrierBase]
    exact realCubeRoot_cube (by norm_num)
  have hc : 0 < c := by dsimp [c]; linarith
  have hc₀c : c₀ < c := by dsimp [c]; linarith
  have hcubelt : c₀ ^ 3 < c ^ 3 := cube_lt_cube hc₀.le hc₀c
  have ha : 0 < a := by
    dsimp [a]
    nlinarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hroot : x ≤ realCubeRoot (N : ℝ) := by
    apply le_realCubeRoot_of_threshold hx
    simpa [zeroCubicBarrierN₀, c, a, x] using hN
  have hcx : c * x ≤ (s : ℝ) := by
    exact le_trans (mul_le_mul_of_nonneg_left hroot hc.le) (by simpa [c, c₀] using hscale)
  have hacx : a * c * x = 2 := by
    dsimp [x]
    field_simp [ne_of_gt ha, ne_of_gt hc]
  have has : 2 ≤ a * (s : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hcx ha.le
    nlinarith
  have hsqNat := occupied_type_sq_le hocc
  have hsq : (s : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hsqNat
  have haNs : 2 * (s : ℝ) ≤ a * (N : ℝ) := by
    have h1 : 2 * (s : ℝ) ≤ (a * (s : ℝ)) * (s : ℝ) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right has (by positivity : (0 : ℝ) ≤ s)
    have h2 : a * (s : ℝ) ^ 2 ≤ a * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hsq ha.le
    nlinarith
  have hrootnonneg : 0 ≤ realCubeRoot (N : ℝ) := realCubeRoot_nonneg (by positivity)
  have hcuberoot : (realCubeRoot (N : ℝ)) ^ 3 = (N : ℝ) := realCubeRoot_cube (by positivity)
  have hcubescale : (c * realCubeRoot (N : ℝ)) ^ 3 ≤ (s : ℝ) ^ 3 :=
    cube_le_cube (mul_nonneg hc.le hrootnonneg) (by simpa [c, c₀] using hscale)
  have hcN : c ^ 3 * (N : ℝ) ≤ (s : ℝ) ^ 3 := by nlinarith
  have htotalR : (N : ℝ) + 2 * (s : ℝ) ≤ 2 * (s : ℝ) ^ 3 := by
    dsimp [a] at haNs
    nlinarith
  have htotal : N + 2 * s ≤ 2 * s ^ 3 := by exact_mod_cast htotalR
  have hspos := typeOccupied_type_pos hocc
  have hs2one : 1 ≤ s ^ 2 := by nlinarith
  have hsub := Nat.sub_add_cancel hs2one
  apply zero_defect_multiplicity_barrier hocc
  nlinarith [htotal]

end DivisorF
