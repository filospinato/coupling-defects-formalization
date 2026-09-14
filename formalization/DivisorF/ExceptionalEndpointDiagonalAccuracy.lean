import DivisorF.ExceptionalEndpointLiteralBadSet
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Accuracy outside the global exceptional set in Lemma 6.1

The dyadic diagonalisation has two outputs in the manuscript.  Its exceptional
set is sparse, but equally importantly the reciprocal precision selected on the
`j`-th block tends to infinity.  Because the block exceptional finset contains
*all* points that are bad at that selected precision, every point outside the
single global set has relative error tending to zero.

The earlier diagonal modules formalized the sparsity output.  After
`ExceptionalEndpointLiteralBadSet` made the bad traces complete, this module
formalizes the accuracy output in a division-free form.  No prime-distribution
or real-analysis theorem occurs here.
-/

namespace DivisorF

/-- Literal reciprocal precision `1/k` used in the manuscript's diagonal
argument. -/
noncomputable def reciprocalError (k : ℕ) : ℝ := 1 / (k : ℝ)

/-- The exact `1/k`-bad endpoints for one fixed statistic and exponent. -/
noncomputable def reciprocalBadEndpoints
    (A : ℝ → ℝ) (eta : ℝ) (k Y : ℕ) : Finset ℕ :=
  literalFixedErrorBadEndpoints Y A (reciprocalError k) eta

/-- The reciprocal bad family has the literal dyadic support. -/
theorem reciprocalBadEndpoints_support
    {A : ℝ → ℝ} {eta : ℝ} :
    FixedPrecisionExceptionalSupport (reciprocalBadEndpoints A eta) := by
  intro k Y n hn
  exact literalFixedErrorBadEndpoints_supported hn

/-- Division-free formulation of relative error tending to zero outside one
integer exceptional set:

`C * |A(n)-n^eta| <= n^eta`

eventually, for every fixed reciprocal precision `C >= 1`. -/
def EventuallyRelativeAccurateOutside
    (S : Set ℕ) (A : ℝ → ℝ) (eta : ℝ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∉ S →
    |A (n : ℝ) - (n : ℝ) ^ eta| * (C : ℝ) ≤ (n : ℝ) ^ eta

/-- Goodness at reciprocal precision `1/k` gives the corresponding
multiplication-free relative-error bound after multiplying by `k`. -/
theorem relative_error_mul_le_of_not_bad_reciprocal
    {A : ℝ → ℝ} {eta : ℝ} {k n : ℕ}
    (hk : 1 ≤ k)
    (hgood : ¬ RealRelativeBad A (fun x => x ^ eta)
      (reciprocalError k) (n : ℝ)) :
    |A (n : ℝ) - (n : ℝ) ^ eta| * (k : ℝ) ≤ (n : ℝ) ^ eta := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hmain0 : 0 ≤ (n : ℝ) ^ eta := Real.rpow_nonneg (by positivity) eta
  have hle :
      |A (n : ℝ) - (n : ℝ) ^ eta| ≤
        reciprocalError k * (n : ℝ) ^ eta := by
    exact le_of_not_gt hgood
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hkpos)
  calc
    |A (n : ℝ) - (n : ℝ) ^ eta| * (k : ℝ)
        ≤ (reciprocalError k * (n : ℝ) ^ eta) * (k : ℝ) := hmul
    _ = (n : ℝ) ^ eta := by
      dsimp [reciprocalError]
      field_simp

/-- On an exact dyadic block, once precision `C` and its threshold have been
reached, every point outside the global diagonal exceptional set already has
relative error at most `1/C` in the division-free sense. -/
theorem relative_error_mul_le_on_dyadic_block_outside_global
    {A : ℝ → ℝ} {eta : ℝ} {threshold : ℕ → ℕ}
    {C j n : ℕ}
    (hC : 1 ≤ C)
    (hCscale : C ≤ 2 ^ j)
    (hthreshold : threshold C ≤ 2 ^ j)
    (hnblock : n ∈ exceptionalDyadicBlock j)
    (hnglobal : n ∉ globalDiagonalExceptionalSet
      (reciprocalBadEndpoints A eta) threshold) :
    |A (n : ℝ) - (n : ℝ) ^ eta| * (C : ℝ) ≤ (n : ℝ) ^ eta := by
  let k := exceptionalDiagonalPrecision threshold (2 ^ j)
  have hCk : C ≤ k :=
    le_exceptionalDiagonalPrecision hC hCscale hthreshold
  have hk : 1 ≤ k := hC.trans hCk
  have hgood :
      ¬ RealRelativeBad A (fun x => x ^ eta) (reciprocalError k) (n : ℝ) := by
    have h := good_at_diagonal_precision_of_not_mem_global
      (A := fun _ _ => A)
      (delta := fun k => reciprocalError k)
      (eta := fun _ => eta)
      (threshold := threshold)
      hnblock hnglobal
    simpa [reciprocalBadEndpoints, literalFixedPrecisionBadEndpoints, k] using h
  have hkbound :
      |A (n : ℝ) - (n : ℝ) ^ eta| * (k : ℝ) ≤ (n : ℝ) ^ eta :=
    relative_error_mul_le_of_not_bad_reciprocal hk hgood
  have hcast : (C : ℝ) ≤ (k : ℝ) := by exact_mod_cast hCk
  have habs0 : 0 ≤ |A (n : ℝ) - (n : ℝ) ^ eta| := abs_nonneg _
  exact (mul_le_mul_of_nonneg_left hcast habs0).trans hkbound

/-- Every positive integer belongs to the exact dyadic block determined by its
binary logarithm. -/
theorem mem_exceptionalDyadicBlock_log
    {n : ℕ} (hn : 1 ≤ n) :
    n ∈ exceptionalDyadicBlock (Nat.log 2 n) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hlow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hupp : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  apply Finset.mem_Ico.mpr
  constructor
  · simpa [exceptionalDyadicBlock] using hlow
  · simpa [exceptionalDyadicBlock, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hupp

/-- **Lemma 6.1 diagonal accuracy.**

For the literal `1/k` bad sets, the single global diagonal exceptional set has
relative error tending to zero outside it.  This is the accuracy half of the
manuscript's Step 2; the sparsity half is proved separately by the existing
global-window theorem. -/
theorem eventuallyRelativeAccurateOutside_globalDiagonal
    {A : ℝ → ℝ} {eta : ℝ} {threshold : ℕ → ℕ} :
    EventuallyRelativeAccurateOutside
      (globalDiagonalExceptionalSet (reciprocalBadEndpoints A eta) threshold)
      A eta := by
  intro C hC
  let B₀ := max C (threshold C)
  refine ⟨max 1 (2 * B₀), ?_⟩
  intro n hn hnglobal
  have hnpos : 1 ≤ n := le_trans (Nat.le_max_left _ _) hn
  let j := Nat.log 2 n
  let B := 2 ^ j
  have hnblock : n ∈ exceptionalDyadicBlock j := by
    dsimp [j]
    exact mem_exceptionalDyadicBlock_log hnpos
  have hnupper : n < 2 * B := by
    exact (Finset.mem_Ico.mp hnblock).2
  have h2B₀n : 2 * B₀ ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hB₀B : B₀ ≤ B := by omega
  have hCB : C ≤ B := (Nat.le_max_left _ _).trans hB₀B
  have hthresholdB : threshold C ≤ B := (Nat.le_max_right _ _).trans hB₀B
  exact relative_error_mul_le_on_dyadic_block_outside_global
    hC hCB hthresholdB hnblock hnglobal

end DivisorF
