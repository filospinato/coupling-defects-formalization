import DivisorF.ExceptionalEndpointDiagonal
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Global dyadic exceptional set on arbitrary windows

Lemma 6.1 of the manuscript constructs one global exceptional set by choosing a
bad set independently on the exact dyadic blocks `[2^j,2^(j+1))`.  The paper
then passes from `o(2^j)` on those exact blocks to

`|E_eta ∩ [Y,2Y)| = o(Y)`

for every integer scale `Y`, using that `[Y,2Y)` meets at most two consecutive
dyadic blocks of comparable size.

`ExceptionalEndpointDiagonal` already constructs the literal global set and
proves sparsity on each exact dyadic trace.  This module formalizes the remaining
project-owned finite covering/counting step, in the same division-free
reciprocal-precision form used elsewhere in the Section 6 formalization.
-/

namespace DivisorF

/-- Finite trace of a global exceptional set on the manuscript's arbitrary
half-open window `[Y,2Y)`. -/
noncomputable def globalExceptionalWindow (S : Set ℕ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico Y (2 * Y)).filter (fun n => n ∈ S)

/-- Finite trace on one exact dyadic block.  The classical membership decision
is intentionally sealed inside the noncomputable definition rather than leaked
into statements that mention the trace. -/
noncomputable def globalExceptionalDyadicTrace (S : Set ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (exceptionalDyadicBlock j).filter (fun n => n ∈ S)

/-- Division-free formulation of `|S ∩ [Y,2Y)| = o(Y)`. -/
def EventuallySparseGlobalDyadicWindows (S : Set ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (globalExceptionalWindow S Y).card * C ≤ Y

/-- Every arbitrary window `[Y,2Y)` with `Y>0` is contained in the union of the
exact dyadic block containing `Y` and its successor block.  This is the finite
covering fact used in the last sentence of Step 2 of Lemma 6.1. -/
theorem globalExceptionalWindow_subset_two_dyadic_blocks
    (S : Set ℕ) {Y : ℕ} (hY : 1 ≤ Y) :
    globalExceptionalWindow S Y ⊆
      globalExceptionalDyadicTrace S (Nat.log 2 Y) ∪
      globalExceptionalDyadicTrace S (Nat.log 2 Y + 1) := by
  classical
  intro n hn
  change n ∈ (Finset.Ico Y (2 * Y)).filter (fun n => n ∈ S) at hn
  rcases Finset.mem_filter.mp hn with ⟨hnIco, hnS⟩
  rcases Finset.mem_Ico.mp hnIco with ⟨hYn, hn2Y⟩
  have hYne : Y ≠ 0 := Nat.ne_of_gt hY
  have hlow : 2 ^ Nat.log 2 Y ≤ Y := Nat.pow_log_le_self 2 hYne
  have hupp : Y < 2 ^ (Nat.log 2 Y + 1) := by
    simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) Y
  by_cases hnmid : n < 2 ^ (Nat.log 2 Y + 1)
  · apply Finset.mem_union_left
    change n ∈ (exceptionalDyadicBlock (Nat.log 2 Y)).filter (fun n => n ∈ S)
    apply Finset.mem_filter.mpr
    refine ⟨?_, hnS⟩
    apply Finset.mem_Ico.mpr
    constructor
    · exact hlow.trans hYn
    · simpa [exceptionalDyadicBlock, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hnmid
  · apply Finset.mem_union_right
    change n ∈ (exceptionalDyadicBlock (Nat.log 2 Y + 1)).filter (fun n => n ∈ S)
    apply Finset.mem_filter.mpr
    refine ⟨?_, hnS⟩
    apply Finset.mem_Ico.mpr
    constructor
    · exact Nat.le_of_not_gt hnmid
    · have hnupper : n < 2 ^ (Nat.log 2 Y + 2) := by
        have h2Y : 2 * Y < 2 ^ (Nat.log 2 Y + 2) := by
          calc
            2 * Y < 2 * (2 ^ (Nat.log 2 Y + 1)) :=
              Nat.mul_lt_mul_of_pos_left hupp (by norm_num)
            _ = 2 ^ (Nat.log 2 Y + 2) := by
              simp [pow_succ, Nat.mul_comm]
        exact hn2Y.trans h2Y
      simpa [exceptionalDyadicBlock, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hnupper

/-- **Lemma 6.1, exact-dyadic to arbitrary-window transfer.**

If one global set has `o(2^j)` points on every sufficiently late exact dyadic
block, then it has `o(Y)` points on every sufficiently late `[Y,2Y)` window.
No analytic input occurs here: this is precisely the paper's final bounded-
number-of-blocks bookkeeping step. -/
theorem eventuallySparseGlobalDyadicWindows_of_blocks
    {S : Set ℕ} (hsparse : EventuallySparseGlobalDyadicBlocks S) :
    EventuallySparseGlobalDyadicWindows S := by
  classical
  intro C hC
  have h8C : 1 ≤ 8 * C := by omega
  rcases hsparse (8 * C) h8C with ⟨B₀, hB₀⟩
  refine ⟨max 1 (2 * B₀), ?_⟩
  intro Y hY
  have hYpos : 1 ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYne : Y ≠ 0 := Nat.ne_of_gt hYpos
  let j := Nat.log 2 Y
  let B := 2 ^ j
  have hBY : B ≤ Y := by
    dsimp [B, j]
    exact Nat.pow_log_le_self 2 hYne
  have hY2B : Y < 2 * B := by
    dsimp [B, j]
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) Y
  have hB₀Y : 2 * B₀ ≤ Y := le_trans (Nat.le_max_right _ _) hY
  have hB₀B : B₀ ≤ B := by omega
  have hfirst := hB₀ j hB₀B
  have hsecond := hB₀ (j + 1) (by
    have : B ≤ 2 ^ (j + 1) := by
      dsimp [B]
      simp [pow_succ]
    exact hB₀B.trans this)
  let A := globalExceptionalDyadicTrace S j
  let D := globalExceptionalDyadicTrace S (j + 1)
  have hcover : globalExceptionalWindow S Y ⊆ A ∪ D := by
    dsimp [A, D, j]
    exact globalExceptionalWindow_subset_two_dyadic_blocks S hYpos
  have hcardCover : (globalExceptionalWindow S Y).card ≤ (A ∪ D).card :=
    Finset.card_le_card hcover
  have hunion : (A ∪ D).card ≤ A.card + D.card := Finset.card_union_le _ _
  have hwindow : (globalExceptionalWindow S Y).card ≤ A.card + D.card :=
    hcardCover.trans hunion
  have hfirst' : A.card * (8 * C) ≤ B := by
    change ((exceptionalDyadicBlock j).filter (fun n => n ∈ S)).card * (8 * C) ≤ B
    simpa [B, j] using hfirst
  have hsecond' : D.card * (8 * C) ≤ 2 * B := by
    change ((exceptionalDyadicBlock (j + 1)).filter (fun n => n ∈ S)).card * (8 * C) ≤ 2 * B
    simpa [B, j, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsecond
  have hsum : (A.card + D.card) * C ≤ Y := by
    nlinarith
  exact (Nat.mul_le_mul_right C hwindow).trans hsum

/-- End-to-end global-set statement from the fixed-precision integer estimates:
the diagonal construction gives one set, exact-block sparsity, and hence the
literal `o(Y)` bound on every `[Y,2Y)` window claimed in Lemma 6.1. -/
theorem eventuallySparseGlobalDyadicWindows_of_fixedPrecision
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (hfixed : FixedPrecisionExceptionalBounds E threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_blocks
    (eventuallySparseGlobalDyadicBlocks_of_fixedPrecision hsupp hfixed)

end DivisorF
