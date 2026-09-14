import DivisorF.ExceptionalEndpointTransfer
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Dyadic diagonalisation of integer exceptional endpoints

Lemma 6.1 of the manuscript first obtains, for every fixed reciprocal precision,
a sufficiently late dyadic range on which the integer exceptional set has the
corresponding small relative cardinality. It then diagonalises those fixed-
precision statements to one exceptional family whose relative density tends to
zero.

This module formalizes that project-owned diagonal step. It deliberately does
not assert the preceding Gafni--Tao real-variable estimate or the
measure-theoretic thickening argument converting it to fixed-precision integer
bounds. Those remain explicit upstream input. The result here starts exactly
from the family of thresholds delivered by that conversion and constructs the
single sparse dyadic family used by the translated-endpoint machinery.

The manuscript then assembles the dyadic family into one set `E_eta ⊆ ℕ` by
using the bad set selected on each block `[2^j,2^(j+1))`.  The final part of this
module records that fidelity bridge explicitly: on every exact dyadic block the
global set has precisely the previously constructed diagonal trace.
-/

namespace DivisorF

/-- At scale `Y`, choose the largest precision `k <= Y` whose threshold has
already been reached. If none is available the value is `0`; all asymptotic
uses below work beyond the threshold for precision `1`, so the zero fallback is
irrelevant there. -/
def exceptionalDiagonalPrecision (threshold : ℕ → ℕ) (Y : ℕ) : ℕ :=
  Nat.findGreatest (fun k => 1 ≤ k ∧ threshold k ≤ Y) Y

/-- Once the threshold for a requested precision `C` has been reached and
`C <= Y`, the diagonal precision is at least `C`. -/
theorem le_exceptionalDiagonalPrecision
    {threshold : ℕ → ℕ} {C Y : ℕ}
    (hC : 1 ≤ C) (hCY : C ≤ Y) (hthreshold : threshold C ≤ Y) :
    C ≤ exceptionalDiagonalPrecision threshold Y := by
  simpa [exceptionalDiagonalPrecision] using
    (Nat.le_findGreatest hCY (show 1 ≤ C ∧ threshold C ≤ Y from ⟨hC, hthreshold⟩))

/-- Under the same nonempty-tail hypothesis, the precision selected by the
maximum is itself certified at scale `Y`. -/
theorem exceptionalDiagonalPrecision_spec
    {threshold : ℕ → ℕ} {C Y : ℕ}
    (hC : 1 ≤ C) (hCY : C ≤ Y) (hthreshold : threshold C ≤ Y) :
    1 ≤ exceptionalDiagonalPrecision threshold Y ∧
      threshold (exceptionalDiagonalPrecision threshold Y) ≤ Y := by
  simpa [exceptionalDiagonalPrecision] using
    (Nat.findGreatest_spec
      (P := fun k => 1 ≤ k ∧ threshold k ≤ Y)
      hCY (show 1 ≤ C ∧ threshold C ≤ Y from ⟨hC, hthreshold⟩))

/-- Select at each dyadic scale the exceptional set corresponding to the
largest precision whose fixed-precision estimate is already certified. -/
def diagonalExceptionalEndpoints
    (E : ℕ → ℕ → Finset ℕ) (threshold : ℕ → ℕ) (Y : ℕ) : Finset ℕ :=
  E (exceptionalDiagonalPrecision threshold Y) Y

/-- Fixed-precision output expected from the real-to-integer thickening step.
For every `k>=1`, once its threshold has been reached, the exceptional set has
cardinality at most `Y/k`, written without division. -/
def FixedPrecisionExceptionalBounds
    (E : ℕ → ℕ → Finset ℕ) (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    (E k Y).card * k ≤ Y

/-- **Lemma 6.1 dyadic diagonalisation.**

A family of fixed-precision integer exceptional estimates can be combined into
one dyadic exceptional family of relative density zero. No uniformity in the
threshold as `k` varies is assumed: the largest currently certified precision
is chosen separately at every scale.

This is the project-owned diagonal argument after the measure-theoretic
real-to-integer conversion and before the translated map `nu_eta` is applied. -/
theorem eventuallyDyadicallySparse_diagonalExceptionalEndpoints
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hfixed : FixedPrecisionExceptionalBounds E threshold) :
    EventuallyDyadicallySparse (diagonalExceptionalEndpoints E threshold) := by
  intro C hC
  refine ⟨max C (threshold C), ?_⟩
  intro Y hY
  have hCY : C ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hthresholdC : threshold C ≤ Y :=
    le_trans (Nat.le_max_right _ _) hY
  have hCdiag : C ≤ exceptionalDiagonalPrecision threshold Y :=
    le_exceptionalDiagonalPrecision hC hCY hthresholdC
  have hdiagSpec :
      1 ≤ exceptionalDiagonalPrecision threshold Y ∧
        threshold (exceptionalDiagonalPrecision threshold Y) ≤ Y :=
    exceptionalDiagonalPrecision_spec hC hCY hthresholdC
  have hdiagBound := hfixed
    (exceptionalDiagonalPrecision threshold Y) hdiagSpec.1 Y hdiagSpec.2
  have hmul :
      (diagonalExceptionalEndpoints E threshold Y).card * C ≤
        (diagonalExceptionalEndpoints E threshold Y).card *
          exceptionalDiagonalPrecision threshold Y := by
    exact Nat.mul_le_mul_left _ hCdiag
  exact hmul.trans hdiagBound

/-- A convenient interface matching the manuscript's quantifier order: if for
every reciprocal precision one can exhibit a threshold and a finite exceptional
family satisfying the fixed-precision estimate, then after choosing all those
thresholds simultaneously there exists a single dyadically sparse exceptional
family.

The choice here is purely project-owned bookkeeping. The proof of the
fixed-precision estimate from the external real-variable theorem is a separate
preceding obligation. -/
theorem exists_eventuallyDyadicallySparse_diagonal_of_fixedPrecision
    {E : ℕ → ℕ → Finset ℕ}
    (hfixed : ∀ k : ℕ, 1 ≤ k → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      (E k Y).card * k ≤ Y) :
    ∃ threshold : ℕ → ℕ,
      EventuallyDyadicallySparse (diagonalExceptionalEndpoints E threshold) := by
  classical
  let threshold : ℕ → ℕ := fun k =>
    if hk : 1 ≤ k then Classical.choose (hfixed k hk) else 0
  have hbounds : FixedPrecisionExceptionalBounds E threshold := by
    intro k hk Y hY
    dsimp [threshold] at hY
    rw [dif_pos hk] at hY
    exact Classical.choose_spec (hfixed k hk) Y hY
  exact ⟨threshold,
    eventuallyDyadicallySparse_diagonalExceptionalEndpoints hbounds⟩

/-- Fixed-precision exceptional finsets are supported on their declared
endpoint block `[Y,2Y)`. This is the discrete support condition used literally
in the manuscript's dyadic construction. -/
def FixedPrecisionExceptionalSupport
    (E : ℕ → ℕ → Finset ℕ) : Prop :=
  ∀ k Y n : ℕ, n ∈ E k Y → Y ≤ n ∧ n < 2 * Y

/-- The scale-indexed diagonal family inherits the same support. -/
theorem diagonalExceptionalEndpoints_supported
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    {Y n : ℕ}
    (hn : n ∈ diagonalExceptionalEndpoints E threshold Y) :
    Y ≤ n ∧ n < 2 * Y := by
  exact hsupp (exceptionalDiagonalPrecision threshold Y) Y n hn

/-- The exact dyadic block `[2^j,2^(j+1))`, in the `[Y,2Y)` form used by the
endpoint-counting layer. -/
def exceptionalDyadicBlock (j : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ j) (2 * (2 ^ j))

/-- Left endpoint of the unique dyadic block containing a positive integer. -/
def exceptionalDyadicScale (n : ℕ) : ℕ :=
  2 ^ Nat.log 2 n

/-- An integer lying in the `j`-th exact dyadic block has dyadic scale `2^j`. -/
theorem exceptionalDyadicScale_eq_of_mem_block
    {j n : ℕ} (hn : n ∈ exceptionalDyadicBlock j) :
    exceptionalDyadicScale n = 2 ^ j := by
  have hbounds : 2 ^ j ≤ n ∧ n < 2 * (2 ^ j) := by
    simpa [exceptionalDyadicBlock] using (Finset.mem_Ico.mp hn)
  have hupp : n < 2 ^ (j + 1) := by
    simpa [pow_succ, Nat.mul_comm] using hbounds.2
  have hlog : Nat.log 2 n = j :=
    Nat.log_eq_of_pow_le_of_lt_pow hbounds.1 hupp
  simp [exceptionalDyadicScale, hlog]

/-- The single global exceptional set constructed exactly as in Lemma 6.1:
on an integer's own dyadic block, use the diagonal bad finset selected at that
block's left endpoint. -/
def globalDiagonalExceptionalSet
    (E : ℕ → ℕ → Finset ℕ) (threshold : ℕ → ℕ) : Set ℕ :=
  {n | n ∈ diagonalExceptionalEndpoints E threshold (exceptionalDyadicScale n)}

/-- Finite trace of the global exceptional set on one exact dyadic block. -/
noncomputable def globalDiagonalExceptionalBlock
    (E : ℕ → ℕ → Finset ℕ) (threshold : ℕ → ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (exceptionalDyadicBlock j).filter
    (fun n => n ∈ globalDiagonalExceptionalSet E threshold)

/-- **Lemma 6.1 global-set fidelity bridge.**

The trace of the manuscript's single global exceptional set on the exact block
`[2^j,2^(j+1))` is precisely the scale-indexed diagonal exceptional finset at
scale `2^j`. Hence the scale-indexed representation used by downstream modules
is literally the dyadic decomposition of one set, rather than a weaker family
with no global realization. -/
theorem globalDiagonalExceptionalBlock_eq
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E) (j : ℕ) :
    globalDiagonalExceptionalBlock E threshold j =
      diagonalExceptionalEndpoints E threshold (2 ^ j) := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hblock, hglobal⟩
    have hscale : exceptionalDyadicScale n = 2 ^ j :=
      exceptionalDyadicScale_eq_of_mem_block hblock
    simpa [globalDiagonalExceptionalSet, hscale] using hglobal
  · intro hn
    have hs := diagonalExceptionalEndpoints_supported hsupp hn
    have hblock : n ∈ exceptionalDyadicBlock j := by
      exact Finset.mem_Ico.mpr hs
    have hscale : exceptionalDyadicScale n = 2 ^ j :=
      exceptionalDyadicScale_eq_of_mem_block hblock
    apply Finset.mem_filter.mpr
    refine ⟨hblock, ?_⟩
    simpa [globalDiagonalExceptionalSet, hscale] using hn

/-- Division-free relative sparsity for the exact dyadic traces of one global
exceptional set. The threshold is expressed on the block's left endpoint. -/
noncomputable def EventuallySparseGlobalDyadicBlocks (S : Set ℕ) : Prop := by
  classical
  exact ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ j : ℕ, Y₀ ≤ 2 ^ j →
    ((exceptionalDyadicBlock j).filter (fun n => n ∈ S)).card * C ≤ 2 ^ j

/-- A sparse scale-indexed diagonal family therefore realizes one global set
whose exact dyadic traces are sparse with the same quantitative bound. -/
theorem eventuallySparseGlobalDyadicBlocks_of_diagonal
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (hsparse : EventuallyDyadicallySparse
      (diagonalExceptionalEndpoints E threshold)) :
    EventuallySparseGlobalDyadicBlocks
      (globalDiagonalExceptionalSet E threshold) := by
  intro C hC
  rcases hsparse C hC with ⟨Y₀, hY₀⟩
  refine ⟨Y₀, ?_⟩
  intro j hj
  change (globalDiagonalExceptionalBlock E threshold j).card * C ≤ 2 ^ j
  rw [globalDiagonalExceptionalBlock_eq hsupp j]
  exact hY₀ (2 ^ j) hj

/-- End-to-end global-set realization starting from the fixed-precision integer
bounds produced by the real-to-integer thickening step. -/
theorem eventuallySparseGlobalDyadicBlocks_of_fixedPrecision
    {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (hfixed : FixedPrecisionExceptionalBounds E threshold) :
    EventuallySparseGlobalDyadicBlocks
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicBlocks_of_diagonal hsupp
    (eventuallyDyadicallySparse_diagonalExceptionalEndpoints hfixed)

end DivisorF
