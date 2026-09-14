import DivisorF.CrossingPacking
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Paper-facing same-type multiplicity corollaries

This module exposes the exact Section 3.4 convention and threshold statement on
top of the occupied-type representation used internally by `Multiplicity.lean`.
The manuscript sets `d_s(N)=0` when the quotient type does not occur; internally
`typeDefect` is intentionally defined only for occupied types so that no dummy
representative is needed.
-/

namespace DivisorF

/--
The manuscript's total `d_s(N)`: the common defect on an occupied quotient
class, and zero when the class is empty.
-/
noncomputable def paperTypeDefect (N s : ℕ) : ℤ := by
  classical
  exact if h : TypeOccupied N s then typeDefect h else 0

@[simp]
theorem paperTypeDefect_eq_of_occupied
    {N s : ℕ} (h : TypeOccupied N s) :
    paperTypeDefect N s = typeDefect h := by
  classical
  simp [paperTypeDefect, h]

@[simp]
theorem paperTypeDefect_eq_zero_of_not_occupied
    {N s : ℕ} (h : ¬ TypeOccupied N s) :
    paperTypeDefect N s = 0 := by
  classical
  simp [paperTypeDefect, h]

/-- Positive multiplicity is exactly occupancy of the quotient class. -/
theorem typeMultiplicity_pos_iff_occupied {N s : ℕ} :
    0 < typeMultiplicity N s ↔ TypeOccupied N s := by
  unfold typeMultiplicity TypeOccupied
  exact Finset.card_pos

/--
Natural-number form of the exact floor bound behind Corollary 3.7:

`d_s(N) ≤ floor(2(s-1)/t_s(N))`.
-/
theorem typeDefectNat_le_multiplicity_floor
    {N s : ℕ} (hocc : TypeOccupied N s) :
    typeDefectNat hocc ≤ (2 * (s - 1)) / typeMultiplicity N s := by
  have hpos : 0 < typeMultiplicity N s :=
    typeMultiplicity_pos_iff_occupied.mpr hocc
  apply (Nat.le_div_iff_mul_le hpos).2
  have hbudget := typeMultiplicity_mul_typeDefectNat_le hocc
  simpa [Nat.mul_comm] using hbudget

/--
**Corollary 3.7, exact threshold form.**  When `t_s(N)≥1`, the paper's common
defect satisfies

`d_s(N) ≤ floor(2(s-1)/t_s(N))`.
-/
theorem paperTypeDefect_le_multiplicity_floor
    {N s : ℕ} (hpos : 0 < typeMultiplicity N s) :
    paperTypeDefect N s
      ≤ (((2 * (s - 1)) / typeMultiplicity N s : ℕ) : ℤ) := by
  have hocc : TypeOccupied N s :=
    typeMultiplicity_pos_iff_occupied.mp hpos
  rw [paperTypeDefect_eq_of_occupied hocc, ← coe_typeDefectNat hocc]
  exact_mod_cast typeDefectNat_le_multiplicity_floor hocc

/--
Paper-facing form of Corollary 3.6, including the empty-type convention.
-/
theorem paperTypeMultiplicity_mul_typeDefect_le
    (N s : ℕ) :
    (typeMultiplicity N s : ℤ) * paperTypeDefect N s
      ≤ ((2 * (s - 1) : ℕ) : ℤ) := by
  classical
  by_cases hocc : TypeOccupied N s
  · rw [paperTypeDefect_eq_of_occupied hocc,
      ← coe_typeDefectNat hocc]
    exact_mod_cast typeMultiplicity_mul_typeDefectNat_le hocc
  · have hmult : typeMultiplicity N s = 0 := by
      by_contra hne
      apply hocc
      apply typeMultiplicity_pos_iff_occupied.mp
      exact Nat.pos_of_ne_zero hne
    simp [paperTypeDefect, hocc, hmult]

end DivisorF
