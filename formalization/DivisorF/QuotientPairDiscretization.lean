import DivisorF.PointwiseTransfer
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Quotient-pair discretisation

Project-original finite arithmetic from Section 6.  This module deliberately
contains no almost-all prime theorem.  It isolates the exact identity used to
embed one good integer endpoint into every quotient interval in a simultaneous
small-type cone.
-/

namespace DivisorF

/-- The floor of the real quotient by a positive natural denominator agrees
with the corresponding natural Euclidean quotient, expressed as an integer. -/
theorem floor_nat_div_eq_natDiv
    {N d : ℕ} (hd : 0 < d) :
    Int.floor ((N : ℝ) / (d : ℝ)) = (N / d : ℕ) := by
  let b : ℕ := N / d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [Int.floor_eq_iff]
  constructor
  · apply (le_div_iff₀ hdR).2
    have hmul : b * d ≤ N := by
      simpa [b] using Nat.div_mul_le_self N d
    exact_mod_cast hmul
  · apply (div_lt_iff₀ hdR).2
    have hupper : N < (b + 1) * d := by
      apply (Nat.div_lt_iff_lt_mul hd).1
      simp [b]
    exact_mod_cast hupper

/-- **Equation (6.5) candidate (exact quotient width).**

If `N = s X + u` with `0 ≤ u < s`, then

`X - floor(N/(s+1)) = ceil((X-u)/(s+1))`.

The right-hand subtraction is taken in `ℝ`, exactly as in the manuscript, so
the formula also covers the small cases `u > X`; the left-hand natural
subtraction is harmless because `floor(N/(s+1)) ≤ X` follows from the same
Euclidean decomposition.
-/
theorem exact_quotient_width_identity
    {N s X u : ℕ}
    (hs : 0 < s)
    (hu : u < s)
    (hN : N = s * X + u) :
    ((X - N / (s + 1) : ℕ) : ℤ) =
      Int.ceil (((X : ℝ) - (u : ℝ)) / ((s + 1 : ℕ) : ℝ)) := by
  let b : ℕ := N / (s + 1)
  have hd : 0 < s + 1 := Nat.succ_pos s
  have hNX : N < (X + 1) * (s + 1) := by
    rw [hN]
    nlinarith
  have hb_lt : b < X + 1 := by
    apply (Nat.div_lt_iff_lt_mul hd).2
    simpa [b] using hNX
  have hbX : b ≤ X := by omega
  have hfloor :
      Int.floor ((N : ℝ) / ((s + 1 : ℕ) : ℝ)) = (b : ℤ) := by
    simpa [b] using floor_nat_div_eq_natDiv (N := N) hd
  have hdR : 0 < ((s + 1 : ℕ) : ℝ) := by positivity
  have hreal :
      (N : ℝ) / ((s + 1 : ℕ) : ℝ) =
        (X : ℝ) -
          (((X : ℝ) - (u : ℝ)) / ((s + 1 : ℕ) : ℝ)) := by
    have hcastN : (N : ℝ) = (s : ℝ) * (X : ℝ) + (u : ℝ) := by
      exact_mod_cast hN
    rw [hcastN]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hdR]
    ring
  let y : ℝ := ((X : ℝ) - (u : ℝ)) / ((s + 1 : ℕ) : ℝ)
  have hfloorShift :
      Int.floor ((X : ℝ) - y) = (X : ℤ) - Int.ceil y := by
    calc
      Int.floor ((X : ℝ) - y)
          = Int.floor ((X : ℝ) + (-y)) := by ring_nf
      _ = (X : ℤ) + Int.floor (-y) := by
        rw [Int.floor_natCast_add]
      _ = (X : ℤ) - Int.ceil y := by
        rw [Int.floor_neg]
        ring
  have hInt : (b : ℤ) = (X : ℤ) - Int.ceil y := by
    calc
      (b : ℤ) = Int.floor ((N : ℝ) / ((s + 1 : ℕ) : ℝ)) := hfloor.symm
      _ = Int.floor ((X : ℝ) - y) := by
        apply congrArg Int.floor
        simpa [y] using hreal
      _ = (X : ℤ) - Int.ceil y := hfloorShift
  change ((X - b : ℕ) : ℤ) = Int.ceil y
  rw [Nat.cast_sub hbX]
  omega

end DivisorF
