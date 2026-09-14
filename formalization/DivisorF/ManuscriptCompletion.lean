import DivisorF.UniformPointwiseBound
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Completion layer for the 10 September 2026 manuscript

This module closes the small but genuine paper-to-Lean coverage gaps left after
the main Section 5 formalization:

* the deleted tail in the cross-type complement comparison has **exactly**
  `s - t` vertices, as stated in the manuscript (the earlier formalization only
  needed and proved the upper bound);
* the transport-ramp inequality (5.3) is recorded in the same positive-part
  form as the manuscript;
* Corollary 5.3 is exposed with the manuscript's real window length `h`, not
  only with the integer window length used internally by `PrimeWindowBound`.

No external analytic input is used here.
-/

namespace DivisorF

open SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-! ## Exact cardinality of the deleted transport tail -/

/-- A canonical deleted tail vertex corresponding to an index
`k : Fin (s-t)`.  Its coefficient is `t+1+k`. -/
noncomputable def truncDeletedOfFin (q p : LargePrime N)
    (hqp : q.val ≠ p.val) (_hle : p.quotientType ≤ q.quotientType)
    (k : Fin (q.quotientType - p.quotientType)) :
    {w : {v : HVertex N // ¬ InFibre p v} // ¬ TruncKeep q p w} := by
  let a := p.quotientType + 1 + k.val
  have ha1 : 1 ≤ a := by
    dsimp [a]
    omega
  have hale : a ≤ q.quotientType := by
    have hk := k.isLt
    dsimp [a]
    omega
  have hvbounds := fibre_value_bounds q ha1 hale
  let v : HVertex N := HVertex.ofValue hvbounds.1 hvbounds.2
  have hvval : v.value = a * q.val := by
    simp [v]
  have hvq : InFibre q v := by
    rw [InFibre, hvval]
    exact ⟨a, by simp [Nat.mul_comm]⟩
  have hvp : ¬ InFibre p v := distinct_fibres_disjoint q p hqp hvq
  refine ⟨⟨v, hvp⟩, ?_⟩
  rw [not_truncKeep_iff]
  refine ⟨hvq, ?_⟩
  have hcoeff : fibreCoefficient q v = a := by
    unfold fibreCoefficient
    rw [hvval]
    exact Nat.mul_div_cancel _ q.pos
  rw [hcoeff]
  dsimp [a]
  omega

@[simp]
theorem truncDeletedOfFin_value (q p : LargePrime N)
    (hqp : q.val ≠ p.val) (hle : p.quotientType ≤ q.quotientType)
    (k : Fin (q.quotientType - p.quotientType)) :
    (truncDeletedOfFin q p hqp hle k).1.1.value
      = (p.quotientType + 1 + k.val) * q.val := by
  simp [truncDeletedOfFin]

/-- Distinct tail indices give distinct deleted vertices. -/
theorem truncDeletedOfFin_injective (q p : LargePrime N)
    (hqp : q.val ≠ p.val) (hle : p.quotientType ≤ q.quotientType) :
    Function.Injective (truncDeletedOfFin q p hqp hle) := by
  intro a b hab
  have hval := congrArg (fun w => w.1.1.value) hab
  rw [truncDeletedOfFin_value q p hqp hle a,
    truncDeletedOfFin_value q p hqp hle b] at hval
  have hcoeff : p.quotientType + 1 + a.val = p.quotientType + 1 + b.val :=
    Nat.eq_of_mul_eq_mul_right q.pos hval
  apply Fin.ext
  omega

/-- **The exact cardinality asserted in the proof of Theorem 5.2.**
The complement `R_{N,p}` loses exactly `s-t` vertices before becoming
isomorphic to `R_{N,q}`. -/
theorem card_truncDeleted_eq (q p : LargePrime N)
    (hqp : q.val ≠ p.val) (hle : p.quotientType ≤ q.quotientType) :
    Fintype.card {w : {v : HVertex N // ¬ InFibre p v} // ¬ TruncKeep q p w}
      = q.quotientType - p.quotientType := by
  apply le_antisymm (card_truncDeleted_le q p)
  have hinj := truncDeletedOfFin_injective q p hqp hle
  simpa using
    (Fintype.card_le_of_injective (truncDeletedOfFin q p hqp hle) hinj)

/-! ## The transport ramp (5.3) -/

/-- The manuscript's
`b_s(t) = (s-t) + F(s) - F(t)`, written for the actual types of `q` and `p`. -/
noncomputable def transportPenalty (q p : LargePrime N) : ℤ :=
  (q.quotientType : ℤ) - p.quotientType
    + (divisorPathPartitionNumber q.quotientType : ℤ)
    - divisorPathPartitionNumber p.quotientType

/-- Vertex sensitivity gives `0 ≤ b_s(t) ≤ 2(s-t)`. -/
theorem transportPenalty_bounds (q p : LargePrime N) (hqp : q.val ≤ p.val) :
    0 ≤ transportPenalty q p ∧
      transportPenalty q p ≤ 2 * ((q.quotientType : ℤ) - p.quotientType) := by
  have hle : p.quotientType ≤ q.quotientType := quotientType_le_of_val_le hqp
  have hF := abs_divisorPathPartitionNumber_sub_le hle
  rw [abs_le] at hF
  unfold transportPenalty
  omega

/-- One-sided cross-type transport in the exact `b_s(t)` form used before (5.3). -/
theorem fibreDefect_sub_transportPenalty_le (q p : LargePrime N)
    (hqp : q.val ≤ p.val) :
    fibreDefect q - transportPenalty q p ≤ fibreDefect p := by
  rcases eq_or_lt_of_le hqp with heq | hlt
  · have hpq : p = q := by
      cases p
      cases q
      simp_all
    subst p
    simp [transportPenalty]
  · have htransport := (crossTypeTransport q p hlt).2
    rw [abs_le] at htransport
    unfold transportPenalty
    omega

/-- The positive-part summand of the transport ramp. -/
noncomputable def transportRampTerm (q p : LargePrime N) : ℤ :=
  max 0 (fibreDefect q - transportPenalty q p)

/-- Each transport-ramp term is bounded by the actual defect at `p`. -/
theorem transportRampTerm_le_fibreDefect (q p : LargePrime N)
    (hqp : q.val ≤ p.val) :
    transportRampTerm q p ≤ fibreDefect p := by
  have hzero : (0 : ℤ) ≤ fibreDefect p := fibreDefect_nonneg p
  have htransport := fibreDefect_sub_transportPenalty_le q p hqp
  exact (max_le_iff).2 ⟨hzero, htransport⟩

/-- **Equation (5.3), the finite transport-ramp inequality.**

The finset `primeWindow N q.val (N-q.val)` represents the manuscript range
`q ≤ p ≤ N`: every element is already a `LargePrime N`, and `q ≤ N` gives
`q + (N-q) = N`. -/
theorem transportRampSum_le (q : LargePrime N) :
    ∑ p ∈ primeWindow N q.val (N - q.val), transportRampTerm q p
      ≤ ((2 * (q.quotientType - 1) : ℕ) : ℤ) := by
  have hterm : ∀ p ∈ primeWindow N q.val (N - q.val),
      transportRampTerm q p ≤ fibreDefect p := by
    intro p hp
    exact transportRampTerm_le_fibreDefect q p (mem_primeWindow.mp hp).1
  calc
    ∑ p ∈ primeWindow N q.val (N - q.val), transportRampTerm q p
        ≤ ∑ p ∈ primeWindow N q.val (N - q.val), fibreDefect p :=
          Finset.sum_le_sum hterm
    _ ≤ ((2 * (q.quotientType - 1) : ℕ) : ℤ) :=
      window_defect_sum_le q (N - q.val)

/-! ## Corollary 5.3 with a real window length -/

/-- **Corollary 5.3 in the manuscript's real-`h` form.**

The paper allows any real `0 < h ≤ N-q`.  Ordinary prime counting at the real
endpoint `q+h` is represented by `Nat.primeCounting ⌊q+h⌋₊`.  Internally we
apply the already-checked integer-window theorem at `H = ⌊h⌋₊`.  This loses
nothing in the prime count, while

`⌊N/(q+H)⌋ ≥ ⌊N/(q+h)⌋`,

so the manuscript's `Delta` is at least the integer-window `Delta`.

The hypothesis on `m` is the subtraction-free form of
`m = 1 + pi(q+h) - pi(q)`. -/
theorem primeWindowBound_real (q : LargePrime N) {h : ℝ} {m : ℕ}
    (hh : 0 < h)
    (hhN : h ≤ (N : ℝ) - (q.val : ℝ))
    (hm : m + Nat.primeCounting q.val =
      1 + Nat.primeCounting ⌊(q.val : ℝ) + h⌋₊) :
    fibreDefect q ≤
      2 * ((q.quotientType : ℤ) -
        ((⌊(N : ℝ) / ((q.val : ℝ) + h)⌋₊ : ℕ) : ℤ))
        + ((2 * (q.quotientType - 1) / m : ℕ) : ℤ) := by
  let H : ℕ := ⌊h⌋₊
  have hh0 : 0 ≤ h := le_of_lt hh
  have hHle : (H : ℝ) ≤ h := by
    dsimp [H]
    exact Nat.floor_le hh0
  have hsumNreal : (q.val : ℝ) + h ≤ (N : ℝ) := by
    linarith
  have hsumHreal : (q.val : ℝ) + (H : ℝ) ≤ (N : ℝ) := by
    linarith
  have hsumH : q.val + H ≤ N := by
    exact_mod_cast hsumHreal
  have hfloorSum : ⌊(q.val : ℝ) + h⌋₊ = q.val + H := by
    have hfa := Nat.floor_add_natCast (R := ℝ) hh0 q.val
    dsimp [H]
    simpa [add_comm] using hfa
  have hmH := hm
  rw [hfloorSum] at hmH
  have hcount := primeCounting_add_card_filter_Ioc
    (a := q.val) (b := q.val + H) (Nat.le_add_right _ _)
  have hwin := primeWindow_card_eq_succ_card_Ioc q hsumH
  have hcard : (primeWindow N q.val H).card = m := by
    rw [hwin]
    omega
  have hqR : 0 < (q.val : ℝ) := by
    exact_mod_cast q.pos
  have hdenHpos : 0 < (q.val : ℝ) + (H : ℝ) := by
    positivity
  have hdenle : (q.val : ℝ) + (H : ℝ) ≤ (q.val : ℝ) + h := by
    linarith
  have hNnonneg : 0 ≤ (N : ℝ) := by
    positivity
  have hquotle :
      (N : ℝ) / ((q.val : ℝ) + h) ≤
        (N : ℝ) / ((q.val : ℝ) + (H : ℝ)) := by
    exact div_le_div_of_nonneg_left hNnonneg hdenHpos hdenle
  have hfloorle := Nat.floor_mono hquotle
  have hfloorH :
      ⌊(N : ℝ) / ((q.val : ℝ) + (H : ℝ))⌋₊ = N / (q.val + H) := by
    simpa [Nat.cast_add] using
      (Nat.floor_div_eq_div (K := ℝ) N (q.val + H))
  rw [hfloorH] at hfloorle
  have hbound := fibreDefect_le_window_bound q H
  rw [hcard] at hbound
  have hfloorleZ :
      (((⌊(N : ℝ) / ((q.val : ℝ) + h)⌋₊ : ℕ) : ℤ)) ≤
        ((N / (q.val + H) : ℕ) : ℤ) := by
    exact_mod_cast hfloorle
  omega

end DivisorF
