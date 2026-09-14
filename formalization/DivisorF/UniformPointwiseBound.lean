import DivisorF.PrimeWindowBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Theorem 5.4: the uniform pointwise bound

The manuscript feeds the Baker--Harman--Pintz short-interval prime bound into
Corollary 5.3 at `h = q^(21/40)` and obtains

```text
D_N(q) << 1 + s q^(-19/40) << s^(21/40) <= N^(21/80).
```

`BakerHarmanPintzInput` is the published estimate, stated as an explicit
interface with its own threshold.  It is **not** proved here, and must not be:
`formalization/AGENTS.md` forbids re-proving published analytic number theory.
Everything else in the chain is the project's own deduction and is proved:

* the window `[q, q + ⌊q^(21/40)⌋]` lies inside `[q, N]` whenever `s ≥ 2`;
* `Delta = s - ⌊N/(q+h)⌋ ≤ (s+1) q^(-19/40) + 1`;
* `log q ≤ 20 q^(1/20)`, so the budget term is `O(s q^(-19/40))`;
* the explicit constant `4036/9` for `q` above the threshold;
* absorption of the finitely many smaller primes through `D_N(q) ≤ 2(s-1)`
  and `s < q`, which needs no case list because `s < q < q₀` bounds them all
  at once;
* the exponent algebra `s q^(-19/40) ≤ s^(21/40)` and `s^(21/40) ≤ N^(21/80)`.

So the manuscript's `<<` statements appear here with *explicit* absolute
constants, quantified exactly as the manuscript quantifies them, from the one
named published input.
-/

namespace DivisorF

open scoped BigOperators

/-! ### The published input -/

/-- **Baker--Harman--Pintz, as an external interface.**

For every integer `n ≥ q₀`,

```text
pi(n + n^(21/40)) - pi(n) ≥ (9/100) n^(21/40) / log n.
```

The manuscript cites this at `\cite[p.~562]{BakerHarmanPintz}`.  Since primes
are integers, counting them in `(n, n + n^(21/40)]` is the same as counting
them in `(n, n + ⌊n^(21/40)⌋]`, which is the form Corollary 5.3 consumes. -/
def BakerHarmanPintzInput (q₀ : ℕ) : Prop :=
  ∀ n : ℕ, q₀ ≤ n →
    (9 / 100 : ℝ) * (n : ℝ) ^ (21 / 40 : ℝ) / Real.log n
      ≤ (Nat.primeCounting (n + ⌊(n : ℝ) ^ (21 / 40 : ℝ)⌋₊) : ℝ)
          - (Nat.primeCounting n : ℝ)

/-! ### Elementary real estimates -/

/-- `log x ≤ 20 x^(1/20)`: the manuscript's `log q = O(q^(1/20))`, explicitly. -/
theorem log_le_twenty_mul_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 20 * x ^ (1 / 20 : ℝ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hpow : (0 : ℝ) < x ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hsplit : Real.log (x ^ (1 / 20 : ℝ)) = (1 / 20 : ℝ) * Real.log x :=
    Real.log_rpow hx0 _
  have hbound : Real.log (x ^ (1 / 20 : ℝ)) ≤ x ^ (1 / 20 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpow
  rw [hsplit] at hbound
  linarith

/-- `x^(1/20) / x^(21/40) = x^(-19/40)`. -/
theorem rpow_log_ratio {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 20 : ℝ) / x ^ (21 / 40 : ℝ) = x ^ (-19 / 40 : ℝ) := by
  rw [← Real.rpow_sub hx]
  norm_num

/-- The budget term is `O(s q^(-19/40))`. -/
theorem log_div_rpow_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x / x ^ (21 / 40 : ℝ) ≤ 20 * x ^ (-19 / 40 : ℝ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hden : (0 : ℝ) < x ^ (21 / 40 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [div_le_iff₀ hden]
  calc
    Real.log x ≤ 20 * x ^ (1 / 20 : ℝ) := log_le_twenty_mul_rpow hx
    _ = 20 * (x ^ (-19 / 40 : ℝ) * x ^ (21 / 40 : ℝ)) := by
        rw [← Real.rpow_add hx0]
        norm_num
    _ = 20 * x ^ (-19 / 40 : ℝ) * x ^ (21 / 40 : ℝ) := by ring

/-! ### The window length -/

/-- The manuscript's `h = q^(21/40)`, as an integer window length. -/
noncomputable def bhpWindow (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (21 / 40 : ℝ)⌋₊

theorem one_le_bhpWindow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ bhpWindow n := by
  have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have : (1 : ℝ) ≤ (n : ℝ) ^ (21 / 40 : ℝ) :=
    Real.one_le_rpow hx (by norm_num)
  exact Nat.le_floor (by exact_mod_cast this)

theorem bhpWindow_le {n : ℕ} (hn : 1 ≤ n) : bhpWindow n ≤ n := by
  have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (21 / 40 : ℝ) ≤ (n : ℝ) := by
    calc (n : ℝ) ^ (21 / 40 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = (n : ℝ) := Real.rpow_one _
  exact Nat.floor_le_of_le hpow |>.trans (by simp)

theorem bhpWindow_le_rpow (n : ℕ) :
    (bhpWindow n : ℝ) ≤ (n : ℝ) ^ (21 / 40 : ℝ) := by
  unfold bhpWindow
  by_cases hn : (0 : ℝ) ≤ (n : ℝ) ^ (21 / 40 : ℝ)
  · exact Nat.floor_le hn
  · exact absurd (Real.rpow_nonneg (Nat.cast_nonneg n) _) hn

/-! ### The quotient-width estimate -/

/-- **The manuscript's `Delta ≤ (s+1) q^(-19/40) + 1`.** -/
theorem delta_le_of_two_le {N : ℕ} (q : LargePrime N) (hs : 2 ≤ q.quotientType) :
    (q.quotientType : ℝ) - ((N / (q.val + bhpWindow q.val) : ℕ) : ℝ)
      ≤ ((q.quotientType : ℝ) + 1) * (q.val : ℝ) ^ (-19 / 40 : ℝ) + 1 := by
  set h := bhpWindow q.val with hh
  set Q : ℝ := (q.val : ℝ) with hQ
  set H : ℝ := (h : ℝ) with hH
  set Nr : ℝ := (N : ℝ) with hNr
  set S : ℝ := (q.quotientType : ℝ) with hS
  have hq2 : 2 ≤ q.val := q.prime.two_le
  have hQ2 : (2 : ℝ) ≤ Q := by rw [hQ]; exact_mod_cast hq2
  have hQpos : (0 : ℝ) < Q := by linarith
  have hH1 : (1 : ℝ) ≤ H := by
    have hw := one_le_bhpWindow (n := q.val) (by omega)
    rw [hH, hh]
    exact_mod_cast hw
  have hHpos : (0 : ℝ) < H := by linarith
  have hHQ : H ≤ Q ^ (21 / 40 : ℝ) := bhpWindow_le_rpow q.val
  -- `N/(q+h)` is a natural floor
  have hden_pos : 0 < q.val + h := by omega
  have hdenR : (0 : ℝ) < Q + H := by linarith
  have hdenCast : ((q.val + h : ℕ) : ℝ) = Q + H := by push_cast; ring
  have hfloor : Nr / (Q + H) < ((N / (q.val + h) : ℕ) : ℝ) + 1 := by
    have hnat : N < (N / (q.val + h) + 1) * (q.val + h) :=
      (Nat.div_lt_iff_lt_mul hden_pos).1 (Nat.lt_succ_self _)
    have hcast : Nr < (((N / (q.val + h) : ℕ) : ℝ) + 1) * (Q + H) := by
      have := (Nat.cast_lt (α := ℝ)).2 hnat
      push_cast at this
      linarith [this]
    rw [div_lt_iff₀ hdenR]
    linarith
  have hSle : S ≤ Nr / Q := by
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := q.val)
    simpa [hS, hNr, hQ, LargePrime.quotientType] using this
  -- the exact difference
  have hdiff : Nr / Q - Nr / (Q + H) = Nr * H / (Q * (Q + H)) := by
    field_simp
    ring
  have hNrpos : (0 : ℝ) ≤ Nr := by positivity
  have hle1 : Nr * H / (Q * (Q + H)) ≤ Nr * H / (Q * Q) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hle2 : Nr * H / (Q * Q) = (Nr / Q) * (H / Q) := by
    field_simp
  have hNrQ : Nr / Q < S + 1 := by
    have hnat : N < (q.quotientType + 1) * q.val :=
      (Nat.div_lt_iff_lt_mul q.pos).1 (Nat.lt_succ_self _)
    have hcast : Nr < (S + 1) * Q := by
      have := (Nat.cast_lt (α := ℝ)).2 hnat
      push_cast at this
      linarith [this]
    rw [div_lt_iff₀ hQpos]
    linarith
  have hHQratio : H / Q ≤ Q ^ (-19 / 40 : ℝ) := by
    have hmul : Q ^ (-19 / 40 : ℝ) * Q = Q ^ (21 / 40 : ℝ) := by
      calc Q ^ (-19 / 40 : ℝ) * Q
          = Q ^ (-19 / 40 : ℝ) * Q ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = Q ^ (-19 / 40 + 1 : ℝ) := (Real.rpow_add hQpos _ _).symm
        _ = Q ^ (21 / 40 : ℝ) := by norm_num
    have hpow : Q ^ (21 / 40 : ℝ) / Q = Q ^ (-19 / 40 : ℝ) := by
      rw [div_eq_iff (ne_of_gt hQpos)]
      exact hmul.symm
    calc H / Q ≤ Q ^ (21 / 40 : ℝ) / Q := by gcongr
      _ = Q ^ (-19 / 40 : ℝ) := hpow
  have hprod : (Nr / Q) * (H / Q) ≤ (S + 1) * Q ^ (-19 / 40 : ℝ) := by
    have hHQ0 : (0 : ℝ) ≤ H / Q := by positivity
    have hNrQ0 : (0 : ℝ) ≤ Nr / Q := by positivity
    calc (Nr / Q) * (H / Q) ≤ (S + 1) * (H / Q) := by
          apply mul_le_mul_of_nonneg_right (le_of_lt hNrQ) hHQ0
      _ ≤ (S + 1) * Q ^ (-19 / 40 : ℝ) := by
          have hS1 : (0 : ℝ) ≤ S + 1 := by positivity
          exact mul_le_mul_of_nonneg_left hHQratio hS1
  linarith [hSle, hfloor, hdiff, hle1, hle2, hprod]

/-! ### The explicit finite bound above the Baker--Harman--Pintz threshold -/

/-- **Theorem 5.4, explicit form (the manuscript's (5.7), simplified).**

Above the published threshold, and for `s ≥ 2`,

```text
D_N(q) ≤ 2 + (4036/9) s q^(-19/40).
```

The constant is explicit because `log q ≤ 20 q^(1/20)` is. -/
theorem fibreDefect_le_explicit_of_bhp {q₀ : ℕ} (hbhp : BakerHarmanPintzInput q₀)
    {N : ℕ} (q : LargePrime N) (hq₀ : q₀ ≤ q.val) (hs : 2 ≤ q.quotientType) :
    (fibreDefect q : ℝ)
      ≤ 2 + (4036 / 9) * (q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ) := by
  classical
  have hq2 : 2 ≤ q.val := q.prime.two_le
  have hh1 : 1 ≤ bhpWindow q.val := one_le_bhpWindow (by omega)
  have hhq : bhpWindow q.val ≤ q.val := bhpWindow_le (by omega)
  have h2q : 2 * q.val ≤ N := (Nat.le_div_iff_mul_le q.pos).1 hs
  have hhN : q.val + bhpWindow q.val ≤ N := by omega
  -- the window prime count
  set m : ℕ :=
    1 + ((Finset.Ioc q.val (q.val + bhpWindow q.val)).filter Nat.Prime).card with hmdef
  have hcount := primeCounting_add_card_filter_Ioc
    (a := q.val) (b := q.val + bhpWindow q.val) (Nat.le_add_right _ _)
  have hm : m + Nat.primeCounting q.val
      = 1 + Nat.primeCounting (q.val + bhpWindow q.val) := by omega
  have hbound := primeWindowBound q (by omega : 0 < bhpWindow q.val) hhN hm
  -- real abbreviations
  have hQ2 : (2 : ℝ) ≤ (q.val : ℝ) := by exact_mod_cast hq2
  have hQpos : (0 : ℝ) < (q.val : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ (q.val : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log (q.val : ℝ) := Real.log_pos (by linarith)
  have hPpos : (0 : ℝ) < (q.val : ℝ) ^ (21 / 40 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hEnonneg : (0 : ℝ) ≤ (q.val : ℝ) ^ (-19 / 40 : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos hQpos _)
  have hS2 : (2 : ℝ) ≤ (q.quotientType : ℝ) := by exact_mod_cast hs
  -- the Baker--Harman--Pintz lower bound for `m`
  have hK : (9 / 100 : ℝ) * (q.val : ℝ) ^ (21 / 40 : ℝ) / Real.log (q.val : ℝ)
      ≤ (m : ℝ) := by
    have hbhpq := hbhp q.val hq₀
    have hcard : (Nat.primeCounting (q.val + bhpWindow q.val) : ℝ)
        - (Nat.primeCounting q.val : ℝ)
        = ((((Finset.Ioc q.val (q.val + bhpWindow q.val)).filter Nat.Prime).card : ℕ) : ℝ) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [show ⌊(q.val : ℝ) ^ (21 / 40 : ℝ)⌋₊ = bhpWindow q.val from rfl, hcard] at hbhpq
    have hmR : ((((Finset.Ioc q.val (q.val + bhpWindow q.val)).filter Nat.Prime).card : ℕ) : ℝ)
        ≤ (m : ℝ) := by
      rw [hmdef]
      push_cast
      linarith
    linarith
  have hKpos : (0 : ℝ)
      < (9 / 100 : ℝ) * (q.val : ℝ) ^ (21 / 40 : ℝ) / Real.log (q.val : ℝ) := by
    positivity
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hKpos hK
  -- the budget term
  have hsub : ((q.quotientType - 1 : ℕ) : ℝ) = (q.quotientType : ℝ) - 1 := by
    have hone : (1 : ℕ) ≤ q.quotientType := by omega
    exact_mod_cast Nat.cast_sub (R := ℝ) hone
  have hnum : ((2 * (q.quotientType - 1) : ℕ) : ℝ) = 2 * ((q.quotientType : ℝ) - 1) := by
    rw [Nat.cast_mul, hsub]
    norm_num
  have hbudget : ((2 * (q.quotientType - 1) / m : ℕ) : ℝ)
      ≤ (4000 / 9) * ((q.quotientType : ℝ) - 1) * (q.val : ℝ) ^ (-19 / 40 : ℝ) := by
    have h1 : ((2 * (q.quotientType - 1) / m : ℕ) : ℝ)
        ≤ ((2 * (q.quotientType - 1) : ℕ) : ℝ) / (m : ℝ) := Nat.cast_div_le
    rw [hnum] at h1
    have h2 : 2 * ((q.quotientType : ℝ) - 1) / (m : ℝ)
        ≤ 2 * ((q.quotientType : ℝ) - 1)
          / ((9 / 100 : ℝ) * (q.val : ℝ) ^ (21 / 40 : ℝ) / Real.log (q.val : ℝ)) :=
      div_le_div_of_nonneg_left (by linarith) hKpos hK
    have h3 : 2 * ((q.quotientType : ℝ) - 1)
          / ((9 / 100 : ℝ) * (q.val : ℝ) ^ (21 / 40 : ℝ) / Real.log (q.val : ℝ))
        = (200 / 9) * ((q.quotientType : ℝ) - 1)
            * (Real.log (q.val : ℝ) / (q.val : ℝ) ^ (21 / 40 : ℝ)) := by
      field_simp
      ring
    have h4 : Real.log (q.val : ℝ) / (q.val : ℝ) ^ (21 / 40 : ℝ)
        ≤ 20 * (q.val : ℝ) ^ (-19 / 40 : ℝ) := log_div_rpow_le hQ1
    have h5 : (200 / 9) * ((q.quotientType : ℝ) - 1)
          * (Real.log (q.val : ℝ) / (q.val : ℝ) ^ (21 / 40 : ℝ))
        ≤ (200 / 9) * ((q.quotientType : ℝ) - 1)
            * (20 * (q.val : ℝ) ^ (-19 / 40 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left h4
      linarith
    linarith
  -- the quotient-width term
  have hdelta := delta_le_of_two_le q hs
  -- assemble
  have hboundR : (fibreDefect q : ℝ)
      ≤ 2 * ((q.quotientType : ℝ) - ((N / (q.val + bhpWindow q.val) : ℕ) : ℝ))
        + ((2 * (q.quotientType - 1) / m : ℕ) : ℝ) := by
    have hcast := (Int.cast_le (R := ℝ)).2 hbound
    rw [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, Int.cast_natCast] at hcast
    norm_num at hcast
    exact hcast
  have hEexp : (0 : ℝ) ≤ (q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ) := by
    positivity
  nlinarith [hboundR, hdelta, hbudget, hEnonneg, hS2]


/-! ### Exponent algebra -/

/-- Negative powers reverse the order of the base. -/
theorem rpow_neg_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-19 / 40 : ℝ) ≤ a ^ (-19 / 40 : ℝ) := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hneg : (-19 / 40 : ℝ) = -(19 / 40 : ℝ) := by norm_num
  rw [hneg, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have hpa : (0 : ℝ) < a ^ (19 / 40 : ℝ) := Real.rpow_pos_of_pos ha _
  have hle : a ^ (19 / 40 : ℝ) ≤ b ^ (19 / 40 : ℝ) :=
    Real.rpow_le_rpow ha.le hab (by norm_num)
  gcongr

/-- `x * x^(-19/40) = x^(21/40)`. -/
theorem mul_rpow_neg_eq {x : ℝ} (hx : 0 < x) :
    x * x ^ (-19 / 40 : ℝ) = x ^ (21 / 40 : ℝ) := by
  calc x * x ^ (-19 / 40 : ℝ)
      = x ^ (1 : ℝ) * x ^ (-19 / 40 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ (1 + (-19 / 40) : ℝ) := (Real.rpow_add hx _ _).symm
    _ = x ^ (21 / 40 : ℝ) := by norm_num

/-- `x^(-19/40) * x^(19/40) = 1`. -/
theorem rpow_neg_mul_rpow {x : ℝ} (hx : 0 < x) :
    x ^ (-19 / 40 : ℝ) * x ^ (19 / 40 : ℝ) = 1 := by
  rw [← Real.rpow_add hx]
  norm_num

/-! ### Theorem 5.4 -/

/-- **Theorem 5.4, first inequality.**

```text
D_N(q) ≤ C (1 + s q^(-19/40))
```

with an absolute constant, uniformly over every `N` and every large prime `q`.
Small primes need no case list: `D_N(q) ≤ 2(s-1)` and `s < q < q₀` bound them
all at once. -/
theorem fibreDefect_le_uniform_of_bhp {q₀ : ℕ} (hbhp : BakerHarmanPintzInput q₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (q : LargePrime N),
      (fibreDefect q : ℝ)
        ≤ C * (1 + (q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ)) := by
  refine ⟨max (4036 / 9) (2 * ((q₀ : ℝ) + 1) ^ (19 / 40 : ℝ)), ?_, ?_⟩
  · have : (0 : ℝ) < 4036 / 9 := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  intro N q
  have hq2 : 2 ≤ q.val := q.prime.two_le
  have hQpos : (0 : ℝ) < (q.val : ℝ) := by
    have : (2 : ℝ) ≤ (q.val : ℝ) := by exact_mod_cast hq2
    linarith
  have hEpos : (0 : ℝ) < (q.val : ℝ) ^ (-19 / 40 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hSnonneg : (0 : ℝ) ≤ (q.quotientType : ℝ) := by positivity
  have hprod : (0 : ℝ) ≤ (q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ) := by
    positivity
  have hCbig : (0 : ℝ) ≤ max (4036 / 9) (2 * ((q₀ : ℝ) + 1) ^ (19 / 40 : ℝ)) := by
    have : (0 : ℝ) < 4036 / 9 := by norm_num
    exact le_trans this.le (le_max_left _ _)
  rcases le_or_gt q₀ q.val with hq₀ | hq₀
  · rcases le_or_gt q.quotientType 1 with hs1 | hs2
    · rw [fibreDefect_eq_zero_of_quotientType_le_one q hs1]
      simp only [Int.cast_zero]
      have : (0 : ℝ) ≤ 1 + (q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ) := by
        linarith
      positivity
    · have hexp := fibreDefect_le_explicit_of_bhp hbhp q hq₀ hs2
      have hC0 : (4036 / 9 : ℝ)
          ≤ max (4036 / 9) (2 * ((q₀ : ℝ) + 1) ^ (19 / 40 : ℝ)) := le_max_left _ _
      nlinarith [hexp, hprod, hC0]
  · -- `q < q₀`: the same-type budget already bounds the defect
    have hbudget : (fibreDefect q : ℝ) ≤ 2 * (q.quotientType : ℝ) := by
      have hle := fibreDefect_le_two_mul_pred q
      have hcast : ((2 * (q.quotientType - 1) : ℕ) : ℝ) ≤ 2 * (q.quotientType : ℝ) := by
        have : (2 * (q.quotientType - 1) : ℕ) ≤ 2 * q.quotientType := by omega
        calc ((2 * (q.quotientType - 1) : ℕ) : ℝ)
            ≤ ((2 * q.quotientType : ℕ) : ℝ) := by exact_mod_cast this
          _ = 2 * (q.quotientType : ℝ) := by push_cast; ring
      have := (Int.cast_le (R := ℝ)).2 hle
      rw [Int.cast_natCast] at this
      linarith
    have hq₀pos : (0 : ℝ) < (q₀ : ℝ) + 1 := by positivity
    have hqle : (q.val : ℝ) ≤ (q₀ : ℝ) + 1 := by
      have : q.val ≤ q₀ := le_of_lt hq₀
      have : (q.val : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast this
      linarith
    have hpow : (q.val : ℝ) ^ (19 / 40 : ℝ) ≤ ((q₀ : ℝ) + 1) ^ (19 / 40 : ℝ) :=
      Real.rpow_le_rpow hQpos.le hqle (by norm_num)
    have hone : (q.val : ℝ) ^ (-19 / 40 : ℝ) * (q.val : ℝ) ^ (19 / 40 : ℝ) = 1 :=
      rpow_neg_mul_rpow hQpos
    have hkey : (q.quotientType : ℝ)
        ≤ ((q₀ : ℝ) + 1) ^ (19 / 40 : ℝ)
            * ((q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ)) := by
      nlinarith [hSnonneg, hEpos, hpow, hone]
    have hC1 : 2 * ((q₀ : ℝ) + 1) ^ (19 / 40 : ℝ)
        ≤ max (4036 / 9) (2 * ((q₀ : ℝ) + 1) ^ (19 / 40 : ℝ)) := le_max_right _ _
    nlinarith [hbudget, hkey, hprod, hC1, hCbig]

/-- **Theorem 5.4, second inequality.**

```text
D_N(q) ≤ C' s^(21/40).
```
-/
theorem fibreDefect_le_quotient_power_of_bhp {q₀ : ℕ}
    (hbhp : BakerHarmanPintzInput q₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (q : LargePrime N),
      (fibreDefect q : ℝ) ≤ C * (q.quotientType : ℝ) ^ (21 / 40 : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := fibreDefect_le_uniform_of_bhp hbhp
  refine ⟨2 * C, by linarith, ?_⟩
  intro N q
  have hq2 : 2 ≤ q.val := q.prime.two_le
  have hs1 : 1 ≤ q.quotientType := Nat.one_le_div_iff q.pos |>.2 q.le_N
  have hSpos : (0 : ℝ) < (q.quotientType : ℝ) := by exact_mod_cast hs1
  have hS1 : (1 : ℝ) ≤ (q.quotientType : ℝ) := by exact_mod_cast hs1
  have hQpos : (0 : ℝ) < (q.val : ℝ) := by positivity
  have hSQ : (q.quotientType : ℝ) ≤ (q.val : ℝ) := by
    have := quotientType_lt_val q
    have : q.quotientType ≤ q.val := le_of_lt this
    exact_mod_cast this
  -- `1 ≤ s^(21/40)`
  have hone : (1 : ℝ) ≤ (q.quotientType : ℝ) ^ (21 / 40 : ℝ) :=
    Real.one_le_rpow hS1 (by norm_num)
  -- `s q^(-19/40) ≤ s^(21/40)`
  have hstep : (q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ)
      ≤ (q.quotientType : ℝ) ^ (21 / 40 : ℝ) := by
    have hmono : (q.val : ℝ) ^ (-19 / 40 : ℝ)
        ≤ (q.quotientType : ℝ) ^ (-19 / 40 : ℝ) := rpow_neg_antitone hSpos hSQ
    calc (q.quotientType : ℝ) * (q.val : ℝ) ^ (-19 / 40 : ℝ)
        ≤ (q.quotientType : ℝ) * (q.quotientType : ℝ) ^ (-19 / 40 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hmono hSpos.le
      _ = (q.quotientType : ℝ) ^ (21 / 40 : ℝ) := mul_rpow_neg_eq hSpos
  have hmain := hC N q
  nlinarith [hmain, hone, hstep, hCpos]

/-- **Theorem 5.4, ambient form.**

```text
max_{q} D_N(q) ≤ C' N^(21/80),
```

because `s^2 ≤ s q ≤ N`. -/
theorem fibreDefect_le_ambient_power_of_bhp {q₀ : ℕ}
    (hbhp : BakerHarmanPintzInput q₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (q : LargePrime N),
      (fibreDefect q : ℝ) ≤ C * (N : ℝ) ^ (21 / 80 : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := fibreDefect_le_quotient_power_of_bhp hbhp
  refine ⟨C, hCpos, ?_⟩
  intro N q
  have hs1 : 1 ≤ q.quotientType := Nat.one_le_div_iff q.pos |>.2 q.le_N
  have hsq : q.quotientType * q.quotientType ≤ N := by
    have h1 : q.quotientType * q.val ≤ N := Nat.div_mul_le_self N q.val
    have h2 : q.quotientType ≤ q.val := le_of_lt (quotientType_lt_val q)
    calc q.quotientType * q.quotientType ≤ q.quotientType * q.val :=
          Nat.mul_le_mul_left _ h2
      _ ≤ N := h1
  have hSnonneg : (0 : ℝ) ≤ (q.quotientType : ℝ) := by positivity
  have hsqR : (q.quotientType : ℝ) * (q.quotientType : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hsq
  -- `s ≤ N^(1/2)`
  have hhalf : (q.quotientType : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hsq2 : ((q.quotientType : ℝ) ^ (2 : ℕ)) ≤ (N : ℝ) := by
      rw [pow_two]; exact hsqR
    have hmono : ((q.quotientType : ℝ) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)
        ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hsq2 (by norm_num)
    have hid : ((q.quotientType : ℝ) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)
        = (q.quotientType : ℝ) := by
      rw [← Real.rpow_natCast (q.quotientType : ℝ) 2, ← Real.rpow_mul hSnonneg]
      norm_num
    rwa [hid] at hmono
  have hpow : (q.quotientType : ℝ) ^ (21 / 40 : ℝ) ≤ (N : ℝ) ^ (21 / 80 : ℝ) := by
    have hmono : (q.quotientType : ℝ) ^ (21 / 40 : ℝ)
        ≤ ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (21 / 40 : ℝ) :=
      Real.rpow_le_rpow hSnonneg hhalf (by norm_num)
    have hid : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (21 / 40 : ℝ) = (N : ℝ) ^ (21 / 80 : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num
    rwa [hid] at hmono
  have hmain := hC N q
  nlinarith [hmain, hpow, hCpos]


end DivisorF
