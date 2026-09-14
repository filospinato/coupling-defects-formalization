import DivisorF.CrossTypeTransport
import DivisorF.CumulativeBoundary
import DivisorF.MultiplicityCorollaries
import DivisorF.ShortIntervalTransfer
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Corollary 5.3: the prime-window bound

Every prime `p` in a window `[q, q+h]` has quotient type between
`s - Delta` and `s`, where `Delta = s - ⌊N/(q+h)⌋`.  Cross-type transport
(`DivisorF.CrossTypeTransport`) therefore gives

```text
D_N(p) >= D_N(q) - 2 Delta
```

for every one of them, and the cumulative boundary budget of Section 3 caps
their total defect at `2(s-1)`.  Dividing by the number `m` of window primes
and using integrality yields the manuscript's

```text
D_N(q) <= 2 Delta + ⌊2(s-1)/m⌋.
```

The arithmetic input — how many primes actually lie in `[q, q+h]` — is
isolated as the hypothesis `m + pi(q) = 1 + pi(q+h)`, the subtraction-free
form of `m = 1 + pi(q+h) - pi(q)`.  Nothing here estimates that count; that
is what a short-interval prime theorem is for, and Theorem 5.4 supplies one
as an explicit external interface.
-/

namespace DivisorF

open SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-! ### A single fibre never exceeds the same-type budget -/

/-- **Lemma 3.1, last inequality.**  `D_N(q) ≤ 2(s-1)`. -/
theorem fibreDefect_le_two_mul_pred (q : LargePrime N) :
    fibreDefect q ≤ ((2 * (q.quotientType - 1) : ℕ) : ℤ) := by
  classical
  have hmem : q ∈ typePrimes N q.quotientType := mem_typePrimes.mpr rfl
  have hocc : TypeOccupied N q.quotientType := ⟨q, hmem⟩
  have hpos : 0 < typeMultiplicity N q.quotientType :=
    typeMultiplicity_pos_iff_occupied.mpr hocc
  have hbudget := typeMultiplicity_mul_typeDefectNat_le hocc
  have hone : typeDefectNat hocc
      ≤ typeMultiplicity N q.quotientType * typeDefectNat hocc :=
    Nat.le_mul_of_pos_left _ hpos
  have hnat : typeDefectNat hocc ≤ 2 * (q.quotientType - 1) :=
    le_trans hone hbudget
  rw [fibreDefect_eq_typeDefect hocc hmem, ← coe_typeDefectNat hocc]
  exact_mod_cast hnat

/-- A fibre with `s = 1` is a single isolated vertex, so it costs nothing. -/
theorem fibreDefect_eq_zero_of_quotientType_le_one (q : LargePrime N)
    (h : q.quotientType ≤ 1) : fibreDefect q = 0 := by
  have hle := fibreDefect_le_two_mul_pred q
  have hzero : q.quotientType - 1 = 0 := by omega
  rw [hzero] at hle
  have hge := fibreDefect_nonneg q
  omega

/-! ### The window of large primes -/

/-- Large primes with value in `[a, a+h]`. -/
noncomputable def primeWindow (N a h : ℕ) : Finset (LargePrime N) := by
  classical
  exact Finset.univ.filter fun p => a ≤ p.val ∧ p.val ≤ a + h

@[simp]
theorem mem_primeWindow {a h : ℕ} {p : LargePrime N} :
    p ∈ primeWindow N a h ↔ a ≤ p.val ∧ p.val ≤ a + h := by
  classical
  simp [primeWindow]

theorem self_mem_primeWindow (q : LargePrime N) (h : ℕ) :
    q ∈ primeWindow N q.val h :=
  mem_primeWindow.mpr ⟨le_rfl, Nat.le_add_right _ _⟩

/-- Window primes have quotient type between `⌊N/(q+h)⌋` and `s`. -/
theorem primeWindow_quotientType_bounds (q : LargePrime N) {h : ℕ}
    {p : LargePrime N} (hp : p ∈ primeWindow N q.val h) :
    N / (q.val + h) ≤ p.quotientType ∧ p.quotientType ≤ q.quotientType := by
  obtain ⟨hlow, hhigh⟩ := mem_primeWindow.mp hp
  exact ⟨Nat.div_le_div_left hhigh p.pos, Nat.div_le_div_left hlow q.pos⟩

/-- Every window prime carries at least `D_N(q) - 2Δ` of defect. -/
theorem window_fibreDefect_lower_bound (q : LargePrime N) {h : ℕ}
    {p : LargePrime N} (hp : p ∈ primeWindow N q.val h) :
    fibreDefect q
        - 2 * ((q.quotientType : ℤ) - (N / (q.val + h) : ℕ))
      ≤ fibreDefect p := by
  obtain ⟨hlow, hhigh⟩ := primeWindow_quotientType_bounds q hp
  rcases eq_or_lt_of_le (mem_primeWindow.mp hp).1 with heq | hlt
  · have hpq : p = q := by
      cases p; cases q; simp_all
    subst hpq
    have : (0 : ℤ) ≤ 2 * ((p.quotientType : ℤ) - (N / (p.val + h) : ℕ)) := by
      have : ((N / (p.val + h) : ℕ) : ℤ) ≤ (p.quotientType : ℤ) := by exact_mod_cast hlow
      omega
    omega
  · have htrans := crossTypeDefectLipschitz q p hlt
    rw [abs_le] at htrans
    have h1 : ((N / (q.val + h) : ℕ) : ℤ) ≤ (p.quotientType : ℤ) := by exact_mod_cast hlow
    omega

/-! ### The window total is capped by the cumulative budget -/

theorem window_defect_sum_le (q : LargePrime N) (h : ℕ) :
    ∑ p ∈ primeWindow N q.val h, fibreDefect p
      ≤ ((2 * (q.quotientType - 1) : ℕ) : ℤ) := by
  classical
  set s := q.quotientType with hs
  set W₂ := (primeWindow N q.val h).filter fun p => 2 ≤ p.quotientType with hW₂
  have hsplit : ∑ p ∈ primeWindow N q.val h, fibreDefect p
      = ∑ p ∈ W₂, fibreDefect p := by
    rw [hW₂]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro p _ hne
    by_contra hlt
    exact hne (fibreDefect_eq_zero_of_quotientType_le_one p (by omega))
  have hsub : W₂ ⊆ cumulativeFibres N s := by
    intro p hp
    rw [hW₂, Finset.mem_filter] at hp
    exact mem_cumulativeFibres.mpr
      ⟨hp.2, (primeWindow_quotientType_bounds q hp.1).2⟩
  calc
    ∑ p ∈ primeWindow N q.val h, fibreDefect p
        = ∑ p ∈ W₂, fibreDefect p := hsplit
    _ ≤ ∑ p ∈ cumulativeFibres N s, fibreDefect p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => fibreDefect_nonneg p)
    _ = cumulativeDefectSum N s := rfl
    _ ≤ (cumulativeBoundaryCapacity s : ℤ) := cumulativeDefectSum_le
    _ = ((2 * (s - 1) : ℕ) : ℤ) := rfl

/-! ### Corollary 5.3 -/

/-- **Corollary 5.3, combinatorial core.**

`m` is the number of large primes in the window `[q, q+h]`. -/
theorem fibreDefect_le_window_bound (q : LargePrime N) (h : ℕ) :
    fibreDefect q
      ≤ 2 * ((q.quotientType : ℤ) - (N / (q.val + h) : ℕ))
        + ((2 * (q.quotientType - 1) / (primeWindow N q.val h).card : ℕ) : ℤ) := by
  classical
  set W := primeWindow N q.val h with hW
  set Δ : ℤ := (q.quotientType : ℤ) - (N / (q.val + h) : ℕ) with hΔ
  set C : ℕ := 2 * (q.quotientType - 1) with hC
  have hmpos : 0 < W.card :=
    Finset.card_pos.mpr ⟨q, self_mem_primeWindow q h⟩
  have hlower : ∀ p ∈ W, fibreDefect q - 2 * Δ ≤ fibreDefect p := by
    intro p hp
    exact window_fibreDefect_lower_bound q hp
  have hcard : (W.card : ℤ) * (fibreDefect q - 2 * Δ)
      ≤ ∑ p ∈ W, fibreDefect p := by
    calc
      (W.card : ℤ) * (fibreDefect q - 2 * Δ)
          = ∑ _p ∈ W, (fibreDefect q - 2 * Δ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ W, fibreDefect p := Finset.sum_le_sum hlower
  have htotal : (W.card : ℤ) * (fibreDefect q - 2 * Δ) ≤ (C : ℤ) :=
    le_trans hcard (window_defect_sum_le q h)
  -- integrality: the surplus is a natural number bounded by `C / m`
  have hquot : (fibreDefect q - 2 * Δ).toNat ≤ C / W.card := by
    rw [Nat.le_div_iff_mul_le hmpos]
    rcases le_or_gt (fibreDefect q - 2 * Δ) 0 with hneg | hpos
    · simp [Int.toNat_of_nonpos hneg]
    · have hcast : ((fibreDefect q - 2 * Δ).toNat : ℤ) = fibreDefect q - 2 * Δ :=
        Int.toNat_of_nonneg (le_of_lt hpos)
      have : ((fibreDefect q - 2 * Δ).toNat * W.card : ℕ) ≤ (C : ℕ) := by
        have hZ : (((fibreDefect q - 2 * Δ).toNat * W.card : ℕ) : ℤ) ≤ (C : ℤ) := by
          push_cast
          rw [hcast]
          linarith [htotal]
        exact_mod_cast hZ
      exact this
  have hself : fibreDefect q - 2 * Δ ≤ ((fibreDefect q - 2 * Δ).toNat : ℤ) :=
    Int.self_le_toNat _
  have hquotZ : (((fibreDefect q - 2 * Δ).toNat : ℕ) : ℤ) ≤ ((C / W.card : ℕ) : ℤ) := by
    exact_mod_cast hquot
  omega

/-! ### The manuscript's prime-counting form -/

/-- The window's large primes are exactly the ordinary primes of `[q, q+h]`. -/
theorem primeWindow_card_eq_succ_card_Ioc (q : LargePrime N) {h : ℕ}
    (hhN : q.val + h ≤ N) :
    (primeWindow N q.val h).card
      = 1 + ((Finset.Ioc q.val (q.val + h)).filter Nat.Prime).card := by
  classical
  have hval : (primeWindow N q.val h).image (fun p => p.val)
      = insert q.val (((Finset.Ioc q.val (q.val + h)).filter Nat.Prime)) := by
    ext n
    simp only [Finset.mem_image, mem_primeWindow, Finset.mem_insert,
      Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨p, ⟨hlow, hhigh⟩, rfl⟩
      rcases eq_or_lt_of_le hlow with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr ⟨⟨hlt, hhigh⟩, p.prime⟩
    · rintro (rfl | ⟨⟨hlt, hhigh⟩, hprime⟩)
      · exact ⟨q, ⟨le_rfl, Nat.le_add_right _ _⟩, rfl⟩
      · refine ⟨⟨n, hprime, ?_, le_trans hhigh hhN⟩, ⟨le_of_lt hlt, hhigh⟩, rfl⟩
        calc N < q.val * q.val := q.large
          _ ≤ n * n := Nat.mul_le_mul (le_of_lt hlt) (le_of_lt hlt)
  have hinj : Set.InjOn (fun p : LargePrime N => p.val) (primeWindow N q.val h) := by
    intro a _ b _ hab
    cases a; cases b; simp_all
  have hnotmem : q.val ∉ ((Finset.Ioc q.val (q.val + h)).filter Nat.Prime) := by
    simp
  calc
    (primeWindow N q.val h).card
        = ((primeWindow N q.val h).image (fun p => p.val)).card :=
          (Finset.card_image_of_injOn hinj).symm
    _ = (insert q.val (((Finset.Ioc q.val (q.val + h)).filter Nat.Prime))).card := by
          rw [hval]
    _ = 1 + ((Finset.Ioc q.val (q.val + h)).filter Nat.Prime).card := by
          rw [Finset.card_insert_of_notMem hnotmem]
          omega

/-- **Corollary 5.3, as the manuscript states it.**

With `m = 1 + pi(q+h) - pi(q)` — written subtraction-free as
`m + pi(q) = 1 + pi(q+h)` — and `Delta = s - ⌊N/(q+h)⌋`,

```text
D_N(q) ≤ 2 Delta + ⌊2(s-1)/m⌋.
```
-/
theorem primeWindowBound (q : LargePrime N) {h m : ℕ}
    (_hh : 0 < h) (hhN : q.val + h ≤ N)
    (hm : m + Nat.primeCounting q.val = 1 + Nat.primeCounting (q.val + h)) :
    fibreDefect q
      ≤ 2 * ((q.quotientType : ℤ) - (N / (q.val + h) : ℕ))
        + ((2 * (q.quotientType - 1) / m : ℕ) : ℤ) := by
  have hcount := primeCounting_add_card_filter_Ioc
    (a := q.val) (b := q.val + h) (Nat.le_add_right _ _)
  have hwin := primeWindow_card_eq_succ_card_Ioc q hhN
  have hmeq : m = (primeWindow N q.val h).card := by omega
  rw [hmeq]
  exact fibreDefect_le_window_bound q h

end DivisorF
