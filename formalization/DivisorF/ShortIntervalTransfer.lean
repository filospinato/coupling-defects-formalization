import DivisorF.ShortIntervalCones
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Theorem 5.2: from `SI(beta)` to quotient-interval prime richness

`DivisorF.ShortIntervalCones` carried the manuscript's own Steps 1–2 as the
interface `ShortIntervalQuotientRichness`: given `SI(beta)`, localise the exact
quotient interval inside a short interval, count the primes there, and conclude
`t_s(N) > 2(s-1)` uniformly on `s <= (N/s)^rho`. That was the last
project-owned gap in Section 5, and it is closed here.

The uniformity in `s` is carried by a single inequality. Writing `x = N/s`, the
range hypothesis `s <= x^rho` gives

`N = s * x <= x^rho * x = x^(1+rho)`,

so `x` is bounded below by a power of `N` and tends to infinity *uniformly*
over the whole range. Every estimate below is therefore stated as an eventual
property of the real parameter `x` alone, and transferred to `N` through that
one inequality.

Nothing analytic is assumed beyond `SI(beta)` itself, which stays a hypothesis:
this module proves the implication, not the short-interval theorem.
-/

namespace DivisorF

open Filter Asymptotics

/-! ### Counting primes in an interval -/

theorem primeCounting_eq_card_filter_Iic (n : ℕ) :
    Nat.primeCounting n = ((Finset.Iic n).filter Nat.Prime).card := by
  have h : Nat.primeCounting n = Nat.count Nat.Prime (n + 1) := rfl
  rw [h, Nat.count_eq_card_filter_range]
  congr 1
  ext y
  simp

/-- `pi(b) - pi(a)` counts the primes of `(a, b]`, in the subtraction-free form
that survives casting to `ℝ`. -/
theorem primeCounting_add_card_filter_Ioc {a b : ℕ} (hab : a ≤ b) :
    Nat.primeCounting a + ((Finset.Ioc a b).filter Nat.Prime).card
      = Nat.primeCounting b := by
  have hdisj : Disjoint ((Finset.Iic a).filter Nat.Prime)
      ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    have h1 := Finset.mem_Iic.mp (Finset.mem_filter.mp hy).1
    have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hy').1
    omega
  rw [primeCounting_eq_card_filter_Iic a, primeCounting_eq_card_filter_Iic b,
    ← Finset.Iic_union_Ioc_eq_Iic hab, Finset.filter_union,
    Finset.card_union_of_disjoint hdisj]

/-! ### The uniform estimates, as eventual properties of `x = N/s` -/

/-- The four inequalities Steps 1–2 need, all eventually true in `x`.

The second gives the inactive large-prime cutoff, the third the containment
`[X - X^beta, X] ⊆ (X_-, X]`, and the fourth the prime count exceeding `2s`. -/
theorem eventually_transfer_conditions {beta rho c : ℝ}
    (hb1 : (1 : ℝ) / 2 < beta) (_hb2 : beta < 1)
    (hrho : 0 < rho) (hrho2 : rho < 1 - beta) (hc : 0 < c) (T0 : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (4 ≤ x ∧ T0 + 1 ≤ x) ∧
        x ^ ((1 + rho) / 2) ≤ x / 2 - 1 ∧
        x ^ beta + 1 ≤ x ^ (1 - rho) / 2 ∧
        4 * Real.log x * x ^ rho ≤ c * x ^ beta := by
  have hbeta0 : 0 < beta := by linarith
  have hhalf : 0 < (1 - rho) / 2 := by linarith
  have hgap : 0 < 1 - rho - beta := by linarith
  have hbr : 0 < beta - rho := by linarith
  have hP1 : ∀ᶠ x : ℝ in atTop, (4 : ℝ) ≤ x ^ ((1 - rho) / 2) :=
    (tendsto_rpow_atTop hhalf).eventually_ge_atTop 4
  have hP2 : ∀ᶠ x : ℝ in atTop, (4 : ℝ) ≤ x ^ (1 - rho - beta) :=
    (tendsto_rpow_atTop hgap).eventually_ge_atTop 4
  have hP3 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (c / 4) * ‖x ^ (beta - rho)‖ :=
    (isLittleO_log_rpow_atTop hbr).def (by positivity)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (T0 + 1),
    hP1, hP2, hP3] with x hx4 hxT0 h1 h2 h3
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  refine ⟨⟨hx4, hxT0⟩, ?_, ?_, ?_⟩
  · have hsplit : x ^ ((1 + rho) / 2) * x ^ ((1 - rho) / 2) = x := by
      rw [← Real.rpow_add hx0,
        show (1 + rho) / 2 + (1 - rho) / 2 = (1 : ℝ) by ring, Real.rpow_one]
    have hpos : (0 : ℝ) < x ^ ((1 + rho) / 2) := Real.rpow_pos_of_pos hx0 _
    have hmul : x ^ ((1 + rho) / 2) * 4 ≤ x := by
      calc x ^ ((1 + rho) / 2) * 4
          ≤ x ^ ((1 + rho) / 2) * x ^ ((1 - rho) / 2) :=
            mul_le_mul_of_nonneg_left h1 hpos.le
        _ = x := hsplit
    linarith
  · have hone : (1 : ℝ) ≤ x ^ beta := Real.one_le_rpow hx1 hbeta0.le
    have hpos : (0 : ℝ) < x ^ beta := lt_of_lt_of_le one_pos hone
    have hsplit : x ^ (1 - rho - beta) * x ^ beta = x ^ (1 - rho) := by
      rw [← Real.rpow_add hx0]
      ring_nf
    have hmul : 4 * x ^ beta ≤ x ^ (1 - rho) := by
      calc 4 * x ^ beta ≤ x ^ (1 - rho - beta) * x ^ beta :=
            mul_le_mul_of_nonneg_right h2 hpos.le
        _ = x ^ (1 - rho) := hsplit
    linarith
  · have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hrpos : (0 : ℝ) < x ^ (beta - rho) := Real.rpow_pos_of_pos hx0 _
    have hbound : Real.log x ≤ (c / 4) * x ^ (beta - rho) := by
      rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hrpos.le] at h3
      exact h3
    have hsplit : x ^ (beta - rho) * x ^ rho = x ^ beta := by
      rw [← Real.rpow_add hx0]
      ring_nf
    have hrho_pos : (0 : ℝ) < x ^ rho := Real.rpow_pos_of_pos hx0 _
    calc 4 * Real.log x * x ^ rho
        ≤ 4 * ((c / 4) * x ^ (beta - rho)) * x ^ rho := by
          have h4 := mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_right h4 hrho_pos.le
      _ = c * (x ^ (beta - rho) * x ^ rho) := by ring
      _ = c * x ^ beta := by rw [hsplit]

/-! ### Steps 1–2 -/

set_option maxHeartbeats 1000000 in
-- One long linear proof: Steps 1 and 2 share a large hypothesis context, and
-- splitting it would mean threading two dozen real inequalities through an
-- auxiliary statement.
/-- **Theorem 5.2, Steps 1–2 (fixed-exponent transfer).**

`SI(beta)` implies exactly the prime-richness input that the Section 5 transfer
consumes: for every admissible `rho`, all sufficiently large `N`, and every
integer `s ≥ 2` with `s ≤ (N/s)^rho`, the large-prime cutoff is inactive on the
exact quotient interval `(⌊N/(s+1)⌋, ⌊N/s⌋]` and that interval carries more
than `2(s-1)` primes.

Step 1 is the containment `[X - X^beta, X] ⊆ (X_-, X]` together with the
inactive cutoff; Step 2 is the count. Both are uniform in `s`, through
`N ≤ x^(1+rho)`.

`SI(beta)` itself stays a hypothesis: no short-interval theorem is proved
here. -/
theorem shortIntervalQuotientRichness {beta : ℝ}
    (hb1 : (1 : ℝ) / 2 < beta) (hb2 : beta < 1) :
    ShortIntervalQuotientRichness beta := by
  intro hSI rho hrho hrho2
  have hbeta0 : 0 < beta := by linarith
  obtain ⟨c, hc, T0, hSIc⟩ := hSI
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (eventually_transfer_conditions hb1 hb2 hrho hrho2 hc T0)
  refine ⟨⌈(max x₀ 1) ^ (1 + rho)⌉₊ + 1, ?_⟩
  intro N hN s hs hrange
  -- elementary positivity
  have hspos : 0 < s := by omega
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have hs2R : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  set x : ℝ := (N : ℝ) / (s : ℝ) with hxdef
  have hxpos : 0 < x := div_pos hNR hsR
  have hNsx : (N : ℝ) = (s : ℝ) * x := by
    rw [hxdef]
    field_simp
  have hsx : (s : ℝ) ≤ x ^ rho := hrange
  have hxr : (0 : ℝ) < x ^ rho := Real.rpow_pos_of_pos hxpos rho
  -- the uniformity inequality `N ≤ x ^ (1 + rho)`
  have hNle : (N : ℝ) ≤ x ^ (1 + rho) := by
    rw [Real.rpow_add hxpos, Real.rpow_one, hNsx]
    nlinarith
  have hxx₁ : max x₀ 1 ≤ x := by
    by_contra hcon
    have hcon' : x < max x₀ 1 := not_le.mp hcon
    have h1 : x ^ (1 + rho) < (max x₀ 1) ^ (1 + rho) :=
      Real.rpow_lt_rpow hxpos.le hcon' (by linarith)
    have h3 : (max x₀ 1) ^ (1 + rho) ≤ ((⌈(max x₀ 1) ^ (1 + rho)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h4 : ((⌈(max x₀ 1) ^ (1 + rho)⌉₊ : ℕ) : ℝ) < (N : ℝ) := by
      have : (⌈(max x₀ 1) ^ (1 + rho)⌉₊ : ℕ) < N := by omega
      exact_mod_cast this
    linarith
  obtain ⟨⟨hx4, hxT0⟩, hC1, hC2, hC3⟩ := hx₀ x (le_trans (le_max_left _ _) hxx₁)
  -- the two endpoints of the exact quotient interval
  set X : ℕ := N / s with hXdef
  set Y : ℕ := N / (s + 1) with hYdef
  have hs1R : (0 : ℝ) < (s : ℝ) + 1 := by linarith
  have hXle : (X : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ hsR]
    have h : X * s ≤ N := by rw [hXdef]; exact Nat.div_mul_le_self N s
    exact_mod_cast h
  have hXgt : x - 1 < (X : ℝ) := by
    have hdm : s * X + N % s = N := by rw [hXdef]; exact Nat.div_add_mod N s
    have hmod : N % s < s := Nat.mod_lt N hspos
    have hnat : N < s * X + s := by omega
    have h : (N : ℝ) < (s : ℝ) * (X : ℝ) + (s : ℝ) := by exact_mod_cast hnat
    have hxlt : x < (X : ℝ) + 1 := by
      rw [hxdef, div_lt_iff₀ hsR]
      nlinarith
    linarith
  have hYle : (Y : ℝ) ≤ (N : ℝ) / ((s : ℝ) + 1) := by
    rw [le_div_iff₀ hs1R]
    have h : Y * (s + 1) ≤ N := by rw [hYdef]; exact Nat.div_mul_le_self N (s + 1)
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    linarith
  have hYgt : (N : ℝ) / ((s : ℝ) + 1) - 1 < (Y : ℝ) := by
    have hdm : (s + 1) * Y + N % (s + 1) = N := by
      rw [hYdef]; exact Nat.div_add_mod N (s + 1)
    have hmod : N % (s + 1) < s + 1 := Nat.mod_lt N (by omega)
    have hnat : N < (s + 1) * Y + (s + 1) := by omega
    have h : (N : ℝ) < ((s : ℝ) + 1) * (Y : ℝ) + ((s : ℝ) + 1) := by
      exact_mod_cast hnat
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hs1R]
    nlinarith
  -- Step 1a: the large-prime cutoff is inactive
  have hsqrt : Real.sqrt (N : ℝ) ≤ x ^ ((1 + rho) / 2) := by
    have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt (x ^ (1 + rho)) := Real.sqrt_le_sqrt hNle
    have h2 : Real.sqrt (x ^ (1 + rho)) = x ^ ((1 + rho) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
      ring_nf
    rwa [h2] at h1
  have hhalfle : x / 2 ≤ (N : ℝ) / ((s : ℝ) + 1) := by
    rw [hNsx, le_div_iff₀ hs1R]
    nlinarith
  have hcutoff : Real.sqrt (N : ℝ) < (Y : ℝ) := by linarith
  -- Step 1b: `[X - X^beta, X]` sits inside the exact quotient interval
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hXgt1 : (1 : ℝ) < (X : ℝ) := by linarith
  have hXbeta_pos : (0 : ℝ) < (X : ℝ) ^ beta := Real.rpow_pos_of_pos hXpos beta
  have hXbeta_le : (X : ℝ) ^ beta ≤ x ^ beta :=
    Real.rpow_le_rpow hXpos.le hXle hbeta0.le
  have hden : (s : ℝ) + 1 ≤ 2 * x ^ rho := by linarith
  have hxpow : x ^ (1 - rho) / 2 = x / (2 * x ^ rho) := by
    rw [Real.rpow_sub hxpos, Real.rpow_one]
    field_simp
  have hfrac : x / (2 * x ^ rho) ≤ x / ((s : ℝ) + 1) := by
    gcongr
  have hNs1' : (N : ℝ) / ((s : ℝ) + 1) = x - x / ((s : ℝ) + 1) := by
    rw [hNsx]
    field_simp
    ring
  have hYupper : (Y : ℝ) ≤ x - x ^ (1 - rho) / 2 := by
    rw [hxpow]
    linarith
  have hYcont : (Y : ℝ) ≤ (X : ℝ) - (X : ℝ) ^ beta := by linarith
  -- Step 2: the prime count
  have hT0X : T0 ≤ (X : ℝ) := by linarith
  have hSIX := hSIc (X : ℝ) hT0X
  rw [Nat.floor_natCast] at hSIX
  set M : ℕ := ⌊(X : ℝ) - (X : ℝ) ^ beta⌋₊ with hMdef
  have hYM : Y ≤ M := by
    rw [hMdef]
    exact Nat.le_floor hYcont
  have hMX : M ≤ X := by
    rw [hMdef]
    calc ⌊(X : ℝ) - (X : ℝ) ^ beta⌋₊ ≤ ⌊(X : ℝ)⌋₊ := Nat.floor_mono (by linarith)
      _ = X := Nat.floor_natCast X
  have hcount : Nat.primeCounting M + ((Finset.Ioc M X).filter Nat.Prime).card
      = Nat.primeCounting X := primeCounting_add_card_filter_Ioc hMX
  have hcountR : (Nat.primeCounting X : ℝ) - (Nat.primeCounting M : ℝ)
      = (((Finset.Ioc M X).filter Nat.Prime).card : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcount
    push_cast at h
    linarith
  have hsub : (Finset.Ioc M X).filter Nat.Prime ⊆ quotientIntervalPrimeValues N s := by
    intro p hp
    rw [mem_quotientIntervalPrimeValues, ← hXdef, ← hYdef]
    have h1 := Finset.mem_filter.mp hp
    have h2 := Finset.mem_Ioc.mp h1.1
    exact ⟨h1.2, by omega, by omega⟩
  have hcard_le : (((Finset.Ioc M X).filter Nat.Prime).card : ℝ)
      ≤ ((quotientIntervalPrimeValues N s).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  -- the analytic lower bound on `c * X^beta / log X`
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXgt1
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogle : Real.log (X : ℝ) ≤ Real.log x := Real.log_le_log hXpos hXle
  have hXhalf : x / 2 ≤ (X : ℝ) := by linarith
  have hxbeta_pos : (0 : ℝ) < x ^ beta := Real.rpow_pos_of_pos hxpos beta
  have hXbeta_ge : x ^ beta / 2 ≤ (X : ℝ) ^ beta := by
    have h1 : (x / 2) ^ beta ≤ (X : ℝ) ^ beta :=
      Real.rpow_le_rpow (by positivity) hXhalf hbeta0.le
    have h2 : (x / 2) ^ beta = x ^ beta / (2 : ℝ) ^ beta :=
      Real.div_rpow hxpos.le (by norm_num) beta
    have h3 : (2 : ℝ) ^ beta ≤ 2 := by
      calc (2 : ℝ) ^ beta ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hb2.le
        _ = 2 := Real.rpow_one 2
    have h4 : (0 : ℝ) < (2 : ℝ) ^ beta := Real.rpow_pos_of_pos (by norm_num) beta
    have h5 : x ^ beta / 2 ≤ x ^ beta / (2 : ℝ) ^ beta := by
      gcongr
    calc x ^ beta / 2 ≤ x ^ beta / (2 : ℝ) ^ beta := h5
      _ = (x / 2) ^ beta := h2.symm
      _ ≤ (X : ℝ) ^ beta := h1
  have hstep1 : x ^ beta / (2 * Real.log x) ≤ (X : ℝ) ^ beta / Real.log (X : ℝ) := by
    rw [show x ^ beta / (2 * Real.log x) = x ^ beta / 2 / Real.log x by ring]
    gcongr
  have hstep2 : 2 * (s : ℝ) ≤ c * (x ^ beta / (2 * Real.log x)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    have h : 4 * Real.log x * (s : ℝ) ≤ 4 * Real.log x * x ^ rho :=
      mul_le_mul_of_nonneg_left hsx (by linarith)
    nlinarith
  have hfinal : 2 * (s : ℝ) ≤ c * ((X : ℝ) ^ beta / Real.log (X : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hstep1 hc.le
    linarith
  have hcount_ge : 2 * (s : ℝ) ≤ ((quotientIntervalPrimeValues N s).card : ℝ) := by
    linarith
  have hcount_nat : 2 * s ≤ (quotientIntervalPrimeValues N s).card := by
    exact_mod_cast hcount_ge
  refine ⟨?_, by omega⟩
  change Real.sqrt (N : ℝ) < ((N / (s + 1) : ℕ) : ℝ)
  rw [← hYdef]
  exact hcutoff

/-- **Theorem 5.2, as the manuscript states it.**

Assume `SI(beta)` for some `1/2 < beta < 1` and fix `0 < rho < 1 - beta`. Then
all sufficiently large `N` have zero defect throughout `2 ≤ s ≤ (N/s)^rho`. -/
theorem eventuallyZeroDefectOn_quotientPowerRange_of_shortInterval
    {beta rho : ℝ} (hb1 : (1 : ℝ) / 2 < beta) (hb2 : beta < 1)
    (hrho : 0 < rho) (hrho2 : rho < 1 - beta)
    (hSI : ShortIntervalPrimeInput beta) :
    EventuallyZeroDefectOn (QuotientPowerRange rho) :=
  eventuallyZeroDefectOn_of_eventuallyPrimeRich
    (shortIntervalQuotientRichness hb1 hb2 hSI rho hrho hrho2)

/-- **Corollary 5.3, as the manuscript states it.**

Assume `SI(beta)`. Every fixed `0 < gamma < (1-beta)/(2-beta)` has eventual
zero defect on the cone `2 ≤ s ≤ N^gamma`. -/
theorem eventuallyZeroDefectOn_naturalPowerCone_of_shortInterval
    {beta gamma : ℝ} (hb1 : (1 : ℝ) / 2 < beta) (hb2 : beta < 1)
    (hgamma : 0 < gamma) (hcone : gamma < (1 - beta) / (2 - beta))
    (hSI : ShortIntervalPrimeInput beta) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) :=
  eventuallyZeroDefectOn_naturalPowerCone_of_fixedExponentPrimeRich
    hb1 hb2 hgamma hcone (shortIntervalQuotientRichness hb1 hb2 hSI)

/-! ### The manuscript's cones, with `SI(beta)` as the only hypothesis -/

/-- **Theorem 5.4.** Guth–Maynard's `SI(17/30)` is now the *only* hypothesis:
the manuscript's Steps 1–2 are supplied by `shortIntervalQuotientRichness`. -/
theorem eventuallyZeroDefect_guthMaynard_cone_of_shortInterval
    (hSI : ShortIntervalPrimeInput (17 / 30))
    {gamma : ℝ} (hgamma : 0 < gamma) (hcone : gamma < 13 / 43) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) :=
  eventuallyZeroDefect_guthMaynard_cone
    (shortIntervalQuotientRichness (by norm_num) (by norm_num)) hSI hgamma hcone

/-- **Corollary 5.8.** Li's `SI(13/25)` is now the only hypothesis. -/
theorem eventuallyZeroDefect_li_cone_of_shortInterval
    (hSI : ShortIntervalPrimeInput (13 / 25))
    {gamma : ℝ} (hgamma : 0 < gamma) (hcone : gamma < 12 / 37) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) :=
  eventuallyZeroDefect_li_cone
    (shortIntervalQuotientRichness (by norm_num) (by norm_num)) hSI hgamma hcone

/-- **Corollary 5.9.** The Riemann family `SI(beta)`, `1/2 < beta < 1`, is now
the only hypothesis. -/
theorem eventuallyZeroDefect_riemann_cone_of_shortInterval
    (hSI : ∀ beta : ℝ, 1 / 2 < beta → beta < 1 → ShortIntervalPrimeInput beta)
    {gamma : ℝ} (hgamma : 0 < gamma) (hcubic : gamma < 1 / 3) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) :=
  eventuallyZeroDefect_riemann_cone
    (fun _ hlow hhigh => shortIntervalQuotientRichness hlow hhigh) hSI hgamma hcubic

end DivisorF
