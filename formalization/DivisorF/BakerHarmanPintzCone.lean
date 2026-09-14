import DivisorF.UniformPointwiseBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Theorem 6.4 and Corollary 6.5: the Baker--Harman--Pintz zero-defect cone

The 10 September 2026 manuscript instantiates the generic cone
`gamma < (1-beta)/(2-beta)` of Corollary 6.3 at the Baker--Harman--Pintz
exponent: `SI(beta)` holds for every fixed `21/40 < beta < 1`, and

```text
(1 - 21/40)/(2 - 21/40) = 19/59.
```

That is Theorem 6.4, and Corollary 6.5 is the fixed-type consequence.

`DivisorF.ShortIntervalCones` already carries `coneExponent` and the generic
transfer; what this module adds is the arithmetic at `21/40`, the family
statement for `beta` just above it, and the fixed-type corollary.

**What stays outside.** `SI(beta)` for `beta > 21/40` is the published
Baker--Harman--Pintz theorem plus a routine packing of consecutive
`x^(21/40)`-windows into one `T^beta`-window.  Neither is proved here: the
first is external literature, and the second is an analytic manipulation of
that external input rather than a project-original result.  Both enter as the
hypothesis `hSI`.
-/

namespace DivisorF

open Filter

/-! ### The exponent -/

/-- **The Baker--Harman--Pintz cone exponent.** `beta = 21/40` gives `19/59`. -/
theorem coneExponent_bakerHarmanPintz : coneExponent (21 / 40) = 19 / 59 := by
  unfold coneExponent
  norm_num

/-- Every `gamma < 19/59` is already covered by some admissible
`beta > 21/40`.

This is the exact content of "for every fixed `eps > 0`" in Theorem 6.4:
`coneExponent` is strictly decreasing, so it approaches `19/59` from below as
`beta` decreases to `21/40`. -/
theorem exists_beta_of_lt_bhp {gamma : ℝ} (hgamma : 0 < gamma)
    (hbhp : gamma < 19 / 59) :
    ∃ beta : ℝ, 21 / 40 < beta ∧ beta < 1 ∧ gamma < coneExponent beta := by
  set g : ℝ := (gamma + 19 / 59) / 2 with hgdef
  have hg_pos : 0 < g := by positivity
  have hg_lt : g < 19 / 59 := by simp only [hgdef]; linarith
  have hg_gt : gamma < g := by simp only [hgdef]; linarith
  have hg_ne : (1 : ℝ) - g ≠ 0 := by
    have : g < 1 := by linarith
    linarith
  refine ⟨(1 - 2 * g) / (1 - g), ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 1 - g)]
    linarith
  · rw [div_lt_one (by linarith : (0 : ℝ) < 1 - g)]
    linarith
  · have hcone : coneExponent ((1 - 2 * g) / (1 - g)) = g := by
      unfold coneExponent
      field_simp
      ring
    rw [hcone]
    exact hg_gt

/-! ### Theorem 6.4 -/

/-- **Theorem 6.4, as the implication it is.**

Given `SI(beta)` for every fixed `beta` in `(21/40, 1)` — which is what
Baker--Harman--Pintz supplies, after packing consecutive short intervals —
every fixed `0 < gamma < 19/59` has eventual zero defect on the cone
`2 ≤ s ≤ N^gamma`.

The exponent `19/59` is machine-checked here as `coneExponent (21/40)`;
`SI(beta)` itself is the published input and is not proved. -/
theorem eventuallyZeroDefect_bakerHarmanPintz_cone_of_shortInterval
    (hSI : ∀ beta : ℝ, 21 / 40 < beta → beta < 1 → ShortIntervalPrimeInput beta)
    {gamma : ℝ} (hgamma : 0 < gamma) (hcone : gamma < 19 / 59) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) := by
  obtain ⟨beta, hlow, hhigh, hbeta⟩ := exists_beta_of_lt_bhp hgamma hcone
  have hhalf : (1 : ℝ) / 2 < beta := by linarith
  exact eventuallyZeroDefectOn_naturalPowerCone_of_shortInterval
    hhalf hhigh hgamma hbeta (hSI beta hlow hhigh)

/-- **Theorem 6.4, second display.**

`q ≥ N^(1-gamma)` forces `s = ⌊N/q⌋ ≤ N^gamma`, so the cone statement in `s`
restates as one in `q`.  With `gamma = 19/59 - eps` the exponent is
`40/59 + eps`, since `19/59 + 40/59 = 1`. -/
theorem fibreDefect_eq_zero_of_cone_and_prime_lower {gamma : ℝ}
    (hcone : EventuallyZeroDefectOn (NaturalPowerCone gamma)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q : LargePrime N,
      (N : ℝ) ^ (1 - gamma) ≤ (q.val : ℝ) → fibreDefect q = 0 := by
  obtain ⟨N₁, hN₁⟩ := hcone
  refine ⟨max N₁ 2, ?_⟩
  intro N hN q hq
  rcases le_or_gt q.quotientType 1 with hs1 | hs2
  · exact fibreDefect_eq_zero_of_quotientType_le_one q hs1
  · have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      linarith
    have hpowpos : (0 : ℝ) < (N : ℝ) ^ (1 - gamma) := Real.rpow_pos_of_pos hNpos _
    have hqpos : (0 : ℝ) < (q.val : ℝ) := lt_of_lt_of_le hpowpos hq
    have hsplit : (N : ℝ) ^ gamma * (N : ℝ) ^ (1 - gamma) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      simp
    have hdiv : (N : ℝ) / (N : ℝ) ^ (1 - gamma) = (N : ℝ) ^ gamma := by
      rw [div_eq_iff (ne_of_gt hpowpos)]
      exact hsplit.symm
    have hs : (q.quotientType : ℝ) ≤ (N : ℝ) ^ gamma := by
      have h1 : (q.quotientType : ℝ) ≤ (N : ℝ) / (q.val : ℝ) := by
        simpa [LargePrime.quotientType] using
          Nat.cast_div_le (α := ℝ) (m := N) (n := q.val)
      have h2 : (N : ℝ) / (q.val : ℝ) ≤ (N : ℝ) / (N : ℝ) ^ (1 - gamma) :=
        div_le_div_of_nonneg_left hNpos.le hpowpos hq
      rw [hdiv] at h2
      linarith
    have hzero := hN₁ N (le_trans (le_max_left _ _) hN) q.quotientType hs2 hs
    have hmem : q ∈ typePrimes N q.quotientType := mem_typePrimes.mpr rfl
    have hocc : TypeOccupied N q.quotientType := ⟨q, hmem⟩
    rw [paperTypeDefect_eq_of_occupied hocc] at hzero
    rw [fibreDefect_eq_typeDefect hocc hmem]
    exact hzero


/-! ### Corollary 6.5 -/

/-- Quotient types `s ≤ 1` never carry defect: a type-`1` fibre is a single
isolated vertex, and a type-`0` class is empty. -/
theorem paperTypeDefect_eq_zero_of_le_one (N : ℕ) {s : ℕ} (hs : s ≤ 1) :
    paperTypeDefect N s = 0 := by
  classical
  by_cases hocc : TypeOccupied N s
  · rw [paperTypeDefect_eq_of_occupied hocc]
    unfold typeDefect
    apply fibreDefect_eq_zero_of_quotientType_le_one
    rw [mem_typePrimes.mp (typeRepresentative_mem hocc)]
    exact hs
  · exact paperTypeDefect_eq_zero_of_not_occupied hocc

/-- A positive power of `N` eventually dominates any fixed integer. -/
theorem exists_threshold_le_rpow {gamma : ℝ} (hgamma : 0 < gamma) (s : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (s : ℝ) ≤ (N : ℝ) ^ gamma := by
  have h := (tendsto_rpow_atTop hgamma).eventually_ge_atTop (s : ℝ)
  rw [Filter.eventually_atTop] at h
  obtain ⟨x₀, hx₀⟩ := h
  refine ⟨⌈x₀⌉₊, ?_⟩
  intro N hN
  have hxN : x₀ ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil x₀) (by exact_mod_cast hN)
  exact hx₀ _ hxN

/-- **Corollary 6.5 (fixed quotient types).**

For every fixed integer `s`, `d_s(N) = 0` for all sufficiently large `N`.
The case `s = 1` is immediate; for `s ≥ 2` the cone of Theorem 6.4 eventually
contains `s`. -/
theorem eventuallyZeroDefect_fixedType_of_cone {gamma : ℝ} (hgamma : 0 < gamma)
    (hcone : EventuallyZeroDefectOn (NaturalPowerCone gamma)) (s : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → paperTypeDefect N s = 0 := by
  rcases le_or_gt s 1 with hs1 | hs2
  · exact ⟨0, fun N _ => paperTypeDefect_eq_zero_of_le_one N hs1⟩
  · obtain ⟨N₁, hN₁⟩ := hcone
    obtain ⟨N₂, hN₂⟩ := exists_threshold_le_rpow hgamma s
    refine ⟨max N₁ N₂, ?_⟩
    intro N hN
    exact hN₁ N (le_trans (Nat.le_max_left _ _) hN) s hs2
      (hN₂ N (le_trans (Nat.le_max_right _ _) hN))

/-- **Corollary 6.5, from the published input directly.** -/
theorem eventuallyZeroDefect_fixedType_of_shortInterval
    (hSI : ∀ beta : ℝ, 21 / 40 < beta → beta < 1 → ShortIntervalPrimeInput beta)
    (s : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → paperTypeDefect N s = 0 :=
  eventuallyZeroDefect_fixedType_of_cone (gamma := 19 / 118) (by norm_num)
    (eventuallyZeroDefect_bakerHarmanPintz_cone_of_shortInterval hSI
      (by norm_num) (by norm_num)) s

end DivisorF
