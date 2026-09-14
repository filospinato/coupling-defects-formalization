import DivisorF.WeightedPairDensity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Effective fixed-type transfers

Project-original Section 5 consequences of the explicit prime-packing lemma.
Dusart's prime-interval estimate is external literature and is not formalized.
Instead `EffectivePrimePackingInput` exposes exactly the paper's packing lemma
as an explicit hypothesis.  Everything after that interface — binary/zero
thresholds, effective natural cutoffs, and the finite-range consequence for a
hypothetical non-binary fibre — is proved here from the same-type budget.
-/

namespace DivisorF

/-- `κ_m(s)` from the manuscript's effective prime-packing subsection. -/
noncomputable def effectivePackingKappa (m s : ℕ) : ℝ :=
  Real.sqrt
    ((m : ℝ) /
      (25 * Real.log (1 + 1 / (s : ℝ))))

/-- `T_m(s)=max{396738,s+1,exp(κ_m(s))}`. -/
noncomputable def effectivePackingThreshold (m s : ℕ) : ℝ :=
  max 396738
    (max ((s + 1 : ℕ) : ℝ) (Real.exp (effectivePackingKappa m s)))

/-- Explicit literature-facing interface for the manuscript's effective
prime-packing lemma.  It is an assumption on a theorem, not a project axiom.
The intended supplier is Dusart's quoted prime-interval estimate plus the
paper's finite packing construction. -/
def EffectivePrimePackingInput : Prop :=
  ∀ (N s m : ℕ),
    2 ≤ N →
    2 ≤ s →
    1 ≤ m →
    ((s + 1 : ℕ) : ℝ) * effectivePackingThreshold m s ≤ (N : ℝ) →
    m ≤ typeMultiplicity N s

/-- **Effective fixed-type binary transfer, optimized form.**
Under the explicit packing input, the manuscript threshold with `m=s` forces
`d_s(N)≤1`. -/
theorem paperTypeDefect_le_one_of_effective_packing
    (hpack : EffectivePrimePackingInput)
    {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s)
    (hthreshold :
      ((s + 1 : ℕ) : ℝ) * effectivePackingThreshold s s ≤ (N : ℝ)) :
    paperTypeDefect N s ≤ 1 := by
  have hm : s ≤ typeMultiplicity N s :=
    hpack N s s hN hs (by omega) hthreshold
  have hpos : 0 < typeMultiplicity N s :=
    lt_of_lt_of_le (by omega : 0 < s) hm
  have hocc : TypeOccupied N s :=
    typeMultiplicity_pos_iff_occupied.mp hpos
  rw [paperTypeDefect_eq_of_occupied hocc]
  exact typeDefect_le_one_of_multiplicity_lower_bound
    hocc hm (by omega)

/-- **Effective fixed-type zero transfer, optimized form.**
Using `m=2s-1` gives exactly the paper's zero-defect threshold. -/
theorem paperTypeDefect_eq_zero_of_effective_packing
    (hpack : EffectivePrimePackingInput)
    {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s)
    (hthreshold :
      ((s + 1 : ℕ) : ℝ) *
          effectivePackingThreshold (2 * s - 1) s ≤ (N : ℝ)) :
    paperTypeDefect N s = 0 := by
  have hm : 2 * s - 1 ≤ typeMultiplicity N s :=
    hpack N s (2 * s - 1) hN hs (by omega) hthreshold
  have hpos : 0 < typeMultiplicity N s :=
    lt_of_lt_of_le (by omega : 0 < 2 * s - 1) hm
  have hocc : TypeOccupied N s :=
    typeMultiplicity_pos_iff_occupied.mp hpos
  rw [paperTypeDefect_eq_of_occupied hocc]
  exact typeDefect_eq_zero_of_multiplicity_lower_bound
    hocc hm (by omega)

/-- Natural executable cutoff corresponding to the optimized binary threshold.
The extra `max 2` only exposes the manuscript's ambient hypothesis `N≥2`. -/
noncomputable def effectiveBinaryNatThreshold (s : ℕ) : ℕ :=
  max 2 (Nat.ceil
    (((s + 1 : ℕ) : ℝ) * effectivePackingThreshold s s))

/-- Natural executable cutoff corresponding to the optimized zero threshold. -/
noncomputable def effectiveZeroNatThreshold (s : ℕ) : ℕ :=
  max 2 (Nat.ceil
    (((s + 1 : ℕ) : ℝ) *
      effectivePackingThreshold (2 * s - 1) s))

/-- The real optimized binary threshold is satisfied once the natural cutoff is
reached. -/
theorem effective_binary_threshold_real_le
    {N s : ℕ} (hN : effectiveBinaryNatThreshold s ≤ N) :
    ((s + 1 : ℕ) : ℝ) * effectivePackingThreshold s s ≤ (N : ℝ) := by
  have hceil :
      Nat.ceil (((s + 1 : ℕ) : ℝ) * effectivePackingThreshold s s) ≤ N :=
    le_trans (le_max_right 2 _) hN
  exact le_trans
    (Nat.le_ceil (((s + 1 : ℕ) : ℝ) * effectivePackingThreshold s s))
    (by exact_mod_cast hceil)

/-- The real optimized zero threshold is satisfied once the natural cutoff is
reached. -/
theorem effective_zero_threshold_real_le
    {N s : ℕ} (hN : effectiveZeroNatThreshold s ≤ N) :
    ((s + 1 : ℕ) : ℝ) *
        effectivePackingThreshold (2 * s - 1) s ≤ (N : ℝ) := by
  have hceil :
      Nat.ceil
        (((s + 1 : ℕ) : ℝ) *
          effectivePackingThreshold (2 * s - 1) s) ≤ N :=
    le_trans (le_max_right 2 _) hN
  exact le_trans
    (Nat.le_ceil
      (((s + 1 : ℕ) : ℝ) *
        effectivePackingThreshold (2 * s - 1) s))
    (by exact_mod_cast hceil)

/-- Effective binary threshold with only natural quantifiers. -/
theorem paperTypeDefect_le_one_of_effective_nat_threshold
    (hpack : EffectivePrimePackingInput)
    {N s : ℕ} (hs : 2 ≤ s)
    (hN : effectiveBinaryNatThreshold s ≤ N) :
    paperTypeDefect N s ≤ 1 := by
  have hN2 : 2 ≤ N :=
    le_trans (le_max_left 2 _) hN
  exact paperTypeDefect_le_one_of_effective_packing
    hpack hN2 hs (effective_binary_threshold_real_le hN)

/-- **Eventual zero defect for every fixed quotient type, effective form.**
For each fixed `s≥2`, every `N` beyond the explicit natural cutoff has
`d_s(N)=0`. -/
theorem paperTypeDefect_eq_zero_of_effective_nat_threshold
    (hpack : EffectivePrimePackingInput)
    {N s : ℕ} (hs : 2 ≤ s)
    (hN : effectiveZeroNatThreshold s ≤ N) :
    paperTypeDefect N s = 0 := by
  have hN2 : 2 ≤ N :=
    le_trans (le_max_left 2 _) hN
  exact paperTypeDefect_eq_zero_of_effective_packing
    hpack hN2 hs (effective_zero_threshold_real_le hN)

/-- Paper-facing existential form of eventual zero defect for fixed types. -/
theorem exists_eventual_zero_threshold_for_fixed_type
    (hpack : EffectivePrimePackingInput)
    {s : ℕ} (hs : 2 ≤ s) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → paperTypeDefect N s = 0 := by
  exact ⟨effectiveZeroNatThreshold s,
    fun N hN => paperTypeDefect_eq_zero_of_effective_nat_threshold
      hpack hs hN⟩

/-- A hypothetical non-binary fibre of fixed quotient type must lie below the
optimized effective binary threshold.  This is the finite-range consequence
used in the manuscript; the cleaner `exp(s/4)` threshold is a later numerical
relaxation and is deliberately not attributed to the external input here. -/
theorem nonbinary_type_below_effective_threshold
    (hpack : EffectivePrimePackingInput)
    {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s)
    (hdef : 1 < paperTypeDefect N s) :
    (N : ℝ) <
      ((s + 1 : ℕ) : ℝ) * effectivePackingThreshold s s := by
  by_contra hnot
  have hthreshold :
      ((s + 1 : ℕ) : ℝ) * effectivePackingThreshold s s ≤ (N : ℝ) :=
    le_of_not_gt hnot
  have hbinary := paperTypeDefect_le_one_of_effective_packing
    hpack hN hs hthreshold
  omega

end DivisorF
