import DivisorF.Defect

set_option linter.style.header false

/-!
# Mandatory crossings and crossing slack

This module formalizes Section 8 of the paper.  The minimum crossing count is
taken over the finite, nonempty collection of maximum spanning linear forests;
in particular, it is an attained minimum rather than an infimum with a hidden
existence assumption.
-/

namespace DivisorF

open SimpleGraph

variable {V : Type*}

/-- The finite collection of maximum spanning linear forests of `G`. -/
noncomputable def maximumLinearForests [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter fun L ↦
    IsLinearForest G L ∧ edgeCard L = linearForestNumber G

@[simp]
theorem mem_maximumLinearForests [Fintype V] [DecidableEq V]
    {G L : SimpleGraph V} :
    L ∈ maximumLinearForests G ↔
      IsLinearForest G L ∧ edgeCard L = linearForestNumber G := by
  classical
  simp [maximumLinearForests]

theorem maximumLinearForests_nonempty [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : (maximumLinearForests G).Nonempty := by
  classical
  obtain ⟨L, hL, hmax⟩ := exists_maximumLinearForest G
  exact ⟨L, by simp [hL, hmax]⟩

/-- Crossing counts attained by maximum spanning linear forests of `H_N`. -/
noncomputable def maximumForestCrossingCounts {N : ℕ} (q : LargePrime N) : Finset ℕ := by
  classical
  exact (maximumLinearForests (reducedDivisorGraph N)).image (crossingCount q)

theorem maximumForestCrossingCounts_nonempty {N : ℕ} (q : LargePrime N) :
    (maximumForestCrossingCounts q).Nonempty := by
  classical
  rw [maximumForestCrossingCounts, Finset.image_nonempty]
  exact maximumLinearForests_nonempty _

/-- `μ_N(q)`, the minimum number of fibre crossings among maximum forests. -/
noncomputable def mandatoryCrossingCount {N : ℕ} (q : LargePrime N) : ℕ :=
  (maximumForestCrossingCounts q).min' (maximumForestCrossingCounts_nonempty q)

theorem mandatoryCrossingCount_mem {N : ℕ} (q : LargePrime N) :
    mandatoryCrossingCount q ∈ maximumForestCrossingCounts q := by
  classical
  exact Finset.min'_mem _ _

/-- The minimum defining `μ_N(q)` is attained by a maximum linear forest. -/
theorem exists_crossing_minimizing_maximumLinearForest {N : ℕ} (q : LargePrime N) :
    ∃ L : SimpleGraph (HVertex N),
      IsLinearForest (reducedDivisorGraph N) L ∧
        edgeCard L = linearForestNumber (reducedDivisorGraph N) ∧
          crossingCount q L = mandatoryCrossingCount q := by
  classical
  have hmem := mandatoryCrossingCount_mem q
  rw [maximumForestCrossingCounts, Finset.mem_image] at hmem
  obtain ⟨L, hL, hcross⟩ := hmem
  rw [mem_maximumLinearForests] at hL
  exact ⟨L, hL.1, hL.2, hcross⟩

/-- `μ_N(q)` is no larger than the crossing count of any maximum forest. -/
theorem mandatoryCrossingCount_le {N : ℕ} (q : LargePrime N)
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N)) :
    mandatoryCrossingCount q ≤ crossingCount q L := by
  classical
  apply Finset.min'_le
  rw [maximumForestCrossingCounts, Finset.mem_image]
  exact ⟨L, by simp [hL, hmax], rfl⟩

/-- If the fibre defect vanishes, a maximum forest exists with no fibre
crossings.  This is the constructive half of Proposition 8.1. -/
theorem exists_maximumLinearForest_crossingCount_zero_of_fibreDefect_eq_zero
    {N : ℕ} (q : LargePrime N) (hdefect : fibreDefect q = 0) :
    ∃ L : SimpleGraph (HVertex N),
      IsLinearForest (reducedDivisorGraph N) L ∧
        edgeCard L = linearForestNumber (reducedDivisorGraph N) ∧
          crossingCount q L = 0 := by
  classical
  let G := reducedDivisorGraph N
  let p : HVertex N → Prop := InFibre q
  obtain ⟨LA, hLA, hcardA⟩ := exists_maximumLinearForest (G.induce {v | p v})
  obtain ⟨LB, hLB, hcardB⟩ := exists_maximumLinearForest (G.induce {v | ¬ p v})
  let e : ({v // p v} ⊕ {v // ¬ p v}) ≃ HVertex N := Equiv.sumCompl p
  let M : SimpleGraph (HVertex N) := relabel e (LA ⊕g LB)
  have hforest : IsLinearForest G M := by
    refine IsLinearForest.of_relabel e (isAcyclic_sum hLA.2.1 hLB.2.1) ?_ ?_
    · intro x
      cases x with
      | inl a => rw [selectedDegree_sum_inl]; exact hLA.2.2 a
      | inr a => rw [selectedDegree_sum_inr]; exact hLB.2.2 a
    · intro x y hxy
      change ((LA ⊕g LB).map e).Adj x y at hxy
      rw [SimpleGraph.map_adj'] at hxy
      obtain ⟨_, u, v, huv, rfl, rfl⟩ := hxy
      cases u with
      | inl a =>
        cases v with
        | inl a' =>
          have h : G.Adj (a : HVertex N) (a' : HVertex N) :=
            hLA.1 (sum_adj_inl.mp huv)
          simpa [e, Equiv.sumCompl_apply_inl] using h
        | inr b => exact absurd huv (not_adj_sum_inl_inr a b)
      | inr a =>
        cases v with
        | inl b => exact absurd huv.symm (not_adj_sum_inl_inr b a)
        | inr a' =>
          have h : G.Adj (a : HVertex N) (a' : HVertex N) :=
            hLB.1 (sum_adj_inr.mp huv)
          simpa [e, Equiv.sumCompl_apply_inr] using h
  have hsum :
      linearForestNumber (G.induce {v | p v})
          + linearForestNumber (G.induce {v | ¬ p v})
        = linearForestNumber G := by
    change linearForestNumber (fibreGraph q) + linearForestNumber (fibreComplement q)
      = linearForestNumber (reducedDivisorGraph N)
    unfold fibreDefect at hdefect
    rw [linearForestNumber_quotientType q] at hdefect
    omega
  have hcardM : edgeCard M = linearForestNumber G := by
    calc
      edgeCard M = edgeCard (LA ⊕g LB) := edgeCard_relabel e (LA ⊕g LB)
      _ = edgeCard LA + edgeCard LB := edgeCard_sum LA LB
      _ = linearForestNumber (G.induce {v | p v})
          + linearForestNumber (G.induce {v | ¬ p v}) := by rw [hcardA, hcardB]
      _ = linearForestNumber G := hsum
  have hcross : crossingCount q M = 0 := by
    unfold crossingCount crossingCard
    rw [Set.ncard_eq_zero]
    ext edge
    constructor
    · rintro ⟨hedge, ⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩
      exfalso
      induction edge using Sym2.ind with
      | _ x y =>
        rw [mem_edgeSet] at hedge
        simp only [Sym2.mem_iff] at ha hb
        have hside : (p x ∧ p y) ∨ (¬ p x ∧ ¬ p y) := by
          change ((LA ⊕g LB).map e).Adj x y at hedge
          rw [SimpleGraph.map_adj'] at hedge
          obtain ⟨_, u, v, huv, rfl, rfl⟩ := hedge
          cases u with
          | inl u =>
            cases v with
            | inl v => exact Or.inl ⟨u.2, v.2⟩
            | inr v => exact absurd huv (not_adj_sum_inl_inr u v)
          | inr u =>
            cases v with
            | inl v => exact absurd huv.symm (not_adj_sum_inl_inr v u)
            | inr v => exact Or.inr ⟨u.2, v.2⟩
        rcases hside with hsame | hsame
        · apply hpb
          rcases hb with hbx | hby
          · rw [hbx]; exact hsame.1
          · rw [hby]; exact hsame.2
        · have hnotpa : ¬ p a := by
            rcases ha with hax | hay
            · rw [hax]; exact hsame.1
            · rw [hay]; exact hsame.2
          exact hnotpa hpa
    · simp
  exact ⟨M, hforest, hcardM, hcross⟩

/-- **Proposition 8.1 of the paper.**  A fibre has zero defect exactly when no
crossing is mandatory in a maximum spanning linear forest. -/
theorem fibreDefect_eq_zero_iff_mandatoryCrossingCount_eq_zero
    {N : ℕ} (q : LargePrime N) :
    fibreDefect q = 0 ↔ mandatoryCrossingCount q = 0 := by
  constructor
  · intro hdefect
    obtain ⟨L, hL, hmax, hcross⟩ :=
      exists_maximumLinearForest_crossingCount_zero_of_fibreDefect_eq_zero q hdefect
    have hle := mandatoryCrossingCount_le q hL hmax
    omega
  · intro hmu
    obtain ⟨L, hL, hmax, hcross⟩ :=
      exists_crossing_minimizing_maximumLinearForest q
    have hnonneg := fibreDefect_nonneg q
    have hle := fibreDefect_le_crossingCount q hL hmax
    rw [hcross, hmu] at hle
    omega

/-- The defect is bounded by the number of mandatory crossings. -/
theorem fibreDefect_le_mandatoryCrossingCount {N : ℕ} (q : LargePrime N) :
    fibreDefect q ≤ (mandatoryCrossingCount q : ℤ) := by
  obtain ⟨L, hL, hmax, hcross⟩ :=
    exists_crossing_minimizing_maximumLinearForest q
  have hle := fibreDefect_le_crossingCount q hL hmax
  rwa [hcross] at hle

/-- `V_N(q) = μ_N(q) - D_N(q)`, represented in `ℤ`. -/
noncomputable def crossingSlack {N : ℕ} (q : LargePrime N) : ℤ :=
  (mandatoryCrossingCount q : ℤ) - fibreDefect q

theorem crossingSlack_nonneg {N : ℕ} (q : LargePrime N) :
    0 ≤ crossingSlack q := by
  have hle := fibreDefect_le_mandatoryCrossingCount q
  unfold crossingSlack
  omega

/-- The crossing-slack identity `D_N(q) = μ_N(q) - V_N(q)`. -/
theorem fibreDefect_eq_mandatoryCrossingCount_sub_crossingSlack
    {N : ℕ} (q : LargePrime N) :
    fibreDefect q = (mandatoryCrossingCount q : ℤ) - crossingSlack q := by
  unfold crossingSlack
  omega

/-- **Theorem 8.2 of the paper.**  On every crossing-minimizing maximum
forest, the crossing slack is exactly the sum of the two restriction losses. -/
theorem crossingSlack_eq_restriction_losses {N : ℕ} (q : LargePrime N)
    {L : SimpleGraph (HVertex N)}
    (_hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hcross : crossingCount q L = mandatoryCrossingCount q) :
    crossingSlack q = fibreRestrictionLoss q L + complementRestrictionLoss q L := by
  unfold crossingSlack
  rw [fibreDefect_eq_crossing_sub_losses q hmax]
  rw [← hcross]
  omega

/-- The total restriction loss is independent of the chosen
crossing-minimizing maximum forest. -/
theorem restrictionLoss_sum_eq_of_crossing_minimizing {N : ℕ} (q : LargePrime N)
    {L K : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hLmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hLcross : crossingCount q L = mandatoryCrossingCount q)
    (hK : IsLinearForest (reducedDivisorGraph N) K)
    (hKmax : edgeCard K = linearForestNumber (reducedDivisorGraph N))
    (hKcross : crossingCount q K = mandatoryCrossingCount q) :
    fibreRestrictionLoss q L + complementRestrictionLoss q L
      = fibreRestrictionLoss q K + complementRestrictionLoss q K := by
  rw [← crossingSlack_eq_restriction_losses q hL hLmax hLcross,
    ← crossingSlack_eq_restriction_losses q hK hKmax hKcross]

/-- The threshold form of Theorem 8.2, for every integer `a ≥ 1`. -/
theorem fibreDefect_ge_iff_mandatoryCrossingCount_ge_crossingSlack_add
    {N : ℕ} (q : LargePrime N) (a : ℤ) (_ha : 1 ≤ a) :
    a ≤ fibreDefect q ↔ crossingSlack q + a ≤ (mandatoryCrossingCount q : ℤ) := by
  unfold crossingSlack
  omega

/-- **Corollary 8.3 of the paper.**  Binary defect is exactly the pointwise
bound saying that at most one mandatory crossing remains after restriction
loss is charged. -/
theorem fibreDefect_le_one_iff_mandatoryCrossingCount_le_crossingSlack_add_one
    {N : ℕ} (q : LargePrime N) :
    fibreDefect q ≤ 1 ↔ (mandatoryCrossingCount q : ℤ) ≤ crossingSlack q + 1 := by
  unfold crossingSlack
  omega

/-- Since the defect is nonnegative, the preceding inequality is equivalent
to membership in `{0, 1}`. -/
theorem fibreDefect_eq_zero_or_one_iff_mandatoryCrossingCount_bound
    {N : ℕ} (q : LargePrime N) :
    (fibreDefect q = 0 ∨ fibreDefect q = 1) ↔
      (mandatoryCrossingCount q : ℤ) ≤ crossingSlack q + 1 := by
  rw [← fibreDefect_le_one_iff_mandatoryCrossingCount_le_crossingSlack_add_one]
  have hnonneg := fibreDefect_nonneg q
  omega

/-- Pointwise universal binarity over all large primes is equivalent to the
mandatory-crossing bound, without asserting that either side holds. -/
theorem universal_binary_iff_mandatoryCrossingCount_bound (N : ℕ) :
    (∀ q : LargePrime N, fibreDefect q = 0 ∨ fibreDefect q = 1) ↔
      ∀ q : LargePrime N,
        (mandatoryCrossingCount q : ℤ) ≤ crossingSlack q + 1 := by
  constructor
  · intro h q
    exact (fibreDefect_eq_zero_or_one_iff_mandatoryCrossingCount_bound q).mp (h q)
  · intro h q
    exact (fibreDefect_eq_zero_or_one_iff_mandatoryCrossingCount_bound q).mpr (h q)

end DivisorF
