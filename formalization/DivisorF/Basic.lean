import Mathlib.Combinatorics.SimpleGraph.Finite

set_option linter.style.header false

/-!
# Finite divisor graphs

This file defines the divisor graph `G_N` on `{1, ..., N}` and its reduced
version `H_N = G_N - {1}` on `{2, ..., N}`.  Both vertex sets are finite by
construction.
-/

namespace DivisorF

/-- Vertices of the divisor graph `G_N`, encoded by `0, ..., N - 1`. -/
abbrev GVertex (N : ℕ) := Fin N

/-- The positive integer represented by a vertex of `G_N`. -/
def GVertex.value {N : ℕ} (v : GVertex N) : ℕ := v.val + 1

@[simp]
theorem GVertex.one_le_value {N : ℕ} (v : GVertex N) : 1 ≤ v.value := by
  simp [GVertex.value]

@[simp]
theorem GVertex.value_le {N : ℕ} (v : GVertex N) : v.value ≤ N := by
  simp [GVertex.value]
  omega

/-- Vertices of `H_N = G_N - {1}`, encoded by `0, ..., N - 2`. -/
abbrev HVertex (N : ℕ) := Fin (N - 1)

/-- The integer in `{2, ..., N}` represented by a vertex of `H_N`. -/
def HVertex.value {N : ℕ} (v : HVertex N) : ℕ := v.val + 2

@[simp]
theorem HVertex.two_le_value {N : ℕ} (v : HVertex N) : 2 ≤ v.value := by
  simp [HVertex.value]

@[simp]
theorem HVertex.value_le {N : ℕ} (v : HVertex N) : v.value ≤ N := by
  simp [HVertex.value]
  omega

/-- Construct a vertex of `H_N` from an integer in `{2, ..., N}`. -/
def HVertex.ofValue {N n : ℕ} (h2 : 2 ≤ n) (hN : n ≤ N) : HVertex N :=
  ⟨n - 2, by omega⟩

@[simp]
theorem HVertex.value_ofValue {N n : ℕ} (h2 : 2 ≤ n) (hN : n ≤ N) :
    (HVertex.ofValue h2 hN).value = n := by
  simp [HVertex.ofValue, HVertex.value]
  omega

theorem HVertex.ext_value {N : ℕ} {v w : HVertex N} (h : v.value = w.value) :
    v = w := by
  apply Fin.ext
  simpa [HVertex.value] using h

/-- The divisor graph on `{1, ..., N}`. -/
def divisorGraph (N : ℕ) : SimpleGraph (GVertex N) :=
  SimpleGraph.fromRel fun v w ↦ v.value ∣ w.value

/-- The divisor graph on `{2, ..., N}`. -/
def reducedDivisorGraph (N : ℕ) : SimpleGraph (HVertex N) :=
  SimpleGraph.fromRel fun v w ↦ v.value ∣ w.value

@[simp]
theorem divisorGraph_adj {N : ℕ} (v w : GVertex N) :
    (divisorGraph N).Adj v w ↔
      v ≠ w ∧ (v.value ∣ w.value ∨ w.value ∣ v.value) :=
  Iff.rfl

@[simp]
theorem reducedDivisorGraph_adj {N : ℕ} (v w : HVertex N) :
    (reducedDivisorGraph N).Adj v w ↔
      v ≠ w ∧ (v.value ∣ w.value ∨ w.value ∣ v.value) :=
  Iff.rfl

end DivisorF
