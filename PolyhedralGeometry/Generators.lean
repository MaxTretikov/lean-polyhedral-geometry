/-
  Generators.lean

  Generator set structure for representing cones via their generating vectors.
  Conical hull definitions and properties.
-/

import PolyhedralGeometry.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.StdBasis

noncomputable section

open Matrix BigOperators
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace PolyhedralGeometry

/-- Pointwise ordering on Vec p (EuclideanSpace doesn't inherit Pi's ordering) -/
instance : LE (Vec p) where
  le x y := ∀ i, x i ≤ y i

instance : Preorder (Vec p) where
  le := (· ≤ ·)
  le_refl x i := le_refl (x i)
  le_trans x y z hxy hyz i := le_trans (hxy i) (hyz i)

/-- A finitely-indexed set of generator vectors. -/
structure GeneratorSet (p : ℕ) where
  ι : Type
  instDecEq : DecidableEq ι
  s : Finset ι
  vec : ι → Vec p

attribute [instance] GeneratorSet.instDecEq

variable {p : ℕ}

/-! ## Conical Hull Definition -/

/-- The conical hull of a set: all non-negative linear combinations. -/
def ConicalHullSet (G : Set (Vec p)) : Set (Vec p) :=
  {x | ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (v : ι → Vec p),
        (∀ i ∈ s, 0 ≤ c i) ∧ (∀ i ∈ s, v i ∈ G) ∧ x = ∑ i ∈ s, c i • v i}

theorem isGeneratorSet_iff_eq_conicalHull (G : Set (Vec p)) (C : Set (Vec p)) :
    IsGeneratorSet G C ↔ C = ConicalHullSet G := Iff.rfl

/-! ## Conical Hull Properties -/

lemma conicalHull_contains (G : Set (Vec p)) (g : Vec p) (hg : g ∈ G) : g ∈ ConicalHullSet G := by
  use Unit, {Unit.unit}, (fun _ => 1), (fun _ => g)
  simp [hg]

lemma conicalHull_add (G : Set (Vec p)) (x y : Vec p) (hx : x ∈ ConicalHullSet G) (hy : y ∈ ConicalHullSet G) :
    x + y ∈ ConicalHullSet G := by
  rcases hx with ⟨ι1, s1, c1, v1, hc1, hv1, rfl⟩
  rcases hy with ⟨ι2, s2, c2, v2, hc2, hv2, rfl⟩
  use Sum ι1 ι2, s1.disjSum s2
  use Sum.elim c1 c2
  use Sum.elim v1 v2
  constructor
  · intro i hi; cases i <;> simp at hi <;> [apply hc1; apply hc2] <;> assumption
  constructor
  · intro i hi; cases i <;> simp at hi <;> [apply hv1; apply hv2] <;> assumption
  · simp

lemma conicalHull_smul (G : Set (Vec p)) (c : ℝ) (x : Vec p) (hc : 0 ≤ c) (hx : x ∈ ConicalHullSet G) :
    c • x ∈ ConicalHullSet G := by
  rcases hx with ⟨ι, s, c', v, hc', hv, rfl⟩
  use ι, s, (fun i => c * c' i), v
  constructor
  · intro i hi; apply mul_nonneg hc (hc' i hi)
  constructor
  · exact hv
  · simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]

theorem conicalHull_mono (S T : Set (Vec p)) (h : S ⊆ T) :
    ConicalHullSet S ⊆ ConicalHullSet T := by
  intro x hx
  obtain ⟨ι, s, c, v, h_nonneg, h_mem, rfl⟩ := hx
  have h_mem_T : ∀ i ∈ s, v i ∈ T := fun i hi => h ( h_mem i hi )
  exact ⟨ι, s, c, v, h_nonneg, h_mem_T, rfl⟩

lemma conicalHull_idempotent (S : Set (Vec p)) : ConicalHullSet (ConicalHullSet S) ⊆ ConicalHullSet S := by
  sorry

theorem conicalHull_subset_generated_cone (GenSets : List (Set (Vec p))) (C : Set (Vec p)) (S : Set (Vec p))
    (h_mem : S ∈ GenSets)
    (h_gen : IsGeneratorSet (⋃₀ {T | T ∈ GenSets}) C) :
    ConicalHullSet S ⊆ C :=
  h_gen.symm ▸ conicalHull_mono _ _ fun x hx => Set.mem_sUnion.mpr ⟨ S, h_mem, hx ⟩

theorem zero_in_conicalHull (G : Set (Vec p)) : 0 ∈ ConicalHullSet G :=
  ⟨ PEmpty, ∅, 0, 0, by norm_num ⟩

/-! ## Hyperplane -/

/-- Hyperplane through origin with normal b, defined as the orthogonal complement of span{b}. -/
def HyperplaneSet (b : Vec p) : Set (Vec p) := ↑((ℝ ∙ b)ᗮ)

/-! ## Generator Filtering by Inner Product Sign -/

/-- Filter generators by sign of inner product with constraint vector b. -/
def posGeneratorsList (G : List (Vec p)) (b : Vec p) : List (Vec p) :=
  G.filter (fun g => ⟪b, g⟫_ℝ > 0)

def negGeneratorsList (G : List (Vec p)) (b : Vec p) : List (Vec p) :=
  G.filter (fun g => ⟪b, g⟫_ℝ < 0)

def zeroGeneratorsList (G : List (Vec p)) (b : Vec p) : List (Vec p) :=
  G.filter (fun g => ⟪b, g⟫_ℝ = 0)

/-! ## Ray-Face Intersection -/

/-- A ray from y in direction η hits a face F. -/
def IsRayFaceIntersection (y η : Vec p) (F : Set (Vec p)) (ξ : Vec p) : Prop :=
  ∃ t : ℝ, t > 0 ∧ (∀ i, ξ i = y i + t * η i) ∧ ξ ∈ F

/-- Interior point condition: y is in the topological interior of the nonnegative orthant. -/
def IsInteriorPoint (y : Vec p) : Prop := y ∈ interior (nonnegOrthant p)

/-- Equivalent characterization: all coordinates strictly positive. -/
lemma isInteriorPoint_iff_all_pos (y : Vec p) :
    IsInteriorPoint y ↔ ∀ i : Fin p, 0 < y i := by
  sorry  -- This requires showing interior of orthant = strict positivity

/-! ## Standard Basis as Finset -/

/-- The standard basis vectors as a finset. -/
def StandardBasis (p : ℕ) : Finset (Vec p) :=
  Finset.univ.image (fun i => EuclideanSpace.basisFun (Fin p) ℝ i)

lemma standardBasisSet_eq (p : ℕ) :
    (StandardBasis p : Set (Vec p)) = StandardBasisSet (p := p) := by
  ext x; constructor
  · intro hx
    simp only [StandardBasis, Finset.coe_image, Set.mem_image] at hx
    rcases hx with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    simp only [StandardBasis, Finset.coe_image, Set.mem_image]
    exact ⟨i, Finset.mem_univ i, rfl⟩

theorem orthant_generated_by_basis :
  IsGeneratorSet (StandardBasis p : Set (Vec p)) OrthantSet := by
    simpa [standardBasisSet_eq, OrthantSet, nonnegOrthant] using
      (orthant_generated_by_std_basis (p := p))

end PolyhedralGeometry
