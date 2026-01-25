/-
  Generators.lean

  Generator set structure for representing cones via their generating vectors.
  Uses conical hull definitions from Cone.lean.
-/

import PolyhedralGeometry.Cone
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

/-! ## IsGeneratorSet and conicalHull equivalence -/

/-- IsGeneratorSet G C is equivalent to C = conicalHull G.
    Note: IsGeneratorSet uses ι : Type (universe 0), while conicalHull uses Type*.
    We use conicalHull.{_,0} to match the universe. -/
theorem isGeneratorSet_iff_eq_conicalHull (G : Set (Vec p)) (C : Set (Vec p)) :
    IsGeneratorSet G C ↔ C = conicalHull.{_, 0} G := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      rw [h] at hx
      obtain ⟨ι, s, c, v, hc, hv, rfl⟩ := hx
      use ι, s, c, v
      constructor
      · intro i hi
        right
        exact ⟨hc i hi, hv i hi⟩
      · rfl
    · intro hx
      rw [h]
      obtain ⟨ι, s, c, v, hcv, rfl⟩ := hx
      classical
      let s' := s.filter (fun i => c i ≠ 0)
      use ι, s', c, v
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_filter] at hi
        rcases hcv i hi.1 with h_zero | ⟨h_nonneg, _⟩
        · exact absurd h_zero hi.2
        · exact h_nonneg
      · intro i hi
        rw [Finset.mem_filter] at hi
        rcases hcv i hi.1 with h_zero | ⟨_, h_mem⟩
        · exact absurd h_zero hi.2
        · exact h_mem
      · symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hni
        rw [Finset.mem_filter, not_and, not_not] at hni
        simp [hni hi]
  · intro h
    rw [h]
    ext x
    constructor
    · intro hx
      obtain ⟨ι, s, c, v, hcv, rfl⟩ := hx
      classical
      let s' := s.filter (fun i => c i ≠ 0)
      use ι, s', c, v
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_filter] at hi
        rcases hcv i hi.1 with h_zero | ⟨h_nonneg, _⟩
        · exact absurd h_zero hi.2
        · exact h_nonneg
      · intro i hi
        rw [Finset.mem_filter] at hi
        rcases hcv i hi.1 with h_zero | ⟨_, h_mem⟩
        · exact absurd h_zero hi.2
        · exact h_mem
      · symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hni
        rw [Finset.mem_filter, not_and, not_not] at hni
        simp [hni hi]
    · intro hx
      obtain ⟨ι, s, c, v, hc, hv, rfl⟩ := hx
      use ι, s, c, v
      constructor
      · intro i hi
        right
        exact ⟨hc i hi, hv i hi⟩
      · rfl

theorem conicalHull_subset_generated_cone (GenSets : List (Set (Vec p))) (C : Set (Vec p)) (S : Set (Vec p))
    (h_mem : S ∈ GenSets)
    (h_gen : IsGeneratorSet (⋃₀ {T | T ∈ GenSets}) C) :
    conicalHull.{_, 0} S ⊆ C := by
  have h := (isGeneratorSet_iff_eq_conicalHull _ _).mp h_gen
  rw [h]
  exact conicalHull_mono S _ fun x hx => Set.mem_sUnion.mpr ⟨ S, h_mem, hx ⟩

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
