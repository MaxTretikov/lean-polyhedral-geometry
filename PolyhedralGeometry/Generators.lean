/-
  Generators.lean

  Generator set structure for representing cones via their generating vectors.
  Core polyhedral geometry definitions.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
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

/-- The standard Euclidean space ℝ^p. -/
abbrev Vec (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- Pointwise ordering on Vec p (EuclideanSpace doesn't inherit Pi's ordering) -/
instance : LE (Vec p) where
  le x y := ∀ i, x i ≤ y i

instance : Preorder (Vec p) where
  le := (· ≤ ·)
  le_refl x i := le_refl (x i)
  le_trans x y z hxy hyz i := le_trans (hxy i) (hyz i)

/-- The nonnegative orthant: all vectors with nonnegative coordinates. -/
def nonnegOrthant (p : ℕ) : Set (Vec p) := { y | ∀ i, 0 ≤ y i }

/-- A finitely-indexed set of generator vectors. -/
structure GeneratorSet (p : ℕ) where
  ι : Type
  instDecEq : DecidableEq ι
  s : Finset ι
  vec : ι → Vec p

attribute [instance] GeneratorSet.instDecEq

variable {p : ℕ}

/-! ## Generator Set Definition -/

/-- A set G generates a cone C if C equals the set of non-negative linear combinations of G. -/
def IsGeneratorSet (G : Set (Vec p)) (C : Set (Vec p)) : Prop :=
  C = {x | ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (v : ι → Vec p),
            (∀ i ∈ s, 0 ≤ c i) ∧ (∀ i ∈ s, v i ∈ G) ∧ x = ∑ i ∈ s, c i • v i}

/-- The conical hull of a set: all non-negative linear combinations. -/
def ConicalHullSet (G : Set (Vec p)) : Set (Vec p) :=
  {x | ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (v : ι → Vec p),
        (∀ i ∈ s, 0 ≤ c i) ∧ (∀ i ∈ s, v i ∈ G) ∧ x = ∑ i ∈ s, c i • v i}

theorem isGeneratorSet_iff_eq_conicalHull (G : Set (Vec p)) (C : Set (Vec p)) :
    IsGeneratorSet G C ↔ C = ConicalHullSet G := Iff.rfl

/-! ## Standard Basis and Orthant

We use `EuclideanSpace.basisFun` directly from Mathlib for the standard orthonormal basis.
This avoids conflicts with `Matrix.stdBasis` from `Mathlib.LinearAlgebra.StdBasis`.
-/

/-- The set of standard basis vectors. -/
def StandardBasisSet : Set (Vec p) := Set.range (EuclideanSpace.basisFun (Fin p) ℝ)

/-- The nonnegative orthant. -/
def OrthantSet : Set (Vec p) := nonnegOrthant p

/-- Hyperplane through origin with normal b, defined as the orthogonal complement of span{b}. -/
def HyperplaneSet (b : Vec p) : Set (Vec p) := ↑((ℝ ∙ b)ᗮ)

/-- Intersection of orthant with hyperplane. -/
def OrthantHyperplaneSet (b : Vec p) : Set (Vec p) := OrthantSet ∩ HyperplaneSet b

/-- Iterated intersection of orthant with multiple hyperplanes. -/
def IteratedIntersectionSet (bs : List (Vec p)) : Set (Vec p) :=
  bs.foldl (fun C b => C ∩ HyperplaneSet b) OrthantSet

lemma basisFun_nonneg (i : Fin p) : EuclideanSpace.basisFun (Fin p) ℝ i ∈ nonnegOrthant p := by
  intro k
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]
  split_ifs <;> linarith

lemma basisFun_injective : Function.Injective (EuclideanSpace.basisFun (Fin p) ℝ) :=
  (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.injective

theorem orthant_generated_by_std_basis :
    IsGeneratorSet (StandardBasisSet (p := p)) (OrthantSet (p := p)) := by
  sorry

/-! ## g_vec: Farkas Combination Generator -/

/-- The Farkas combination generator: |b_j| • e_i + |b_i| • e_j.
    This vector lies in the hyperplane ⟪b, ·⟫ = 0 when b_i > 0 and b_j < 0. -/
def g_vec (b : Vec p) (i j : Fin p) : Vec p :=
  |b j| • EuclideanSpace.basisFun (Fin p) ℝ i + |b i| • EuclideanSpace.basisFun (Fin p) ℝ j

lemma g_vec_orthogonal (b : Vec p) (i j : Fin p) (hi : b i > 0) (hj : b j < 0) :
    ⟪b, g_vec b i j⟫_ℝ = 0 := by
  simp only [g_vec, inner_add_right, real_inner_smul_right,
    EuclideanSpace.inner_basisFun_real, abs_of_pos hi, abs_of_neg hj]
  ring

lemma g_vec_component_i (b : Vec p) (i j : Fin p) (hij : i ≠ j) :
    (g_vec b i j) i = |b j| := by
  simp only [g_vec, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul, if_true, if_neg hij, mul_one, mul_zero, add_zero]

lemma g_vec_component_j (b : Vec p) (i j : Fin p) (hij : i ≠ j) :
    (g_vec b i j) j = |b i| := by
  simp only [g_vec, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul, if_neg hij.symm, if_true, mul_zero, zero_add, mul_one]

lemma g_vec_component_k (b : Vec p) (i j k : Fin p) (hki : k ≠ i) (hkj : k ≠ j) :
    (g_vec b i j) k = 0 := by
  simp only [g_vec, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul, if_neg hki, if_neg hkj, mul_zero, add_zero]

lemma g_vec_nonneg (b : Vec p) (i j : Fin p) : g_vec b i j ∈ nonnegOrthant p := by
  intro k
  simp only [g_vec, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul]
  split_ifs <;> linarith [abs_nonneg (b j), abs_nonneg (b i)]

/-! ## Intersection Generators -/

/-- Generators for the intersection of orthant with a single hyperplane.
    Consists of:
    1. Standard basis vectors e_k where b_k = 0
    2. Farkas combinations g_vec b i j where b_i > 0 and b_j < 0 -/
def IntersectionGenerators (b : Vec p) : Set (Vec p) :=
  {x | (∃ k : Fin p, b k = 0 ∧ x = EuclideanSpace.basisFun (Fin p) ℝ k) ∨
       (∃ i j : Fin p, b i > 0 ∧ b j < 0 ∧ x = g_vec b i j)}

theorem intersection_generators_finite (b : Vec p) : (IntersectionGenerators b).Finite := by
  apply Set.Finite.subset
  · exact Set.finite_range (fun k : Fin p => EuclideanSpace.basisFun (Fin p) ℝ k) |>.union
           (Set.finite_range (fun ij : Fin p × Fin p => g_vec b ij.1 ij.2))
  · intro x hx
    rcases hx with ⟨k, _, rfl⟩ | ⟨i, j, _, _, rfl⟩
    · left; exact ⟨k, rfl⟩
    · right; exact ⟨(i, j), rfl⟩

theorem intersection_generators_card_bound (b : Vec p) :
    (IntersectionGenerators b).ncard ≤ p + p * p := by
  have h_finite := intersection_generators_finite b
  have h_range1_finite : (Set.range (fun k : Fin p => EuclideanSpace.basisFun (Fin p) ℝ k)).Finite :=
    Set.finite_range _
  have h_range2_finite : (Set.range (fun ij : Fin p × Fin p => g_vec b ij.1 ij.2)).Finite :=
    Set.finite_range _
  calc (IntersectionGenerators b).ncard
      ≤ (Set.range (fun k : Fin p => EuclideanSpace.basisFun (Fin p) ℝ k) ∪
         Set.range (fun ij : Fin p × Fin p => g_vec b ij.1 ij.2)).ncard := by
        apply Set.ncard_le_ncard
        intro x hx
        rcases hx with ⟨k, _, rfl⟩ | ⟨i, j, _, _, rfl⟩
        · left; exact ⟨k, rfl⟩
        · right; exact ⟨(i, j), rfl⟩
        exact h_range1_finite.union h_range2_finite
    _ ≤ (Set.range (fun k : Fin p => EuclideanSpace.basisFun (Fin p) ℝ k)).ncard +
        (Set.range (fun ij : Fin p × Fin p => g_vec b ij.1 ij.2)).ncard :=
        Set.ncard_union_le _ _
    _ ≤ Fintype.card (Fin p) + Fintype.card (Fin p × Fin p) := by
        apply add_le_add
        · rw [Set.ncard_range_of_injective basisFun_injective, Nat.card_eq_fintype_card]
        · have : (Set.range (fun ij : Fin p × Fin p => g_vec b ij.1 ij.2)).ncard ≤
              Nat.card (Fin p × Fin p) := by
            rw [← Set.ncard_univ]
            conv_lhs => rw [← Set.image_univ (f := fun ij : Fin p × Fin p => g_vec b ij.1 ij.2)]
            exact Set.ncard_image_le Set.finite_univ
          simp only [Nat.card_eq_fintype_card] at this ⊢
          exact this
    _ = p + p * p := by simp [Fintype.card_fin, Fintype.card_prod]

theorem intersection_generators_subset_cone (b : Vec p) :
    IntersectionGenerators b ⊆ OrthantHyperplaneSet b := by
  intro x hx
  constructor
  · -- x ∈ OrthantSet
    rcases hx with ⟨k, _, rfl⟩ | ⟨i, j, _, _, rfl⟩
    · exact basisFun_nonneg k
    · exact g_vec_nonneg b i j
  · -- x ∈ HyperplaneSet b (using Mathlib's orthogonal complement API)
    rcases hx with ⟨k, hbk, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
    · apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      simp only [EuclideanSpace.inner_basisFun_real, hbk]
    · apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      exact g_vec_orthogonal b i j hi hj

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

end PolyhedralGeometry
