-- import Mathlib.Data.Real.Basic
-- import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

section
variable {V : Type*} [AddCommMonoid V] [Module ℝ V] (s : Set V)

def Halfspace : Prop :=
  ∃ (f : V →ₗ[ℝ] ℝ) (c : ℝ), s = { x | f x ≤ c }

def IsPolyhedron : Prop :=
  ∃ (ι : Type*) (H : ι → Set V), Finite ι ∧ (∀ i : ι, Halfspace (H i)) ∧ s = ⋂ (i : ι), H i

variable (V) in
@[ext]
structure Polyhedron where
  carrier : Set V
  protected is_polyhedron' : ∃ (ι : Type*) (H : ι → Set V), Finite ι ∧ (∀ i : ι, Halfspace (H i)) ∧ carrier = ⋂ (i : ι), H i

theorem isPolyhedron_def (s : Polyhedron.{_,u} V) : IsPolyhedron.{_,u} s.carrier := s.is_polyhedron'

end

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (s : Set V)

def Polytope.{u} : Prop :=
  IsPolyhedron.{_, u} s ∧ Bornology.IsBounded s

-- theorem bounded_iff_bounded_all (s : Set V) : Polytope' s ↔ IsPolyhedron s ∧ ∃ (_ : SeminormedAddCommGroup V) (_ : InnerProductSpace ℝ V), Bornology.IsBounded s := by sorry

variable {p : ℕ}

/-- The space R^p with the Euclidean inner product. -/
abbrev E (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- The non-negative orthant in R^p. -/
def Orthant (p : ℕ) : Set (E p) := {x | ∀ i, 0 ≤ x i}

/-- The standard basis vectors in R^p. -/
def StandardBasis (p : ℕ) : Finset (E p) :=
  Finset.univ.image (fun i => PiLp.basisFun 2 ℝ (Fin p) i)

/-- A set G generates a cone C if C is the set of non-negative linear combinations of elements of G. -/
def IsGeneratorSet (G : Set (E p)) (C : Set (E p)) : Prop :=
  C = {x | ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (v : ι → E p),
            (∀ i ∈ s, 0 ≤ c i) ∧ (∀ i ∈ s, v i ∈ G) ∧ x = ∑ i ∈ s, c i • v i}

/-- The standard basis vector e_i. -/
def basis (i : Fin p) : E p := PiLp.basisFun 2 ℝ (Fin p) i

/-!
## Hyperplane and Cone Intersection Definitions
-/

/-- A hyperplane passing through the origin defined by normal vector b. -/
def Hyperplane (b : E p) : Set (E p) := {x | inner ℝ b x = (0 : ℝ)}

/-- The intersection of a set C with a hyperplane defined by b. -/
def IntersectCones (C : Set (E p)) (b : E p) : Set (E p) :=
  C ∩ Hyperplane b

/-- The result of intersecting the orthant with a sequence of hyperplanes. -/
def IteratedIntersection (bs : List (E p)) : Set (E p) :=
  bs.foldl IntersectCones (Orthant p)

/-!
## Generator Construction for Hyperplane Intersection

The generators for Orthant ∩ Hyperplane(b) are:
1. Standard basis vectors e_k where b_k = 0 (kernel of b)
2. Farkas combinations |b_j|·e_i + |b_i|·e_j where b_i > 0 and b_j < 0

Paper claims at most p(p-1) generators; we bound by p².
-/

/-- The set of generators for the intersection of the orthant with the hyperplane defined by b. -/
def IntersectionGenerators (b : E p) : Set (E p) :=
  {x | (∃ k, b k = 0 ∧ x = basis k) ∨
       (∃ i j, b i > 0 ∧ b j < 0 ∧ x = |b j| • basis i + |b i| • basis j)}

theorem intersection_generators_finite (b : E p) : (IntersectionGenerators b).Finite := by
  unfold IntersectionGenerators;
  exact Set.Finite.subset ( Set.toFinite ( Set.range ( fun k : Fin p => basis k ) ∪ Set.range ( fun p : Fin p × Fin p => |b p.2| • basis p.1 + |b p.1| • basis p.2 ) ) ) fun x hx => by aesop;

end
