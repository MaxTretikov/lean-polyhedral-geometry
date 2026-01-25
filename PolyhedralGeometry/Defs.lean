import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

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

end

/-! ## Standard Basis and Orthant for ℝ^p -/

section
variable {p : ℕ}

/-- The standard Euclidean space ℝ^p. -/
abbrev Vec (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- The nonnegative orthant: all vectors with nonnegative coordinates. -/
def nonnegOrthant (p : ℕ) : Set (Vec p) := { y | ∀ i, 0 ≤ y i }

/-- The set of standard basis vectors. -/
def StandardBasisSet : Set (Vec p) := Set.range (EuclideanSpace.basisFun (Fin p) ℝ)

/-- The nonnegative orthant. -/
def OrthantSet : Set (Vec p) := nonnegOrthant p

lemma basisFun_nonneg (i : Fin p) : EuclideanSpace.basisFun (Fin p) ℝ i ∈ nonnegOrthant p := by
  intro k
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]
  split_ifs <;> linarith

lemma basisFun_injective : Function.Injective (EuclideanSpace.basisFun (Fin p) ℝ) :=
  (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.injective

/-- A set G generates a cone C if C equals the set of non-negative linear combinations of G. -/
def IsGeneratorSet (G : Set (Vec p)) (C : Set (Vec p)) : Prop :=
  C = {x | ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (v : ι → Vec p),
            (∀ i ∈ s, 0 ≤ c i) ∧ (∀ i ∈ s, v i ∈ G) ∧ x = ∑ i ∈ s, c i • v i}

theorem orthant_generated_by_std_basis :
    IsGeneratorSet (StandardBasisSet (p := p)) (OrthantSet (p := p)) := by
  classical
  ext x
  constructor
  · intro hx
    use Fin p, Finset.univ, x, (EuclideanSpace.basisFun (Fin p) ℝ)
    refine ⟨?_, ?_, ?_⟩
    · intro i _
      exact hx i
    · intro i _
      exact ⟨i, rfl⟩
    · have hxsum : x = ∑ i, x i • EuclideanSpace.basisFun (Fin p) ℝ i := by
        ext k
        simpa [EuclideanSpace.basisFun_apply, smul_eq_mul] using
          (congrArg (fun f => f k) (pi_eq_sum_univ' (x := x.ofLp)))
      simpa using hxsum
  · intro hx
    rcases hx with ⟨ι, t, c, v, h_c, h_v, rfl⟩
    intro k
    have h_nonneg : ∀ i ∈ t, 0 ≤ c i * v i k := by
      intro i hi
      have hc : 0 ≤ c i := h_c i hi
      have hv : 0 ≤ v i k := by
        rcases h_v i hi with ⟨j, h_eq⟩
        simpa [h_eq] using (basisFun_nonneg (p := p) j) k
      exact mul_nonneg hc hv
    have h_sum : (∑ i ∈ t, c i • v i) k = ∑ i ∈ t, c i * v i k := by
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 ≤ ∑ i ∈ t, c i * v i k := by
      exact Finset.sum_nonneg h_nonneg
    simpa [h_sum] using this

end
