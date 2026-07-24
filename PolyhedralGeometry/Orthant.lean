/-
  Orthant.lean

  Interior characterization of the nonnegative orthant: the interior of
  `nonnegOrthant n` consists exactly of the vectors all of whose coordinates
  are strictly positive.

  The proof transfers the problem along the homeomorphism between
  `EuclideanSpace ℝ (Fin n)` and the product space `Fin n → ℝ`, where the
  orthant is a finite product of the closed half-lines `Set.Ici 0` and the
  interior of a finite product is the product of the interiors.
-/

import LinearAlgebraHelpers.Defs

noncomputable section

/-- The interior of the nonnegative orthant is the set of vectors with all
coordinates strictly positive. -/
theorem interior_nonnegOrthant (n : ℕ) :
    interior (nonnegOrthant n) = {x : Vec n | ∀ i, 0 < x i} := by
  have h : nonnegOrthant n
      = (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph ⁻¹'
          (Set.univ.pi fun _ : Fin n => Set.Ici (0 : ℝ)) := by
    ext x
    simp only [nonnegOrthant, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi,
      Set.mem_Ici]
    exact Iff.rfl
  rw [h, ← Homeomorph.preimage_interior, interior_pi_set Set.finite_univ]
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, interior_Ici, Set.mem_Ioi,
    Set.mem_setOf_eq]
  exact Iff.rfl

/-- Membership in the interior of the nonnegative orthant is equivalent to all
coordinates being strictly positive. -/
theorem mem_interior_nonnegOrthant_iff {n : ℕ} (x : Vec n) :
    x ∈ interior (nonnegOrthant n) ↔ ∀ i, 0 < x i := by
  rw [interior_nonnegOrthant]
  exact Iff.rfl

end
