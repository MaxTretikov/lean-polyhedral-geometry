/-
  InteriorPoint.lean

  Farkas combination that produces interior points for all dimensions.

  This module implements the Farkas point construction by summing over ALL pairs
  of positive/negative generators plus all zero generators. When G is the standard
  basis and b has mixed signs, the result has ALL coordinates strictly positive,
  guaranteeing an interior point.

  PAPER REFERENCE: Algorithm 4 (FarkasCombination) from paper.tex.
-/

import PolyhedralGeometry.Generators
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.OfFn

noncomputable section

open Matrix BigOperators PolyhedralGeometry
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace InteriorPoint

/-! ## Farkas Point Definition -/

variable {p : ℕ}

/-- The Farkas Point: sums over ALL pairs of positive/negative generators
    (weighted to cancel inner product with b) plus all zero generators. -/
def FarkasPoint (G : List (Vec p)) (b : Vec p) : Vec p :=
  let pos := posGeneratorsList G b
  let neg := negGeneratorsList G b
  let zeros := zeroGeneratorsList G b
  let sum_pairs := pos.foldl (fun acc1 g1 =>
    acc1 + neg.foldl (fun acc2 g2 =>
      acc2 + |⟪b, g2⟫_ℝ| • g1 + |⟪b, g1⟫_ℝ| • g2) (0 : Vec p)) (0 : Vec p)
  let sum_zeros := zeros.foldl (fun acc g => acc + g) (0 : Vec p)
  sum_pairs + sum_zeros

/-- The standard basis vectors in R^p as a list. -/
def standardBasisList (p : ℕ) : List (Vec p) :=
  List.ofFn (fun i : Fin p => EuclideanSpace.basisFun (Fin p) ℝ i)

/-! ## Helper Lemmas -/

/-- Helper lemma: foldl with addition can separate the initial accumulator. -/
lemma foldl_add_const {α β : Type*} [AddCommMonoid β] (f : α → β) (L : List α) (z : β) :
    List.foldl (fun acc x => acc + f x) z L = z + List.foldl (fun acc x => acc + f x) 0 L := by
  induction L generalizing z with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (z + f x), ih (f x)]
    abel

/-- Lemma: foldl addition starting from 0 equals sum.
    Note: This could also be proved using List.foldl_eq_foldr for commutative operations. -/
lemma foldl_add_eq_sum {α : Type*} [AddCommMonoid α] (L : List α) :
    List.foldl (fun acc x => acc + x) 0 L = L.sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.sum_cons, zero_add]
    rw [foldl_add_const (fun y => y) xs x, ih]

/-- Lemma for the inner fold identity in the Farkas point calculation. -/
lemma inner_fold_identity (N : List (Vec p)) (c : Vec p → ℝ) (d : Vec p → ℝ) (g1 : Vec p) :
    N.foldl (fun acc2 g2 => acc2 + c g2 • g1 + d g1 • g2) (0 : Vec p) =
    (N.map c).sum • g1 + d g1 • N.sum := by
  induction N with
  | nil => simp
  | cons g2 N' ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, add_smul, smul_add, zero_add]
    have h_comm : ∀ (L : List (Vec p)) (x : Vec p),
        List.foldl (fun acc2 g2 => acc2 + c g2 • g1 + d g1 • g2) x L =
        x + List.foldl (fun acc2 g2 => acc2 + c g2 • g1 + d g1 • g2) 0 L := by
      intro L x
      induction L generalizing x with
      | nil => simp
      | cons y ys ihl =>
        simp only [List.foldl_cons, zero_add]
        rw [ihl (x + c y • g1 + d g1 • y), ihl (c y • g1 + d g1 • y)]
        abel
    rw [h_comm, ih]
    abel

/-- The double foldl structure can be decomposed into sums of scaled vectors. -/
theorem double_fold_identity (P N : List (Vec p)) (c d : Vec p → ℝ) :
    P.foldl (fun acc1 g1 => acc1 + N.foldl (fun acc2 g2 =>
      acc2 + c g2 • g1 + d g1 • g2) (0 : Vec p)) (0 : Vec p) =
    (N.map c).sum • P.sum + (P.map d).sum • N.sum := by
  induction P with
  | nil => simp
  | cons g1 P' ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, add_smul, smul_add, zero_add]
    rw [inner_fold_identity]
    have h_comm : ∀ (L : List (Vec p)) (x : Vec p),
        List.foldl (fun acc1 g1 => acc1 + N.foldl (fun acc2 g2 => acc2 + c g2 • g1 + d g1 • g2) 0) x L =
        x + List.foldl (fun acc1 g1 => acc1 + N.foldl (fun acc2 g2 => acc2 + c g2 • g1 + d g1 • g2) 0) 0 L := by
      intro L x
      induction L generalizing x with
      | nil => simp
      | cons y ys ihl =>
        simp only [List.foldl_cons, zero_add]
        rw [ihl (x + N.foldl _ 0), ihl (N.foldl _ 0)]
        abel
    rw [h_comm, ih]
    abel

/-- The Farkas Point decomposes into weighted sums. -/
theorem farkas_decomposition (G : List (Vec p)) (b : Vec p) :
    let pos := posGeneratorsList G b
    let neg := negGeneratorsList G b
    let zeros := zeroGeneratorsList G b
    let P_val := (pos.map (fun g => |⟪b, g⟫_ℝ|)).sum
    let N_val := (neg.map (fun g => |⟪b, g⟫_ℝ|)).sum
    FarkasPoint G b = N_val • pos.sum + P_val • neg.sum + zeros.sum := by
  dsimp only [FarkasPoint, posGeneratorsList, negGeneratorsList, zeroGeneratorsList]
  rw [double_fold_identity]
  congr 1
  exact foldl_add_eq_sum _

/-- Helper: the k-th coordinate of a list sum of vectors equals the sum of k-th coordinates -/
lemma list_sum_coord (L : List (Vec p)) (k : Fin p) :
    (L.sum) k = (L.map (fun v => v k)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, PiLp.add_apply, ih]

/-- Helper: sum of indicator function over a nodup list containing k equals 1 -/
lemma sum_ite_eq_one_of_mem {k : α} {L : List α} [DecidableEq α]
    (h_nodup : L.Nodup) (h_mem : k ∈ L) :
    (L.map (fun i => if i = k then (1 : ℝ) else 0)).sum = 1 := by
  induction L with
  | nil => simp at h_mem
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have ⟨h_not_mem, h_nodup_xs⟩ := List.nodup_cons.mp h_nodup
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      subst heq
      simp only [↓reduceIte]
      have : (xs.map (fun i => if i = k then (1 : ℝ) else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        intro heq
        exact h_not_mem (heq ▸ hi)
      rw [this]
      ring
    | inr hmem =>
      have hne : x ≠ k := fun heq => h_not_mem (heq ▸ hmem)
      simp only [hne, ↓reduceIte, zero_add]
      exact ih h_nodup_xs hmem

/-- Helper: sum of indicator function over a list not containing k equals 0 -/
lemma sum_ite_eq_zero_of_not_mem {k : α} {L : List α} [DecidableEq α]
    (h_not_mem : k ∉ L) :
    (L.map (fun i => if i = k then (1 : ℝ) else 0)).sum = 0 := by
  apply List.sum_eq_zero
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  intro heq
  exact h_not_mem (heq ▸ hi)

/-- The k-th coordinate of the sum of a filtered list of standard basis vectors is 1 if
    the k-th basis vector satisfies the predicate, and 0 otherwise. -/
lemma sum_filter_basis_coord (p : ℕ) (P : Vec p → Prop) [DecidablePred P] (k : Fin p) :
    let G := List.ofFn (fun i : Fin p => EuclideanSpace.basisFun (Fin p) ℝ i)
    let L := G.filter P
    (L.sum) k = if P (EuclideanSpace.basisFun (Fin p) ℝ k) then 1 else 0 := by
  simp only
  rw [List.ofFn_eq_map, List.filter_map]
  have h_filter_eq : (fun b => decide (P b)) ∘ (fun i => EuclideanSpace.basisFun (Fin p) ℝ i) =
      fun i => decide (P (EuclideanSpace.basisFun (Fin p) ℝ i)) := rfl
  simp only [h_filter_eq]
  set L := (List.finRange p).filter (fun i => P (EuclideanSpace.basisFun (Fin p) ℝ i)) with hL
  rw [list_sum_coord]
  have h_basis_val : ∀ i : Fin p, (EuclideanSpace.basisFun (Fin p) ℝ i) k = if i = k then 1 else 0 :=
    fun i => by
      simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, eq_comm]
  simp only [List.map_map, Function.comp_def, h_basis_val]
  have h_nodup : L.Nodup := List.Nodup.filter _ (List.nodup_finRange p)
  by_cases hPk : P (EuclideanSpace.basisFun (Fin p) ℝ k)
  · simp only [hPk, ↓reduceIte]
    have h_k_in_L : k ∈ L := by
      simp only [hL, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      exact hPk
    exact sum_ite_eq_one_of_mem h_nodup h_k_in_L
  · simp only [hPk, ↓reduceIte]
    have h_k_not_in_L : k ∉ L := by
      simp only [hL, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      exact hPk
    exact sum_ite_eq_zero_of_not_mem h_k_not_in_L

/-- Inner product distributes over list sum. Uses inner_add_right inductively. -/
lemma inner_list_sum (b : Vec p) (L : List (Vec p)) :
    ⟪b, L.sum⟫_ℝ = (L.map (fun g => ⟪b, g⟫_ℝ)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.sum_cons, List.map_cons, inner_add_right, ih]

/-! ## Main Theorems -/

/-- The Farkas Point lies in the hyperplane defined by b. -/
theorem farkas_in_hyperplane (G : List (Vec p)) (b : Vec p)
    (h_mixed : (∃ g ∈ G, ⟪b, g⟫_ℝ > 0) ∧ (∃ g ∈ G, ⟪b, g⟫_ℝ < 0)) :
    ⟪b, FarkasPoint G b⟫_ℝ = 0 := by
  have h_decomp := farkas_decomposition G b
  rw [h_decomp, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
  -- Inner product of b with pos.sum equals P_val (sum of positive inner products)
  have h_inner_pos : ⟪b, (posGeneratorsList G b).sum⟫_ℝ =
      ((posGeneratorsList G b).map (fun g => |⟪b, g⟫_ℝ|)).sum := by
    rw [inner_list_sum]
    congr 1
    apply List.map_congr_left
    intro g hg
    simp only [posGeneratorsList, List.mem_filter, decide_eq_true_eq] at hg
    exact (abs_of_pos hg.2).symm
  -- Inner product of b with neg.sum equals -N_val (sum of negative inner products)
  have h_inner_neg : ⟪b, (negGeneratorsList G b).sum⟫_ℝ =
      -((negGeneratorsList G b).map (fun g => |⟪b, g⟫_ℝ|)).sum := by
    rw [inner_list_sum]
    have h_eq : (negGeneratorsList G b).map (fun g => ⟪b, g⟫_ℝ) =
        (negGeneratorsList G b).map (fun g => -|⟪b, g⟫_ℝ|) := by
      apply List.map_congr_left
      intro g hg
      simp only [negGeneratorsList, List.mem_filter, decide_eq_true_eq] at hg
      rw [abs_of_neg hg.2]
      ring
    rw [h_eq]
    induction (negGeneratorsList G b) with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  -- Inner product of b with zeros.sum is 0
  have h_inner_zeros : ⟪b, (zeroGeneratorsList G b).sum⟫_ℝ = 0 := by
    rw [inner_list_sum]
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [zeroGeneratorsList, List.mem_filter, decide_eq_true_eq] at hg
    exact hg.2
  rw [h_inner_pos, h_inner_neg, h_inner_zeros]
  ring

/-- The Farkas Point is a conic combination of generators. -/
theorem farkas_in_cone (G : List (Vec p)) (b : Vec p)
    (h_gen : ∀ g ∈ G, g ∈ nonnegOrthant p) :
    FarkasPoint G b ∈ nonnegOrthant p := by
  have h_decomp := farkas_decomposition G b
  rw [h_decomp]
  intro i
  -- P_val and N_val are non-negative (sums of absolute values)
  have h_P_nonneg : 0 ≤ ((posGeneratorsList G b).map (fun g => |⟪b, g⟫_ℝ|)).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  have h_N_nonneg : 0 ≤ ((negGeneratorsList G b).map (fun g => |⟪b, g⟫_ℝ|)).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  -- Sum of generators in each filtered list has non-negative i-th coordinate
  have h_pos_sum_nonneg : 0 ≤ ((posGeneratorsList G b).sum) i := by
    rw [list_sum_coord]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    simp only [posGeneratorsList, List.mem_filter] at hg
    exact h_gen g hg.1 i
  have h_neg_sum_nonneg : 0 ≤ ((negGeneratorsList G b).sum) i := by
    rw [list_sum_coord]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    simp only [negGeneratorsList, List.mem_filter] at hg
    exact h_gen g hg.1 i
  have h_zeros_sum_nonneg : 0 ≤ ((zeroGeneratorsList G b).sum) i := by
    rw [list_sum_coord]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    simp only [zeroGeneratorsList, List.mem_filter] at hg
    exact h_gen g hg.1 i
  -- The i-th coordinate of smul • v is smul * (v i)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have h1 : 0 ≤ ((negGeneratorsList G b).map (fun g => |⟪b, g⟫_ℝ|)).sum * ((posGeneratorsList G b).sum) i :=
    mul_nonneg h_N_nonneg h_pos_sum_nonneg
  have h2 : 0 ≤ ((posGeneratorsList G b).map (fun g => |⟪b, g⟫_ℝ|)).sum * ((negGeneratorsList G b).sum) i :=
    mul_nonneg h_P_nonneg h_neg_sum_nonneg
  linarith

/-! ## Interior Point Result -/

/-- Helper: sum of positive reals in a non-empty list is positive.
    Uses List.sum_nonneg from Mathlib.Algebra.Order.BigOperators.Group.List -/
lemma sum_pos_of_all_pos {l : List ℝ} (hl : ∀ x ∈ l, 0 < x) (hne : l ≠ []) : 0 < l.sum := by
  cases l with
  | nil => contradiction
  | cons x xs =>
    simp only [List.sum_cons]
    have hx : 0 < x := hl x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : 0 ≤ xs.sum := List.sum_nonneg (fun y hy => le_of_lt (hl y (List.mem_cons.mpr (Or.inr hy))))
    linarith

/-- Helper: element of a nonneg list is bounded by the sum.
    Could also use List.Sublist.sum_le_sum from Mathlib. -/
lemma le_sum_of_mem {l : List ℝ} (hl : ∀ x ∈ l, 0 ≤ x) {x : ℝ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      simp only [List.sum_cons]
      have hys : 0 ≤ ys.sum := List.sum_nonneg (fun z hz => hl z (List.mem_cons.mpr (Or.inr hz)))
      linarith
    | inr h =>
      simp only [List.sum_cons]
      have := ih (fun z hz => hl z (List.mem_cons.mpr (Or.inr hz))) h
      have hy : 0 ≤ y := hl y (List.mem_cons.mpr (Or.inl rfl))
      linarith

/-- Key theorem: When b has mixed signs, the Farkas Point from the
    standard basis has ALL coordinates strictly positive (is in the interior). -/
theorem farkas_interior (p : ℕ) (b : Vec p)
    (h_mixed : (∃ i : Fin p, b i > 0) ∧ (∃ j : Fin p, b j < 0)) :
    let G := standardBasisList p
    let y := FarkasPoint G b
    ∀ k : Fin p, y k > 0 := by
  set G := List.ofFn (fun i : Fin p => EuclideanSpace.basisFun (Fin p) ℝ i)
  set pos := G.filter (fun g => ⟪b, g⟫_ℝ > 0)
  set neg := G.filter (fun g => ⟪b, g⟫_ℝ < 0)
  set zeros := G.filter (fun g => ⟪b, g⟫_ℝ = 0)
  set P_val := (pos.map (fun g => |⟪b, g⟫_ℝ|)).sum
  set N_val := (neg.map (fun g => |⟪b, g⟫_ℝ|)).sum
  have h_y : FarkasPoint G b = N_val • pos.sum + P_val • neg.sum + zeros.sum :=
    farkas_decomposition G b
  have h_P_pos : 0 < P_val := by
    obtain ⟨i, hi⟩ := h_mixed.left
    have h_inner_eq : ⟪b, EuclideanSpace.basisFun (Fin p) ℝ i⟫_ℝ = b i := by
      simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right,
        RCLike.conj_to_real, one_mul]
    have h_basis_i_in_pos : EuclideanSpace.basisFun (Fin p) ℝ i ∈ pos := by
      simp only [pos, G, List.mem_filter, List.mem_ofFn]
      exact ⟨⟨i, rfl⟩, by simp only [decide_eq_true_eq, h_inner_eq, hi]⟩
    have h_mem : |⟪b, EuclideanSpace.basisFun (Fin p) ℝ i⟫_ℝ| ∈
        List.map (fun g => |⟪b, g⟫_ℝ|) pos :=
      List.mem_map.mpr ⟨_, h_basis_i_in_pos, rfl⟩
    have h_abs_pos : 0 < |⟪b, EuclideanSpace.basisFun (Fin p) ℝ i⟫_ℝ| :=
      abs_pos.mpr (by simp [EuclideanSpace.inner_single_right]; linarith)
    have h_le : |⟪b, EuclideanSpace.basisFun (Fin p) ℝ i⟫_ℝ| ≤ P_val :=
      le_sum_of_mem (fun x hx => by obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) h_mem
    linarith
  have h_N_pos : 0 < N_val := by
    obtain ⟨j, hj⟩ := h_mixed.right
    have h_inner_eq_j : ⟪b, EuclideanSpace.basisFun (Fin p) ℝ j⟫_ℝ = b j := by
      simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right,
        RCLike.conj_to_real, one_mul]
    have h_basis_j_in_neg : EuclideanSpace.basisFun (Fin p) ℝ j ∈ neg := by
      simp only [neg, G, List.mem_filter, List.mem_ofFn]
      exact ⟨⟨j, rfl⟩, by simp only [decide_eq_true_eq, h_inner_eq_j, hj]⟩
    have h_mem : |⟪b, EuclideanSpace.basisFun (Fin p) ℝ j⟫_ℝ| ∈
        List.map (fun g => |⟪b, g⟫_ℝ|) neg :=
      List.mem_map.mpr ⟨_, h_basis_j_in_neg, rfl⟩
    have h_le : |⟪b, EuclideanSpace.basisFun (Fin p) ℝ j⟫_ℝ| ≤ N_val :=
      le_sum_of_mem (fun x hx => by obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) h_mem
    have h_pos : 0 < |⟪b, EuclideanSpace.basisFun (Fin p) ℝ j⟫_ℝ| :=
      abs_pos.mpr (by simp [EuclideanSpace.inner_single_right]; linarith)
    linarith
  have h_sum_pos : ∀ k : Fin p, (pos.sum) k = if b k > 0 then 1 else 0 := by
    intro k
    convert sum_filter_basis_coord p (fun g => ⟪b, g⟫_ℝ > 0) k using 2
    simp [EuclideanSpace.inner_single_right]
  have h_sum_neg : ∀ k : Fin p, (neg.sum) k = if b k < 0 then 1 else 0 := by
    intro k
    convert sum_filter_basis_coord p (fun g => ⟪b, g⟫_ℝ < 0) k using 2
    simp [EuclideanSpace.inner_single_right]
  have h_sum_zeros : ∀ k : Fin p, (zeros.sum) k = if b k = 0 then 1 else 0 := by
    intro k
    convert sum_filter_basis_coord p (fun g => ⟪b, g⟫_ℝ = 0) k using 2
    simp [EuclideanSpace.inner_single_right]
  have h_eq : standardBasisList p = G := by
    simp only [standardBasisList, G, List.ofFn_eq_map]
  simp only [h_eq]
  intro k
  have h_expand : (FarkasPoint G b) k = N_val * (pos.sum k) + P_val * (neg.sum k) + (zeros.sum k) := by
    rw [h_y]
    rfl
  rw [h_expand]
  specialize h_sum_pos k
  specialize h_sum_neg k
  specialize h_sum_zeros k
  rcases lt_trichotomy (b k) 0 with h_neg | h_zero | h_pos
  · have hne : b k ≠ 0 := ne_of_lt h_neg
    simp only [not_lt.mpr (le_of_lt h_neg), if_false, h_neg, if_true, hne] at h_sum_pos h_sum_neg h_sum_zeros
    simp only [h_sum_pos, h_sum_neg, h_sum_zeros, mul_zero, mul_one, zero_add, add_zero]
    linarith
  · simp only [h_zero, lt_irrefl, if_false, if_true] at h_sum_pos h_sum_neg h_sum_zeros
    simp only [h_sum_pos, h_sum_neg, h_sum_zeros, mul_zero, zero_add, add_zero]
    linarith
  · have hne : b k ≠ 0 := ne_of_gt h_pos
    simp only [h_pos, if_true, not_lt.mpr (le_of_lt h_pos), if_false, hne] at h_sum_pos h_sum_neg h_sum_zeros
    simp only [h_sum_pos, h_sum_neg, h_sum_zeros, mul_zero, mul_one]
    linarith

/-! ## Interface for ConeConstruction -/

/-- Farkas combination using GeneratorSet interface. -/
def farkasCombination (G : GeneratorSet p) (b : Vec p) : Option (Vec p) :=
  let genList := G.s.toList.map G.vec
  let pos := posGeneratorsList genList b
  let neg := negGeneratorsList genList b
  if pos.isEmpty ∧ neg.isEmpty then
    let zeros := zeroGeneratorsList genList b
    if zeros.isEmpty then none
    else some zeros.sum
  else if pos.isEmpty ∨ neg.isEmpty then
    none
  else
    some (FarkasPoint genList b)

/-- The Farkas combination produces a point in the hyperplane. -/
theorem farkasCombination_in_hyperplane {G : GeneratorSet p} {b y : Vec p} :
    farkasCombination G b = some y → ⟪b, y⟫_ℝ = 0 := by
  intro h
  simp only [farkasCombination] at h
  set genList := G.s.toList.map G.vec with h_genList
  set pos := posGeneratorsList genList b with h_pos
  set neg := negGeneratorsList genList b with h_neg
  split_ifs at h with h1 h2 h3
  all_goals simp only [Option.some.injEq] at h
  · rw [← h, inner_list_sum]
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [zeroGeneratorsList, List.mem_filter, decide_eq_true_eq] at hg
    exact hg.2
  · rw [← h]
    apply farkas_in_hyperplane
    simp only [List.isEmpty_iff] at h3
    push_neg at h3
    constructor
    · obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil pos h3.1
      rw [h_pos, posGeneratorsList] at hg
      simp only [List.mem_filter, decide_eq_true_eq] at hg
      exact ⟨g, hg.1, hg.2⟩
    · obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil neg h3.2
      rw [h_neg, negGeneratorsList] at hg
      simp only [List.mem_filter, decide_eq_true_eq] at hg
      exact ⟨g, hg.1, hg.2⟩

/-- The Farkas combination produces a point in the cone. -/
theorem farkasCombination_nonneg {G : GeneratorSet p} {b y : Vec p} :
    farkasCombination G b = some y →
    (∀ i ∈ G.s, G.vec i ∈ nonnegOrthant p) →
    y ∈ nonnegOrthant p := by
  intro h h_gen
  simp only [farkasCombination] at h
  set genList := G.s.toList.map G.vec with h_genList
  set pos := posGeneratorsList genList b with h_pos
  set neg := negGeneratorsList genList b with h_neg
  -- All generators in genList are in nonnegOrthant
  have h_gen_list : ∀ g ∈ genList, g ∈ nonnegOrthant p := by
    intro g hg
    simp only [h_genList, List.mem_map] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    exact h_gen i (Finset.mem_toList.mp hi)
  split_ifs at h with h1 h2 h3
  all_goals simp only [Option.some.injEq] at h
  · -- Case: pos and neg are empty, y = zeros.sum
    rw [← h]
    intro k
    rw [list_sum_coord]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    simp only [zeroGeneratorsList, List.mem_filter] at hg
    exact h_gen_list g hg.1 k
  · -- Case: pos and neg are non-empty, y = FarkasPoint genList b
    rw [← h]
    exact farkas_in_cone genList b h_gen_list

/-!
## g_vec: Farkas Combination Generator
-/

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

end InteriorPoint
