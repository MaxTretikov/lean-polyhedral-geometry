import PolyhedralGeometry.Cone
import PolyhedralGeometry.Generators
import PolyhedralGeometry.InteriorPoint
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Analysis.InnerProductSpace.Subspace

section
variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

lemma halfspace_convex (s : Set V) (h_halfspace_s : Halfspace s) : Convex ℝ s := by
  intro x _ y _ a b _ _ h_a_b_one
  rcases h_halfspace_s with ⟨f, ⟨c, rfl⟩⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul]
  calc
    a * f x + b * f y
      ≤ a * c + b * c := by apply add_le_add <;> apply mul_le_mul_of_nonneg_left <;> assumption
    _ = (a + b) * c := by rw [add_mul]
    _ = 1 * c := by rw [h_a_b_one]
    _ = c := one_mul c

theorem poly_convex (s : Set V) (h_poly_s : IsPolyhedron s) : Convex ℝ s := by
  rcases h_poly_s with ⟨_, _, _, h_halfspace, rfl⟩
  exact convex_iInter fun i => halfspace_convex _ (h_halfspace i)

end

section
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
open Finset Module

theorem caratheordory (s : Set V) : ∀ x ∈ conicalHull s, isConicalCombo_aux s x (finrank ℝ V) := by
  rintro x h
  rcases (reindex_conicalCombo s x).mp h with ⟨n, h⟩
  revert h
  induction n with
  | zero =>
      intro h
      exact isconicalCombo_aux_le s x (Nat.zero_le _) h
  | succ N ih =>
      intro h
      by_cases hN : N + 1 ≤ finrank ℝ V
      · exact isconicalCombo_aux_le s x hN h
      push_neg at hN
      rcases h with ⟨a, v, h_av, h_x_combo⟩
      apply ih

      wlog h_a_all_pos : ∀ i < N + 1, a i ≠ 0 generalizing
      · push_neg at h_a_all_pos
        apply reduce_conicalCombo s x v h_a_all_pos
        exact ⟨h_av, h_x_combo⟩

      have : ¬ LinearIndepOn ℝ v (range (N + 1)) := by
        intro h
        absurd hN
        rw [not_lt]
        have := LinearIndepOn.encard_le_toENat_rank h
        simp only [Set.encard_coe_eq_coe_finsetCard] at this
        simp at this
        have := ENat.toNat_le_toNat this
          (by simp; exact Module.rank_lt_aleph0 ℝ V)
        exact this
      replace := (not_congr linearIndepOn_iff'').mp this
      push_neg at this
      rcases this with ⟨t, b, h_t_sub_range, h_b_comp, h_b_combo_eq_0, j, h_jt, h_j_ne_0⟩
      wlog h' : t = range (N + 1) generalizing t
      · apply this (range (N + 1))
        all_goals clear this h'; try simp
        · intro i hiN
          have : i ∉ t := by
            intro h_it
            have := h_t_sub_range h_it
            have := mem_range.mp this
            linarith
          exact h_b_comp i this
        · rw [← h_b_combo_eq_0]
          symm
          apply sum_subset
          · assumption
          · intro i _ h_it
            rw [h_b_comp i h_it]
            simp
        · have := h_t_sub_range h_jt
          simp only [Finset.coe_range, Set.mem_Iio] at this
          omega
      rw [h'] at h_b_combo_eq_0 h_jt
      clear h_t_sub_range h_b_comp h' t
      wlog h_b_j_pos : b j > 0 generalizing b
      · let b' := -b
        apply this b' <;> simp [b']
        · assumption
        · simp [h_b_combo_eq_0]
        · simp at h_b_j_pos
          exact lt_of_le_of_ne h_b_j_pos h_j_ne_0
      clear h_j_ne_0

      let ratios : Finset ℝ := ((Finset.range (N + 1)).filter (λ i => b i ≠ 0)).image (λ i => a i / b i)
      let ratios_non_neg : Finset ℝ := ratios.filter (λ r => r ≥ 0)
      have hratio_nonem : ratios_non_neg.Nonempty := by
        unfold ratios_non_neg
        unfold ratios
        have a_j_geq_zero : a j ≥ 0 := by
          cases (h_av j (Finset.mem_range.mp h_jt)) <;> linarith
        unfold Finset.Nonempty
        use a j / b j
        have hj₁ : j ∈ {i ∈ range (N + 1) | b i ≠ 0} := by
          simp
          refine ⟨?_,?_⟩
          · have := Finset.mem_range.mp h_jt; omega
          · linarith
        simp
        refine ⟨?_,?_⟩
        · use j
          refine ⟨⟨?_,?_⟩,?_⟩
          · have := Finset.mem_range.mp h_jt; omega
          · linarith
          · rfl
        apply div_nonneg <;> linarith

      set β := (ratios_non_neg : Finset ℝ).min' hratio_nonem with hβ_def
      have hβ_mem : β ∈ ratios_non_neg := (ratios_non_neg).min'_mem hratio_nonem
      have ⟨h_ratios, h_βgeq0⟩ := mem_filter.mp hβ_mem
      rcases mem_image.mp h_ratios with ⟨i₀,i₀_in_range,hi₀_is_index_β⟩

      replace h_b_combo_eq_0 : ∑ i ∈ range (N + 1),  (β * b i) • v i = 0 := by
        have : β • (∑ i ∈ range (N + 1),  b i • v i) = 0 := by
          exact smul_eq_zero_of_right β h_b_combo_eq_0
        have : ∑ i ∈ range (N + 1),  β • b i • v i = 0 := by
          rw [← Finset.smul_sum]
          exact this
        simp [← smul_assoc] at this
        exact this
      rw [← sub_zero (∑ i ∈ range (N + 1), a i • v i)] at h_x_combo
      rw [← h_b_combo_eq_0] at h_x_combo
      have x_plus_zero : x = ∑ i ∈ range (N + 1), ((a - β • b) i • v i) := by
        simp [sub_smul, Finset.sum_sub_distrib]
        exact h_x_combo

      have h_all_ai_βbi_nonneg : ∀ i < N + 1, 0 ≤ (a i - β * b i)  := by
        intro j h_j_in_range
        have h_aj_non_neg : 0 ≤ a j  := by
              rcases h_av j h_j_in_range with h_aj_zero | ⟨h_ai_geq_zero,_⟩ <;> linarith
        by_cases h_bj_zero : b j ≤ 0
        · have : β * b j ≤ 0 := by
            exact mul_nonpos_of_nonneg_of_nonpos h_βgeq0 h_bj_zero
          have : - β * b j ≥ 0 := by
            simp
            exact this
          linarith
        · push_neg at h_bj_zero
          have h_β_is_min : β ≤ a j / b j  := by
            have h_ajbj_in_ratios_non_neg : (a j / b j) ∈ ratios_non_neg := by
              unfold ratios_non_neg
              repeat rw [mem_filter, mem_image]
              refine ⟨?_,?_⟩
              · use j
                refine ⟨?_,rfl⟩
                · apply mem_filter.mpr
                  refine ⟨?_,?_⟩
                  · exact mem_range.mpr h_j_in_range
                  · linarith
              · apply div_nonneg
                · exact h_aj_non_neg
                · linarith [h_bj_zero]
            apply Finset.min'_le ratios_non_neg (a j / b j) h_ajbj_in_ratios_non_neg

          have : β * b j ≤ a j / b j * b j  := by
            exact mul_le_mul_of_nonneg_right h_β_is_min (le_of_lt h_bj_zero)

          have : β * b j ≤ a j := by
            exact (le_div_iff₀ h_bj_zero).mp h_β_is_min

          exact sub_nonneg_of_le this

      have h_i₀_ai_βbi_zero : (a - β • b) i₀ = 0 := by
        rw [← hi₀_is_index_β]
        have hbi₀_nonzero : b i₀ ≠ 0 := (mem_filter.mp i₀_in_range).2
        simp [hbi₀_nonzero]

      have : i₀ < N + 1 := by
        rw [← mem_range]
        exact (mem_filter.mp i₀_in_range).1
      apply reduce_conicalCombo s x v ⟨i₀, this, h_i₀_ai_βbi_zero⟩
      refine ⟨?_, x_plus_zero⟩
      intro i h_i
      right
      constructor
      · exact h_all_ai_βbi_nonneg i h_i
      · rcases h_av i h_i with h | h
        · absurd h
          exact h_a_all_pos i h_i
        · exact h.2

end

section
variable {ι : Type u}

lemma nonneg_orthant_closed : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i } :=
  (Set.setOf_forall fun i (x : ι → ℝ) => 0 ≤ x i) ▸
  isClosed_iInter fun i => IsClosed.preimage (continuous_apply i) isClosed_Ici

variable [Finite ι] [DecidableEq ι]

lemma nonneg_orthant_gens :
    {x : ι → ℝ | ∀ i, 0 ≤ x i } = conicalHull.{_, u} (Set.range (Pi.basisFun ℝ ι)) := by
  ext x; constructor <;> intro h
  haveI := Fintype.ofFinite ι
  · use ι, Finset.univ, x, (Pi.basisFun ℝ ι)
    constructor
    · intro i h'
      right
      constructor
      · exact h i
      · use i
    · -- Use mathlib's pi_eq_sum_univ' which decomposes along Pi.single i 1
      convert pi_eq_sum_univ' x using 2
      ext i
      simp [Pi.basisFun_apply]
  · rcases h with ⟨α, t, a, v, h₁, rfl⟩
    intro i
    simp
    apply Finset.sum_nonneg
    intro x h_xt
    rcases h₁ x h_xt with h | h
    · simp [h]
    · apply mul_nonneg
      · exact h.left
      · rcases h.right with ⟨j, h⟩
        rw [← h]
        simp only [Pi.basisFun_apply, Pi.single_apply]
        apply ite_nonneg <;> norm_num

end

section
variable {V : Type*} [DecidableEq V] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
open Set Module

private abbrev d_subsets (s : Set V) := {t : Finset V | (↑t : Set V) ⊆ s ∧ t.card ≤ finrank ℝ V}

omit [DecidableEq V] [FiniteDimensional ℝ V] in
lemma d_subsets_finite (s : Set V) : s.Finite → (d_subsets s).Finite := by
  intro h_s
  classical
  let s' : Finset V := h_s.toFinset
  have hs' : (s' : Set V) = s := h_s.coe_toFinset
  refine (s'.powerset.finite_toSet).subset ?_
  intro t ht
  rcases ht with ⟨h_ts, _⟩
  apply Finset.mem_powerset.mpr
  intro x hx
  have hx' : x ∈ (s' : Set V) := by
    have : (↑t : Set V) ⊆ (s' : Set V) := by
      simpa [hs'] using h_ts
    exact this hx
  simpa using hx'

lemma conical_hull_union_conical_hull_d_subsets (s : Set V) :
    conicalHull.{_, 0} s = ⋃ t ∈ d_subsets s, conicalHull.{_, 0} (t : Set V) := by
  ext x; constructor
  · intro hx
    rcases caratheordory s x hx with ⟨a, v, h_av, h_x⟩
    let I : Finset ℕ := (Finset.range (finrank ℝ V)).filter (fun i => a i ≠ 0)
    let t : Finset V := I.image v
    have h_ts : (t : Set V) ⊆ s := by
      intro y hy
      rw [Finset.coe_image] at hy
      rcases hy with ⟨i, hiI, rfl⟩
      have hiI' : i ∈ I := hiI
      rcases Finset.mem_filter.mp hiI' with ⟨hi_range, h_ane⟩
      have hi_lt : i < finrank ℝ V := Finset.mem_range.mp hi_range
      have h_av_i := h_av i hi_lt
      rcases h_av_i with h_zero | h_pos
      · exact (h_ane h_zero).elim
      · exact h_pos.2
    have h_card : t.card ≤ finrank ℝ V := by
      have h_card_I : I.card ≤ finrank ℝ V := by
        simpa using
          (Finset.card_filter_le (s := Finset.range (finrank ℝ V)) (p := fun i => a i ≠ 0))
      dsimp [t]
      exact (Finset.card_image_le.trans h_card_I)
    have h_subset : I ⊆ Finset.range (finrank ℝ V) := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    have h_zero : ∀ i ∈ Finset.range (finrank ℝ V), i ∉ I → a i • v i = 0 := by
      intro i hi_range hi_not
      by_cases h_aeq : a i = 0
      · simp [h_aeq]
      · exfalso
        apply hi_not
        exact Finset.mem_filter.mpr ⟨hi_range, h_aeq⟩
    have h_sum' : ∑ i ∈ I, a i • v i = ∑ i ∈ Finset.range (finrank ℝ V), a i • v i := by
      exact Finset.sum_subset h_subset h_zero
    have h_x_I : x = ∑ i ∈ I, a i • v i := by
      calc
        x = ∑ i ∈ Finset.range (finrank ℝ V), a i • v i := h_x
        _ = ∑ i ∈ I, a i • v i := by symm; exact h_sum'
    refine Set.mem_iUnion.mpr ?_
    refine ⟨t, ?_⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨h_ts, h_card⟩, ?_⟩
    unfold conicalHull isConicalCombo isConicalCombo'
    exact ⟨_, I, a, v, fun i hi => by
      rcases Finset.mem_filter.mp hi with ⟨hi_range, h_ane⟩
      have hi_lt : i < finrank ℝ V := Finset.mem_range.mp hi_range
      have h_av_i := h_av i hi_lt
      rcases h_av_i with h_zero | h_pos
      · exact (h_ane h_zero).elim
      · right; exact ⟨h_pos.1, Finset.mem_image_of_mem v hi⟩, h_x_I⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨ht, hx_t⟩
    rcases ht with ⟨h_ts, _⟩
    rcases hx_t with ⟨ι', t', a, v, h_av, h_sum⟩
    unfold conicalHull isConicalCombo isConicalCombo'
    use ULift ι', t'.map ⟨ULift.up, ULift.up_injective⟩, a ∘ ULift.down, v ∘ ULift.down
    constructor
    · intro i hi
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi
      rcases hi with ⟨j, hj, rfl⟩
      simp only [Function.comp_apply]
      rcases h_av j hj with h_zero | h_pos
      · exact Or.inl h_zero
      · right; exact ⟨h_pos.1, h_ts h_pos.2⟩
    · simp only [Function.comp_apply]
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, ULift.down_up]
      exact h_sum

--worth including this in Mathlib.Data.Finsupp.Single?
theorem Finsupp.single_map [Zero M] {a : α} {b : M} [DecidableEq α] :
    Finsupp.single a b = fun a' => if a = a' then b else 0 := by
  ext a'
  exact single_apply

--proposition 1.3.3(b)
set_option maxHeartbeats 400000 in
theorem conical_hull_closed_of_finite (s : Set V) : s.Finite → IsClosed (conicalHull.{_, 0} s) := by
  generalize h_dim : finrank ℝ V = n
  revert V
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro V _ _ _ _ s h_dim h_s
      by_cases h_n : n = 0
      · rw [h_n] at h_dim
        rw [finrank_zero_iff] at h_dim
        have : s = ∅ ∨ ∃ (x : V), s = {x} := Subsingleton.eq_empty_or_singleton subsingleton_of_subsingleton
        rcases this with h | h <;> exact isClosed_discrete (conicalHull s)
      replace h_n : n > 0 := Nat.zero_lt_of_ne_zero h_n
      rw [conical_hull_union_conical_hull_d_subsets s]
      apply Finite.isClosed_biUnion (d_subsets_finite s h_s)
      intro t ⟨h_ts, h_tcard_le⟩
      clear h_ts h_s s
      let t' : {x // x ∈ t} → V := Subtype.val
      let V' : Submodule ℝ V := Submodule.span ℝ (range t')
      have h_span_le : finrank ℝ V' ≤ t.card := by
        simpa [V', Fintype.card_coe] using (finrank_range_le_card t')
      have h_finrank_le : finrank ℝ V' ≤ n := by
        calc finrank ℝ V' ≤ t.card := h_span_le
          _ ≤ finrank ℝ V := h_tcard_le
          _ = n := h_dim
      rcases lt_or_eq_of_le h_finrank_le with h_span_lt | h_span_eq
      · -- Inductive case: finrank V' < n
        -- Use IH on the submodule V' which has smaller dimension
        let t'' : { x // x ∈ t } → V' := fun x => ⟨t' x, Submodule.subset_span (mem_range_self x)⟩
        have h_finite : (range t'').Finite := Set.finite_range t''
        haveI : DecidableEq V' := Classical.decEq V'
        have h_closed' : IsClosed (conicalHull.{_, 0} (range t'')) :=
          ih (finrank ℝ V') h_span_lt (V := V') (s := range t'') rfl h_finite
        have h_closed_map : IsClosedMap ((↑) : V' → V) :=
          (Submodule.closed_of_finiteDimensional V').isClosedMap_subtype_val
        have h_image_closed : IsClosed (((↑) : V' → V) '' conicalHull.{_, 0} (range t'')) :=
          h_closed_map _ h_closed'
        have h_eq_t : range t' = (t : Set V) := Subtype.range_val
        have h_range : ((↑) : V' → V) '' range t'' = (t : Set V) := by
          have h_range' : ((↑) : V' → V) '' range t'' = range t' := by
            ext y; simp only [Set.mem_image, Set.mem_range]
            constructor
            · rintro ⟨y', ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
            · rintro ⟨x, rfl⟩; exact ⟨t'' x, ⟨x, rfl⟩, rfl⟩
          rw [h_range', h_eq_t]
        have h_image_eq :
            ((↑) : V' → V) '' conicalHull.{_, 0} (range t'') = conicalHull.{_, 0} (t : Set V) := by
          have := conicalHull_image (s := range t'') (f := (Submodule.subtype V'))
          convert this using 1
          rw [← h_range]; rfl
        rw [← h_image_eq]; exact h_image_closed
      · have h_tcard_ge : n ≤ t.card := by
          simp only [h_span_eq] at h_span_le
          exact h_span_le
        have h_tcard_eq : t.card = n := by
          have h_le : t.card ≤ n := h_dim ▸ h_tcard_le
          exact le_antisymm h_le h_tcard_ge
        have h_tcard_eq' : Fintype.card {x // x ∈ t} = finrank ℝ V := by
          simp only [Fintype.card_coe, h_tcard_eq, h_dim]
        have h_t_lin_ind : LinearIndependent ℝ t' := by
          have h_card_eq_span :
              Fintype.card {x // x ∈ t} = finrank ℝ (Submodule.span ℝ (range t')) := by
            simp only [Fintype.card_coe, h_tcard_eq, h_span_eq, V']
          exact (linearIndependent_iff_card_eq_finrank_span).2 h_card_eq_span
        have ht_nonempty : t.Nonempty := by
          apply Finset.card_ne_zero.mp
          have : (0 : ℕ) < t.card := by
            simpa [h_tcard_eq] using h_n
          exact ne_of_gt this
        haveI : Nonempty {x // x ∈ t} := by
          rcases ht_nonempty with ⟨x, hx⟩
          exact ⟨⟨x, hx⟩⟩
        let B : Basis { x // x ∈ t } ℝ V :=
          basisOfLinearIndependentOfCardEqFinrank h_t_lin_ind h_tcard_eq'
        let φ : V ≃ₗ[ℝ] { x // x ∈ t } → ℝ := B.equivFun
        -- Use the standard basis vectors Pi.single i 1 for the subtype index
        haveI : DecidableEq { x // x ∈ t } := Classical.decEq _
        let piStdBasis' : { x // x ∈ t } → ({ x // x ∈ t } → ℝ) := fun i => Pi.single i 1
        have h_φ (x : V) (hxt : x ∈ t) : φ x = piStdBasis' ⟨x, hxt⟩ := by
          unfold φ
          have : x = B ⟨x, hxt⟩ := by
            simp only [coe_basisOfLinearIndependentOfCardEqFinrank, B, t']
          nth_rewrite 1 [this]
          simp only [Basis.equivFun_apply, Basis.repr_self, piStdBasis']
          ext i
          simp only [Finsupp.single_apply, Pi.single_apply, eq_comm]
        have h_φ_symm : φ.symm ∘ piStdBasis' = Subtype.val := by
          ext ⟨x, h_xt⟩
          exact (LinearEquiv.symm_apply_eq φ).mpr (h_φ x h_xt).symm
        have h_φ_symm_image : φ.symm '' (range piStdBasis') = (t : Set V) := by
          rw [← image_univ, ← image_comp, h_φ_symm]
          simp
        have h_cont_φ : Continuous φ := continuous_equivFun_basis B
        have h_closed := nonneg_orthant_closed (ι := { x // x ∈ t })
        -- Use the non-negative orthant characterization
        -- The nonneg orthant is closed and equals conicalHull of piStdBasis'
        have h_orthant_eq : {x : { x // x ∈ t } → ℝ | ∀ i, 0 ≤ x i } =
            conicalHull.{_, 0} (Set.range piStdBasis') := by
          ext x; constructor <;> intro h
          · -- Forward direction: nonneg orthant ⊆ conicalHull
            haveI : Fintype { x // x ∈ t } := Fintype.ofFinite _
            let n := Fintype.card { x // x ∈ t }
            have hn_pos : 0 < n := Fintype.card_pos
            let e : Fin n ≃ { x // x ∈ t } := Fintype.equivFin { x // x ∈ t } |>.symm
            let toIdx : ℕ → { x // x ∈ t } := fun i => if hi : i < n then e ⟨i, hi⟩ else e ⟨0, hn_pos⟩
            use ℕ, (Finset.range n), x ∘ toIdx, piStdBasis' ∘ toIdx
            constructor
            · intro i hi
              have hi' : i < n := Finset.mem_range.mp hi
              right
              constructor
              · simp only [Function.comp_apply, toIdx, hi', dif_pos]; exact h (e ⟨i, hi'⟩)
              · simp only [Function.comp_apply, toIdx, hi', dif_pos]; exact ⟨e ⟨i, hi'⟩, rfl⟩
            · -- Goal: x = ∑ i ∈ Finset.range n, (x ∘ toIdx) i • (piStdBasis' ∘ toIdx) i
              -- First simplify RHS to sum over Fin n
              have h_rhs : ∑ i ∈ Finset.range n, (x ∘ toIdx) i • (piStdBasis' ∘ toIdx) i =
                  ∑ j : Fin n, x (e j) • piStdBasis' (e j) := by
                rw [Finset.sum_fin_eq_sum_range]
                apply Finset.sum_congr rfl
                intro i hi
                have hi' : i < n := Finset.mem_range.mp hi
                simp only [Function.comp_apply, toIdx, hi', ↓reduceDIte]
              rw [h_rhs]
              -- Use Finset.sum_equiv to reindex via e.symm : { x // x ∈ t } ≃ Fin n
              have h_reindex : ∑ i : { x // x ∈ t }, x i • piStdBasis' i =
                  ∑ j : Fin n, x (e j) • piStdBasis' (e j) := by
                exact Finset.sum_equiv e.symm (by simp) (fun i _ => by simp [Equiv.apply_symm_apply])
              rw [← h_reindex]
              -- Now show x = ∑ i, x i • piStdBasis' i
              ext j
              simp only [Finset.sum_apply, Pi.smul_apply, piStdBasis', Pi.single_apply, smul_eq_mul]
              rw [Fintype.sum_eq_single j]
              · simp only [↓reduceIte, mul_one]
              · intro i hij
                rw [if_neg hij.symm]
                ring
          · rcases h with ⟨α, s, a, v, h₁, rfl⟩
            intro i; simp
            apply Finset.sum_nonneg
            intro x h_xs
            rcases h₁ x h_xs with h | h
            · simp [h]
            · apply mul_nonneg h.left
              rcases h.right with ⟨j, hj⟩
              rw [← hj]
              simp only [piStdBasis', Pi.single_apply]
              apply ite_nonneg <;> norm_num
        have h_closed' : IsClosed (conicalHull.{_, 0} (range piStdBasis')) := by
          rw [← h_orthant_eq]; exact h_closed
        have h_eq : conicalHull.{_, 0} (t : Set V) = φ ⁻¹' conicalHull.{_, 0} (range piStdBasis') := by
          rw [← LinearEquiv.image_symm_eq_preimage]
          show conicalHull.{_, 0} (t : Set V) = (↑φ.symm) '' conicalHull.{_, 0} (range piStdBasis')
          have h_image' : (↑φ.symm) '' conicalHull.{_, 0} (range piStdBasis') =
              conicalHull.{_, 0} ((↑φ.symm) '' range piStdBasis') := by
            have := conicalHull_image (s := range piStdBasis') (f := φ.symm.toLinearMap)
            simp only [LinearEquiv.coe_coe] at this
            exact this
          rw [h_image', h_φ_symm_image]
        rw [h_eq]
        exact IsClosed.preimage h_cont_φ h_closed'

example (f : ι → V) [Fintype ι] : finrank ℝ (Submodule.span ℝ (range f)) ≤ Fintype.card ι := finrank_range_le_card f

example (f : ι → V) [Fintype ι] : LinearIndependent ℝ f ↔ Fintype.card ι = finrank ℝ (Submodule.span ℝ (range f)) := linearIndependent_iff_card_eq_finrank_span

example (f : ι → V) [Fintype ι] : Submodule.span ℝ (range f) = ⊤ ↔ finrank ℝ (Submodule.span ℝ (range f)) = finrank ℝ V :=
  Iff.intro
    (fun h => h ▸ finrank_top ℝ V)
    (fun h => Submodule.eq_top_of_finrank_eq h)

end

--========================================================--
--========================= todo =========================--
--========================================================--

--theorem farkas : _ := by sorry --uses lemma 1.2.2 and hyperplane_separation
--OR, use hyperplane separation theorem already in mathlib (we only need the statement of Farkas

--see NormedSpace.polar
--theorem 1.5.1
--proposition 1.5.2(b)

--theorem 1.6.1
