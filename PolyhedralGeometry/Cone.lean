import PolyhedralGeometry.Defs
import Mathlib.Analysis.Convex.Cone.Basic

variable {V W : Type*} [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W] (s : Set V) (f : V →ₗ[ℝ] W)

def Cone : Prop :=
  s.Nonempty ∧ ∀ c ≥ (0 : ℝ), ∀ x ∈ s, c • x ∈ s

theorem zero_mem_of_cone {s : Set V} (h_cone_s : Cone s) : 0 ∈ s :=
  have ⟨⟨x, h_xs⟩, h_smul_closed⟩ := h_cone_s
  zero_smul ℝ x ▸ h_smul_closed 0 (le_refl 0) x h_xs

def IsConvexCone : Prop :=
  Convex ℝ s ∧ Cone s

#check ConvexCone

def PolyhedralCone.{u} : Prop :=
  IsPolyhedron.{_, u} s ∧ Cone s

def isConicalCombo' (x : V) {ι : Type*} (t : Finset ι) (a : ι → ℝ) (v : ι → V) : Prop :=
  (∀ i ∈ t, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ t, a i • v i

def isConicalCombo (x : V) : Prop :=
  ∃ (ι : Type*) (t : Finset ι) (a : ι → ℝ) (v : ι → V), isConicalCombo' s x t a v

def isConicalCombo_aux' (x : V) (n : ℕ) (a : ℕ → ℝ) (v : ℕ → V) : Prop :=
  (∀ i < n, a i = 0 ∨ 0 ≤ a i ∧ v i ∈ s) ∧ x = ∑ i ∈ Finset.range n, a i • v i

theorem subset_setOf_isConicalCombo : s ⊆ { x | isConicalCombo s x } := by
  intro y hy
  unfold isConicalCombo isConicalCombo'
  use ULift ℕ, {1}, (fun _ => (1 : ℝ)), (fun _ => y)
  simp
  exact hy

def isConicalCombo_aux (x : V) (n : ℕ) : Prop :=
  ∃ (a : ℕ → ℝ) (v : ℕ → V), isConicalCombo_aux' s x n a v

def conicalHull.{u} : Set V :=
  { x | isConicalCombo.{_, u} s x }

theorem isConvexCone_sInter {S : Set (Set V)} (h : ∀ s ∈ S, IsConvexCone s) :
    IsConvexCone (⋂₀ S) where
      left := convex_sInter fun s hs ↦ (h s hs).1
      right.left := ⟨0, fun s hs ↦ zero_mem_of_cone (h s hs).2⟩
      right.right := fun c hc x hxS s hs ↦ (h s hs).2.2 c hc x (hxS s hs)

lemma cone_conicalHull (s : Set V) : Cone (conicalHull s) := by
  constructor
  · use 0, ULift Empty, ∅, fun x => Empty.elim (ULift.down x), fun x => Empty.elim (ULift.down x)
    simp [isConicalCombo']
  · rintro c h_c _ ⟨ι, t, a, v, h_av, rfl⟩
    use ι, t, c • a, v
    constructor
    · intro i h_it
      rcases h_av i h_it with h | ⟨h₁, h₂⟩
      · left
        simp
        right
        exact h
      · right
        refine ⟨mul_nonneg h_c h₁, h₂⟩
    · rw [Finset.smul_sum]
      congr
      ext i
      rw [← smul_assoc]
      simp

lemma conicalHull_eq_zero_of_empty {s : Set V} (h_s : s = ∅) : conicalHull s = {0} := by
  rw [h_s]
  refine subset_antisymm ?_ (by simp; exact zero_mem_of_cone (cone_conicalHull _))
  intro x h_x
  simp
  rcases h_x with ⟨ι, t, a, v, h_av, rfl⟩
  apply Finset.sum_eq_zero
  intro i h_it
  rcases h_av i h_it with h | ⟨_, h⟩
  · simp [h]
  contradiction

lemma subset_conicalHull_of_set (s: Set V): s ⊆ conicalHull s := by
  intro y hy
  unfold conicalHull isConicalCombo isConicalCombo'
  use ULift ℕ , {1}, (λ x => 1), (λ x => y)
  simp; exact hy

lemma sum_bijon {α β γ : Type*} [AddCommMonoid γ] {t : Finset α} {s : Finset β} {T : α → β} (h_bij : Set.BijOn T t s) {f : α → γ} {g : β → γ} (h_fg : f = g ∘ T) : ∑ i ∈ t, f i = ∑ j ∈ s, g j := by
  rcases h_bij with ⟨h_mapsto, h_inj, h_surj⟩
  apply Finset.sum_bij
  · apply h_mapsto
  · apply h_inj
  · convert h_surj
    simp [Set.SurjOn]
    rfl
  · tauto

lemma reindex_conicalCombo' {s : Set V} {x : V} {ι : Type*} (t : Finset ι) (a : ι → ℝ) (v : ι → V) : isConicalCombo' s x t a v → isConicalCombo_aux s x t.card := by
  rintro ⟨h_av, h_x_combo⟩
  have := (Finset.equivFin t).symm
  set N := t.card
  by_cases hN : N = 0
  · rw [hN]
    use (λ n ↦ 0), (λ n ↦ 0), by simp
    rw [Finset.sum_range_zero, h_x_combo]
    have : t = ∅ := Finset.card_eq_zero.mp hN
    rw [this]
    simp
  replace hN : N > 0 := Nat.zero_lt_of_ne_zero hN
  set F : ℕ → ι := Subtype.val ∘ (Finset.equivFin t).symm ∘ λ n ↦ if hn : n < N then (⟨n, hn⟩ : Fin N) else (⟨0, hN⟩ : Fin N)
  have h_F : Set.BijOn F (Finset.range N) t := by
    repeat' constructor
    · simp [Set.MapsTo, F]
    · simp [Set.InjOn, F]
      intro n₁ hn₁ n₂ hn₂ h_eq
      have h_fin : (⟨n₁, hn₁⟩ : Fin N) = ⟨n₂, hn₂⟩ := by
        apply t.equivFin.symm.injective
        exact Subtype.ext (by simpa [F, hn₁, hn₂] using h_eq)
      exact Fin.val_congr h_fin
    · intro i h_it
      simp
      have : Function.Surjective t.equivFin.symm := t.equivFin.symm.surjective
      rcases this ⟨i, h_it⟩ with ⟨⟨n, hn⟩, h_eq⟩
      use n, hn
      simp [F]
      rw [dif_pos hn, h_eq]
  set a' : ℕ → ℝ := a ∘ F
  set v' : ℕ → V := v ∘ F
  use a', v'
  repeat' constructor
  · intro i _
    dsimp [a', v']
    apply h_av
    apply h_F.1
    simpa
  · dsimp [a', v']
    rw [h_x_combo]
    symm
    apply sum_bijon
    · simp; convert h_F; simp
    · ext; simp

lemma reindex_conicalCombo (s : Set V) (x : V) : isConicalCombo s x ↔ ∃ n, isConicalCombo_aux s x n := by
  constructor
  · rintro ⟨ι, t, a, v, h⟩
    use t.card
    exact reindex_conicalCombo' _ _ _ h
  · rintro ⟨n, a, v, h_av, h_x_combo⟩
    let ℕ' := ULift ℕ
    let I := Finset.map (Function.Embedding.mk (@ULift.up Nat) (@ULift.up.inj Nat)) (Finset.range n)
    let a' : ℕ' → ℝ := fun i ↦ a i.down
    let v' : ℕ' → V := fun i ↦ v i.down
    use ℕ', I, a', v'
    simp [isConicalCombo', ℕ', I, a', v', Finset.mem_range]
    use h_av

lemma reduce_conicalCombo (s : Set V) (x : V) {n : ℕ} {a : ℕ → ℝ} (v : ℕ → V) : (∃ j < n + 1, a j = 0) → isConicalCombo_aux' s x (n + 1) a v → isConicalCombo_aux s x n := by
  rintro ⟨j, h_j⟩ ⟨h_av, h_x_combo⟩
  convert reindex_conicalCombo' ((Finset.range (n + 1)).erase j) a v ?_
  · have := Finset.card_erase_add_one (Finset.mem_range.mpr h_j.1)
    simp at this
    rw [this]
  · unfold isConicalCombo'
    constructor
    · intro i h_i
      rw [Finset.mem_erase, Finset.mem_range] at h_i
      exact h_av i h_i.2
    · have : a j • v j = 0 := by rw [h_j.2]; simp
      rw[Finset.sum_erase (Finset.range (n + 1)) this]

lemma isconicalCombo_aux_le (s : Set V) (x : V) : m ≤ n → isConicalCombo_aux s x m → isConicalCombo_aux s x n := by
  intro h_mn
  rintro ⟨a, v, h_av, h_x_combo⟩
  let a' : ℕ → ℝ := fun i => if h_im : i < m then a i else 0
  use a', v
  repeat' constructor
  · intro i h_in
    by_cases h_im : i < m
    · simp [a', if_pos h_im]
      exact h_av i h_im
    · simp [a', if_neg h_im]
  · have h₁ : Finset.range m ⊆ Finset.range n := by simp; linarith
    have h₂ : ∀ i ∈ Finset.range n, i ∉ Finset.range m → a' i • v i = 0 := by
      simp [a']
      intros
      linarith
    rw [← Finset.sum_subset h₁ h₂]
    simp [a']
    rw [Finset.sum_ite_of_true, h_x_combo]
    intro i hi
    rw [Finset.mem_range] at hi
    exact hi

theorem zero_mem_conicalHull (s : Set V) : 0 ∈ conicalHull s := by
  use ULift Empty, ∅, fun x => Empty.elim (ULift.down x), fun x => Empty.elim (ULift.down x)
  simp [isConicalCombo']

open Finset

theorem conicalHull_image (s : Set V) : f '' (conicalHull.{_,u} s) = conicalHull.{_,u} (f '' s) := by
  apply subset_antisymm <;> rintro y h_y
  · rcases h_y with ⟨x, ⟨ι, t, a, v, h_av, h_combo⟩, rfl⟩
    use ι, t, a, f ∘ v
    constructor
    · intro i h_it
      rcases h_av i h_it with h | ⟨h₁, h₂⟩
      · exact Or.inl h
      · exact Or.inr ⟨h₁, v i, h₂, rfl⟩
    · rw [h_combo]
      simp
  · rcases h_y with ⟨ι, t, a, w, h_av, rfl⟩
    let t' := filter (fun i ↦ a i ≠ 0) t
    classical
    have h_key : ∀ i ∈ t', 0 ≤ a i ∧ w i ∈ f '' s := fun i h_it' ↦
      h_av i (mem_of_mem_filter i h_it') |>.resolve_left <| by simp [t'] at h_it'; exact h_it'.2
    let v : ι → V := fun i ↦ if h : i ∈ t' then (h_key i h).2.choose else 0
    have : ∀ i ∈ t', f (v i) = w i := fun i h ↦ by
      simp [v, h]
      exact Exists.choose_spec (h_key i h).2 |>.2
    have : ∀ i ∈ t, a i • f (v i) = a i • w i := by
      intro i h_it
      by_cases h_it' : i ∈ t'
      · simp [this i h_it']
      simp [t'] at h_it'
      simp [h_it' h_it]
    use ∑ i ∈ t, a i • v i
    constructor; swap
    · simp
      exact sum_congr rfl this
    use ι, t', a, v
    constructor
    · intro i h_it'
      right
      constructor
      · exact (h_key i h_it').1
      simp [v, h_it']
      exact Exists.choose_spec (h_key i h_it').2 |>.1
    symm
    apply sum_subset (Finset.filter_subset _ _)
    intro i h_it h_it'
    simp at h_it'
    simp [h_it' h_it]

theorem conicalHull_preimage_subset_preimage_conicalHull (s : Set W) : conicalHull.{_,u} (f ⁻¹' s) ⊆ f ⁻¹' (conicalHull.{_,u} s) := by
  rintro x ⟨ι, t, a, v, h₁, h₂⟩
  use ι, t, a, f ∘ v
  constructor
  · exact h₁
  rw [h₂]
  simp only [map_sum, map_smul, Function.comp_apply]

/-! ## Additional Conical Hull Properties -/

lemma conicalHull_contains (g : V) (hg : g ∈ s) : g ∈ conicalHull s :=
  subset_conicalHull_of_set s hg

lemma conicalHull_add.{u} (x y : V) (hx : x ∈ conicalHull.{_, u} s) (hy : y ∈ conicalHull.{_, u} s) :
    x + y ∈ conicalHull.{_, u} s := by
  rcases hx with ⟨ι1, t1, a1, v1, h1, rfl⟩
  rcases hy with ⟨ι2, t2, a2, v2, h2, rfl⟩
  use ULift.{u} (ι1 ⊕ ι2), (t1.disjSum t2).map ⟨ULift.up, ULift.up_injective⟩
  use fun i => Sum.elim a1 a2 i.down
  use fun i => Sum.elim v1 v2 i.down
  constructor
  · intro i hi
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_disjSum] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    cases j with
    | inl j1 =>
      rcases hj with ⟨k, hk, heq⟩ | ⟨k, _, heq⟩
      · simp only [Sum.inl.injEq] at heq; subst heq; exact h1 k hk
      · simp at heq
    | inr j2 =>
      rcases hj with ⟨k, _, heq⟩ | ⟨k, hk, heq⟩
      · simp at heq
      · simp only [Sum.inr.injEq] at heq; subst heq; exact h2 k hk
  · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_disjSum,
      Sum.elim_inl, Sum.elim_inr]

lemma conicalHull_smul.{u} (c : ℝ) (x : V) (hc : 0 ≤ c) (hx : x ∈ conicalHull.{_, u} s) :
    c • x ∈ conicalHull.{_, u} s := by
  rcases hx with ⟨ι, t, a, v, h_av, rfl⟩
  use ι, t, fun i => c * a i, v
  constructor
  · intro i hi
    rcases h_av i hi with h | ⟨h₁, h₂⟩
    · left; simp [h]
    · right; exact ⟨mul_nonneg hc h₁, h₂⟩
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]

theorem isConvexCone_setOf_isConicalCombo : IsConvexCone { x | isConicalCombo s x } := by
  change IsConvexCone (conicalHull s)
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have hx' : a • x ∈ conicalHull s := conicalHull_smul (s := s) a x ha hx
    have hy' : b • y ∈ conicalHull s := conicalHull_smul (s := s) b y hb hy
    simpa using (conicalHull_add (s := s) (x := a • x) (y := b • y) hx' hy')
  · refine ⟨⟨0, zero_mem_conicalHull s⟩, ?_⟩
    intro c hc x hx
    exact conicalHull_smul (s := s) c x hc hx

theorem conicalHull_mono.{u} (T : Set V) (h : s ⊆ T) :
    conicalHull.{_, u} s ⊆ conicalHull.{_, u} T := by
  intro x hx
  obtain ⟨ι, t, c, v, h_combo, rfl⟩ := hx
  use ι, t, c, v
  constructor
  · intro i hi
    rcases h_combo i hi with h_zero | ⟨h_nonneg, h_mem⟩
    · left; exact h_zero
    · right; exact ⟨h_nonneg, h h_mem⟩
  · rfl

lemma conicalHull_idempotent.{u} : conicalHull.{_, u} (conicalHull.{_, u} s) ⊆ conicalHull.{_, u} s := by
  classical
  rintro x ⟨ι, t, a, v, h_av, rfl⟩
  have h_term : ∀ i ∈ t, a i • v i ∈ conicalHull s := by
    intro i hi
    rcases h_av i hi with h_zero | ⟨h_nonneg, h_mem⟩
    · have h0 : (0 : V) ∈ conicalHull s := zero_mem_conicalHull s
      simpa [h_zero] using h0
    · exact conicalHull_smul (s := s) (c := a i) (x := v i) h_nonneg h_mem
  have h_sum :
      ∀ t : Finset ι, (∀ i ∈ t, a i • v i ∈ conicalHull s) →
        (∑ i ∈ t, a i • v i) ∈ conicalHull s := by
    classical
    intro t
    refine Finset.induction_on t ?base ?step
    · intro _
      simp [zero_mem_conicalHull]
    · intro i t hi ih ht
      have h_i : a i • v i ∈ conicalHull s := ht i (by simp [hi])
      have h_t : ∀ j ∈ t, a j • v j ∈ conicalHull s := by
        intro j hj
        exact ht j (by simp [hj])
      have h_rest : (∑ j ∈ t, a j • v j) ∈ conicalHull s := ih h_t
      have h_add :
          a i • v i + ∑ j ∈ t, a j • v j ∈ conicalHull s :=
        conicalHull_add (s := s) (x := a i • v i) (y := ∑ j ∈ t, a j • v j) h_i h_rest
      simpa [Finset.sum_insert, hi] using h_add
  exact h_sum t h_term

--not sure what the simps! attribute does
@[simps! isClosed]
def conicalHull' : ClosureOperator (Set V) :=
  ClosureOperator.mk₂ (fun s => conicalHull.{_, 0} s)
    (fun s => subset_conicalHull_of_set s)
    (by
      intro s t hst
      exact (conicalHull_mono (s := s) (T := conicalHull t) hst).trans
        (conicalHull_idempotent (s := t)))

theorem mem_conicalHull'_iff {x : V} : x ∈ conicalHull' s ↔ isConicalCombo.{_, 0} s x := by
  rfl

-- might be useful:
theorem polyhedralCone_as_convexCone (s : Set V) :
  PolyhedralCone s → ∃ s' : ConvexCone ℝ V, s'.carrier = s := by
  intro h_poly
  rcases h_poly with ⟨h_isPoly, h_cone⟩
  have h_convex : Convex ℝ s := by
    rcases h_isPoly with ⟨ι, H, _hfin, h_half, h_eq⟩
    have h_convex_H : ∀ i, Convex ℝ (H i) := by
      intro i
      rcases h_half i with ⟨f, c, h_eq⟩
      have h_convex_half : Convex ℝ {x : V | f x ≤ c} := by
        intro x hx y hy a b ha hb hab
        have hx' : f x ≤ c := hx
        have hy' : f y ≤ c := hy
        have hlin : f (a • x + b • y) = a * f x + b * f y := by
          simp [LinearMap.map_add, smul_eq_mul]
        have h1 : a * f x + b * f y ≤ a * c + b * c := by
          nlinarith [hx', hy', ha, hb]
        calc
          f (a • x + b • y) = a * f x + b * f y := hlin
          _ ≤ a * c + b * c := h1
          _ = c := by
            calc
              a * c + b * c = (a + b) * c := by ring
              _ = 1 * c := by simp [hab]
              _ = c := by ring
      rw [h_eq]
      exact h_convex_half
    rw [h_eq]
    exact convex_iInter h_convex_H
  refine ⟨{ carrier := s, smul_mem' := ?_, add_mem' := ?_ }, rfl⟩
  · intro c hc x hx
    exact h_cone.2 c (le_of_lt hc) x hx
  · intro x hx y hy
    have h_mid : ( (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ) ∈ s := by
      have := h_convex hx hy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num)
      simpa using this
    have h_scaled :
        (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ s :=
      h_cone.2 2 (by norm_num) _ h_mid
    have h_sum :
        (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = x + y := by
      calc
        (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
            = (2 : ℝ) • ((1 / 2 : ℝ) • x) + (2 : ℝ) • ((1 / 2 : ℝ) • y) := by
              simp [smul_add]
        _ = ((2 : ℝ) * (1 / 2 : ℝ)) • x + ((2 : ℝ) * (1 / 2 : ℝ)) • y := by
              simp [smul_smul]
        _ = x + y := by
              simp
    simpa [h_sum] using h_scaled
