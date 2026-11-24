import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- Removing a cubic cover endpoint pays for three edges and one cover vertex.
-- A resistant circuit must therefore preclude a large independent set.
-- At a singly read input the same gate detects every pivotal assignment.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4117_1
    (detect : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit) (v w : Fin n),
      let reads (i : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
      G.Adj v w → v ∉ A → w ∉ A → FanInTwo C → circuitFun n C = graphFun G A →
      (C.gates.filter (reads v.val)).length ≤ 1 →
      ∃ j : Fin C.size, reads v.val C.gates[j] = true ∧
        ∀ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) →
        graphFun G A x ≠ graphFun G A y → gateVal n C j x ≠ gateVal n C j y)
    (count : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let reads (i : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
      let readers (v : Fin n) := C.gates.filter (reads v.val)
      (∀ v, G.degree v = if v ∈ A then 0 else 3) → 7 ≤ G.egirth →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ v ∉ A, (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, ∃ j : Fin C.size,
        let g := gateAt C j
        readers v = [g] ∧
        (∀ u : Fin n, u ≠ v → g.inputs.Perm [v.val,u.val] → g.op = .not) ∧
        (g.op ≠ .or → ((Finset.Ioo j.val C.size).filter
          (fun k => reads (n+j.val) (gateAt C k))).card ≤ 2) ∧
        ∀ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) →
        f x ≠ f y → gateVal n C j x ≠ gateVal n C j y) →
      (∀ v ∉ A, ∀ s, HasCircuitSize n (fun x => f (Function.update x v false)) s → C.size < s+4) →
      ∃ S : Finset (Fin n), (∀ i ∈ S, ∀ j ∈ S, ¬ G.Adj i j) ∧
        A.card + G.edgeFinset.card + n ≤ C.size + 1 + S.card) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20 := by
  classical
  -- The circuit builder follows the project's Shannon, OrChain and EdgeUpper proofs.
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    simp [wiresFrom, List.foldl_append]

  have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp

  have length_wiresFrom (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
    rw [ht]; simp [hl]

  have getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
    rw [ht, List.getD_append _ _ _ _ h]

  let Ok (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  have getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
      (List.ofFn x).getD (i : ℕ) false = x i := by simp

  let Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
    ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
      out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

  have bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
      Bld n F s' := by
    intro m hm
    obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
    exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

  have bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
      (e : ∀ x, F x = H x) : Bld n H s := by
    intro m hm
    obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
    exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

  have bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
    intro m hm
    refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
    intro w _
    simp [wiresFrom]

  have bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
      {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
      Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
    intro m hm
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
    obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
    refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · exact ok1 g hg
      · exact ok2 g hg
      · subst hg; rcases hop with h | h <;> simp [Ok, h]
    · simp; omega
    · simp; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set v := wiresFrom gs1 w with hv
      have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
      set u := wiresFrom gs2 v with hu
      have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
      have step : wiresFrom [⟨op, [o1, o2]⟩] u
          = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
      rw [step, ← lu, getD_snoc_eq]
      simp only [List.map_cons, List.map_nil, hc]
      have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
        rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
      have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
        rw [hu, ev2 v lv]
        congr 1
        funext i
        rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
      rw [e1, e2]

  have bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
      (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
    bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; cases a <;> cases b <;> rfl) h1 h2

  have bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
      (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
    bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; cases a <;> cases b <;> rfl) h1 h2

  have bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
      HasCircuitSize n F s := by
    obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
    refine ⟨⟨gs, out⟩, ok, len, ?_⟩
    intro x
    have e := ev (List.ofFn x) (by simp)
    change (wiresFrom gs (List.ofFn x)).getD out false = F x
    rw [e]
    congr 1
    funext i
    exact getD_ofFn x i

  clear_value Bld
  have bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
      Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
    induction vs with
    | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
    | cons w ws ih =>
      intro v
      have := bld_or (bld_var v) (ih w)
      refine bld_congr (bld_mono this (by simp)) ?_
      intro x
      simp

  have bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
      Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
    obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
      cases h : S.toList with
      | nil => simp at h; exact absurd h hS.ne_empty
      | cons v vs => exact ⟨v, vs, rfl⟩
    have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
    refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
    simp

  have bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
      (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
      Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
    induction T using Finset.induction_on with
    | empty =>
      intro E hE hc
      obtain ⟨e, he⟩ := hE
      obtain ⟨t, ht, _⟩ := hc e he
      simp at ht
    | @insert t T0 htT ih =>
      intro E hE hc
      set E1 := E.filter (fun e => t ∈ e) with hE1
      set E2 := E.filter (fun e => t ∉ e) with hE2
      have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
      have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
      have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
        intro e he
        rw [hE2, Finset.mem_filter] at he
        obtain ⟨t', ht', hte⟩ := hc e he.1
        rcases Finset.mem_insert.1 ht' with h | h
        · subst h; exact absurd hte he.2
        · exact ⟨t', h, hte⟩
      -- the star at `t`
      set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
          exact hv
        · intro a _ b _ hab
          exact Sym2.congr_right.1 hab
      have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
          E1.card := by
        intro h1
        have hSne : S.Nonempty := by
          obtain ⟨e, he⟩ := h1
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
          exact ⟨b, by simp [hS, ← hb, he]⟩
        have := bld_and (bld_var t) (bld_anyFinset S hSne)
        have hpos := hSne.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨ht, v, hv, hxv⟩
          refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
          intro u hu
          rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
        · rintro ⟨e, he, hall⟩
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
          subst hb
          exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
            hall b (Sym2.mem_mk_right _ _)⟩
      have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
          = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
        intro x
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
        constructor
        · rintro ⟨e, he, h⟩
          by_cases hte : t ∈ e
          · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
          · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
        · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
      rw [hcard]
      by_cases h1 : E1.Nonempty
      · by_cases h2 : E2.Nonempty
        · have := bld_or (star h1) (ih E2 h2 c2)
          have hp := h2.card_pos
          refine bld_congr (bld_mono this (by omega)) ?_
          intro x
          rw [key]
        · rw [Finset.not_nonempty_iff_eq_empty] at h2
          refine bld_congr (bld_mono (star h1) (by omega)) ?_
          intro x
          rw [key, h2]
          simp
      · rw [Finset.not_nonempty_iff_eq_empty] at h1
        have h2 : E2.Nonempty := by
          by_contra h2
          rw [Finset.not_nonempty_iff_eq_empty] at h2
          have := hE.card_pos
          rw [h1, h2] at hsplit
          simp at hsplit
          omega
        refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
        intro x
        rw [key, h1]
        simp

  -- Rebuild the restricted function on the surviving edges and cover.
  have rebuild (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A T : Finset (Fin n)) (v : Fin n) (unmarked : v ∉ A)
      (cover : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T)
      (survives : ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v) :
      let E := G.edgeFinset.filter fun e => v ∉ e
      HasCircuitSize n (fun x => graphFun G A (Function.update x v false))
        (A.card + E.card + (T.erase v).card - 1) := by
    classical
    let E := G.edgeFinset.filter fun e => v ∉ e
    let edges := fun (x : Fin n → Bool) => decide (∃ e ∈ E, ∀ u ∈ e, x u = true)
    let marks := fun (x : Fin n → Bool) => decide (∃ a ∈ A, x a = true)
    have nonempty : E.Nonempty := by
      obtain ⟨i,j,hij,hi,hj⟩ := survives
      exact ⟨s(i,j), Finset.mem_filter.mpr ⟨by simpa using hij, by simpa [Sym2.mem_iff] using And.intro hi.symm hj.symm⟩⟩
    have covers : ∀ e ∈ E, ∃ t ∈ T.erase v, t ∈ e := by
      intro e
      refine Sym2.ind (fun i j => ?_) e
      intro he
      obtain ⟨hedge, avoids⟩ := Finset.mem_filter.mp he
      have hij : G.Adj i j := by simpa using hedge
      rcases cover i j hij with hi | hj
      · exact ⟨i, Finset.mem_erase.mpr ⟨fun h => avoids (h ▸ Sym2.mem_mk_left i j),hi⟩,Sym2.mem_mk_left i j⟩
      · exact ⟨j, Finset.mem_erase.mpr ⟨fun h => avoids (h ▸ Sym2.mem_mk_right i j),hj⟩,Sym2.mem_mk_right i j⟩
    have described (x : Fin n → Bool) :
        (marks x || edges x) = graphFun G A (Function.update x v false) := by
      unfold marks edges graphFun
      congr 1
      · rw [decide_eq_decide]
        constructor <;> rintro ⟨a,ha,h⟩ <;> refine ⟨a,ha,?_⟩
        · simpa [Function.update_of_ne (show a ≠ v from fun e => unmarked (e ▸ ha))] using h
        · simpa [Function.update_of_ne (show a ≠ v from fun e => unmarked (e ▸ ha))] using h
      · rw [decide_eq_decide]
        constructor
        · rintro ⟨e,he,h⟩
          revert he h
          refine Sym2.ind (fun i j => ?_) e
          intro he h
          obtain ⟨hedge,avoids⟩ := Finset.mem_filter.mp he
          have hi : i ≠ v := fun eq => avoids (eq ▸ Sym2.mem_mk_left i j)
          have hj : j ≠ v := fun eq => avoids (eq ▸ Sym2.mem_mk_right i j)
          exact ⟨i,j,by simpa using hedge, by simpa [Function.update_of_ne hi] using h i (Sym2.mem_mk_left i j),
            by simpa [Function.update_of_ne hj] using h j (Sym2.mem_mk_right i j)⟩
        · rintro ⟨i,j,hij,hi,hj⟩
          have iv : i ≠ v := by rintro rfl; simp at hi
          have jv : j ≠ v := by rintro rfl; simp at hj
          refine ⟨s(i,j),Finset.mem_filter.mpr ⟨by simpa using hij, by simpa [Sym2.mem_iff] using And.intro iv.symm jv.symm⟩,?_⟩
          intro t ht
          rcases Sym2.mem_iff.mp ht with rfl | rfl
          · simpa [Function.update_of_ne iv] using hi
          · simpa [Function.update_of_ne jv] using hj
    have buildEdges : Bld n edges (E.card + (T.erase v).card - 1) :=
      bld_edges n (T.erase v) E nonempty covers
    apply bld_hasCircuitSize
    have ep := nonempty.card_pos
    by_cases hA : A.Nonempty
    · have ap := hA.card_pos
      exact bld_congr (bld_mono (bld_or (bld_anyFinset A hA) buildEdges) (by change _ ≤ A.card + E.card + (T.erase v).card - 1; omega)) described
    · have empty := Finset.not_nonempty_iff_eq_empty.mp hA
      apply bld_congr (bld_mono buildEdges (by change _ ≤ A.card + E.card + (T.erase v).card - 1; omega))
      intro x
      calc
        edges x = (marks x || edges x) := by simp [marks,empty]
        _ = _ := described x
  intro n G inst A C
  dsimp only
  intro degree girth unmarked edge minimal computes bounds single noNear
  obtain ⟨a,am,few,noRaw⟩ := single
  have deg (v : Fin n) (h : v ∉ A) : G.degree v = 3 :=
    (G.ncard_neighborSet v).symm.trans (degree v h)
  have apos : 0 < (G.neighborFinset a).card := by
    change 0 < G.degree a
    rw [deg a am]; decide
  obtain ⟨w,hw⟩ := Finset.card_pos.mp apos
  have aw := (G.mem_neighborFinset a w).mp hw
  obtain ⟨j,reads,pivotal⟩ := detect n G A C a w aw am (unmarked w a aw.symm) minimal.1 computes few
  let active (i : ℕ) (g : Gate) :=
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
  have actual : gateAt C j = C.gates[j] := by
    change C.gates.getD j.val _ = _
    exact List.getD_eq_getElem _ _ j.isLt
  have hit : active a.val (gateAt C j) = true := actual ▸ reads
  have member : gateAt C j ∈ C.gates := actual ▸ List.getElem_mem j.isLt
  have exactly : C.gates.filter (active a.val) = [gateAt C j] := by
    have mem := List.mem_filter.mpr ⟨member,hit⟩
    change (C.gates.filter (active a.val)).length ≤ 1 at few
    generalize h : C.gates.filter (active a.val) = l at few mem ⊢
    cases l with
    | nil => cases mem
    | cons head tail =>
      have small : tail.length = 0 := by simpa using few
      have empty : tail = [] := List.length_eq_zero_iff.mp small
      subst tail
      simpa using (List.mem_singleton.mp mem).symm
  have degrees (v : Fin n) : G.degree v = if v ∈ A then 0 else 3 := by
    by_cases hv : v ∈ A
    · rw [if_pos hv,G.degree_eq_zero]
      intro u edge'
      exact unmarked v u edge' hv
    · simpa [hv] using deg v hv
  have raw (u : Fin n) (ua : u ≠ a) (p : (gateAt C j).inputs.Perm [a.val,u.val]) :
      (gateAt C j).op = .not := by
    obtain ⟨na,no⟩ := noRaw _ (List.mem_filter.mpr ⟨member,hit⟩) u ua p
    have basis := (minimal.1 _ member).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at basis
    exact (basis.resolve_left na).resolve_left no
  have fewLater (op : (gateAt C j).op ≠ .or) :
      ((Finset.Ioo j.val C.size).filter (fun k => active (n+j.val) (gateAt C k))).card ≤ 2 := by
    by_contra! many
    apply noNear
    refine ⟨a,am,j.val,j.isLt,hit,op,?_⟩
    apply le_trans many
    apply Finset.card_le_card
    intro k hk
    obtain ⟨interval,r⟩ := Finset.mem_filter.mp hk
    obtain ⟨jk,ks⟩ := Finset.mem_Ioo.mp interval
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ks, jk.ne.symm, Or.inr ⟨jk,r⟩⟩
  by_contra impossible
  have resistant (v : Fin n) (vm : v ∉ A) (s : ℕ)
      (small : HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s) :
      C.size < s+4 := by
    apply Nat.lt_of_not_ge
    exact fun fit => impossible ⟨v,vm,s,fit,small⟩
  obtain ⟨S,independent,bound⟩ := count n G A C degrees girth minimal computes bounds
    ⟨a,am,j,exactly,raw,fewLater,pivotal⟩ resistant
  let T := Sᶜ
  have cover (i k : Fin n) (adj : G.Adj i k) : i ∈ T ∨ k ∈ T := by
    by_cases hi : i ∈ S
    · exact Or.inr (Finset.mem_compl.mpr (fun hk => independent i hi k hk adj))
    · exact Or.inl (Finset.mem_compl.mpr hi)
  have price : A.card + G.edgeFinset.card + T.card ≤ C.size + 1 := by
    have sum : T.card + S.card = n := by simp [T]
    omega
  apply impossible
  obtain ⟨i,j,hij⟩ := edge
  have endpoint : ∃ v w, v ∈ T ∧ G.Adj v w := by
    rcases cover i j hij with hi | hj
    · exact ⟨i,j,hi,hij⟩
    · exact ⟨j,i,hj,hij.symm⟩
  obtain ⟨v,w,vt,vw⟩ := endpoint
  have vm := unmarked v w vw
  have wm := unmarked w v vw.symm
  have vd : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (degree v vm)
  have wd : (G.neighborFinset w).card = 3 := (G.ncard_neighborSet w).symm.trans (degree w wm)
  have vw' : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr vw.symm
  have pos : 0 < ((G.neighborFinset w).erase v).card := by
    rw [Finset.card_erase_of_mem vw', wd]
    decide
  obtain ⟨u,hu⟩ := Finset.card_pos.mp pos
  obtain ⟨uv,wu⟩ := Finset.mem_erase.mp hu
  have hu' := (G.mem_neighborFinset w u).mp wu
  have survives : ∃ a b, G.Adj a b ∧ a ≠ v ∧ b ≠ v := ⟨w,u,hu',vw.ne.symm,uv⟩
  let E := G.edgeFinset.filter fun e => v ∉ e
  have part : (G.incidenceFinset v).card + E.card = G.edgeFinset.card := by
    rw [G.incidenceFinset_eq_filter]
    exact Finset.card_filter_add_card_filter_not _
  rw [G.card_incidenceFinset_eq_degree,vd] at part
  have ep : 0 < E.card := Finset.card_pos.mpr ⟨s(w,u), Finset.mem_filter.mpr
    ⟨by simpa using hu', by simpa [Sym2.mem_iff] using And.intro vw.ne uv.symm⟩⟩
  have tp := Finset.card_erase_of_mem vt
  have tpos := Finset.card_pos.mpr (show T.Nonempty from ⟨v,vt⟩)
  refine ⟨v,vm,A.card + E.card + (T.erase v).card - 1,by omega,?_⟩
  exact rebuild n G A T v vm cover survives
