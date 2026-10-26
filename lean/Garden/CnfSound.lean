import Garden.CnfGen
import Garden.Tower

/-!
# Every `Adm` circuit satisfies its run's generated CNF

`CnfGen.events n r tt o` is `optimal_circuit.encode`'s clause list over variable *meanings*
(`CnfGen.M`). Here a circuit `gs` (output node `o`, negated by `neg`) gives each meaning a truth
value, `ev`: `sel i j k` is "gate `i` reads `(j, k)`", `val i t` is node `i`'s value on row `t`,
`red T g` is "gate `g` is redundant on the rows `T`", and so on. Then:

* `number_sat`: if every event is satisfied under `ev` (`Good`), the numbered CNF `cnfOf evs` is
  satisfied by `fun k => ev (decls[k])`. Generic in `ev`: the numbering only renames.
* `events_good`: if `gs` satisfies `Tower.Adm n f R` and the encoder options `o` ask for nothing
  `R` does not grant (`Fits`), every event of `events n gs.length tt o` is `Good`.
* **`adm_sat`**: so `toCNF (cnfOf (events n gs.length tt o ++ cube))` is satisfiable, for any
  cube of literals the circuit satisfies. Hence if that CNF is `Unsat`, no `Adm` circuit of
  `gs.length` gates lies in the cube.

Axioms: the standard three.
-/

namespace CnfSound
open CnfGen CircuitDual GateElim SymBreak SymCanon Reduction Mod3SemBounds Mod3Lower Tower

/-! ### Python's iteration orders, as sets -/

lemma mem_combs_sublist {α : Type} : ∀ (k : ℕ) (L : List α) (c : List α), c ∈ combs k L →
    c.Sublist L ∧ c.length = k
  | 0, L, c, h => by simp [combs] at h; subst h; exact ⟨List.nil_sublist _, rfl⟩
  | k + 1, [], c, h => by simp [combs] at h
  | k + 1, x :: xs, c, h => by
    simp only [combs, List.mem_append, List.mem_map] at h
    rcases h with ⟨d, hd, rfl⟩ | h
    · obtain ⟨h1, h2⟩ := mem_combs_sublist k xs d hd
      exact ⟨h1.cons_cons x, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := mem_combs_sublist (k + 1) xs c h
      exact ⟨h1.cons x, h2⟩

lemma mem_combs2 {α : Type} (L : List α) (c : List α) (h : c ∈ combs 2 L) :
    ∃ a b, c = [a, b] ∧ [a, b].Sublist L := by
  obtain ⟨h1, h2⟩ := mem_combs_sublist 2 L c h
  match c, h2 with
  | [a, b], _ => exact ⟨a, b, rfl, h1⟩

lemma sublist_pair_lt (L : List ℕ) (hL : L.Pairwise (· < ·)) (a b : ℕ) (h : [a, b].Sublist L) :
    a < b := by
  have := hL.sublist h
  simpa using this

lemma mem_pairs (i : ℕ) (p : ℕ × ℕ) : p ∈ pairs i ↔ p.1 < p.2 ∧ p.2 < i := by
  obtain ⟨j, k⟩ := p
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨j', hj', k', ⟨hk', hjk⟩, rfl, rfl⟩; exact ⟨hjk, hk'⟩
  · rintro ⟨hjk, hk⟩; exact ⟨j, by omega, k, ⟨hk, hjk⟩, rfl, rfl⟩

lemma pairs_nodup (i : ℕ) : (pairs i).Nodup := by
  unfold pairs
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => ((List.nodup_range).filter _).map (fun a b h => by simpa using h), ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne (fun a _ b _ hab => ?_)
  intro p hp hq
  simp only [List.mem_map, List.mem_filter] at hp hq
  obtain ⟨_, _, rfl⟩ := hp
  obtain ⟨_, _, h⟩ := hq
  exact hab (congrArg Prod.fst h).symm

lemma mem_gates (n r i : ℕ) : i ∈ gates n r ↔ n ≤ i ∧ i < n + r := by
  simp only [gates, List.mem_range'_1]

lemma gates_nodup (n r : ℕ) : (gates n r).Nodup := List.nodup_range'

lemma gates_sorted (n r : ℕ) : (gates n r).Pairwise (· < ·) := by
  unfold gates
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_range']; omega

lemma mem_selItems (n r : ℕ) (x : ℕ × ℕ × ℕ) :
    x ∈ selItems n r ↔ (n ≤ x.1 ∧ x.1 < n + r) ∧ x.2.1 < x.2.2 ∧ x.2.2 < x.1 := by
  obtain ⟨i, j, k⟩ := x
  simp only [selItems, List.mem_flatMap, List.mem_map, mem_gates, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', p, hp, rfl, rfl, rfl⟩
    exact ⟨hi', (mem_pairs _ _).mp hp⟩
  · rintro ⟨hi, h⟩
    exact ⟨i, hi, (j, k), (mem_pairs _ _).mpr h, rfl, rfl, rfl⟩

lemma mem_rows (n t : ℕ) : t ∈ rows n ↔ t < 2 ^ n := by simp [rows]

/-! ### Counting: `atMost` -/

lemma atMost_of_count {α : Type} (L : List α) (p : α → Bool) (k : ℕ)
    (hc : (L.filter p).length < k) (c : List α) (h : c ∈ combs k L) : ∃ x ∈ c, p x = false := by
  obtain ⟨hs, hlen⟩ := mem_combs_sublist k L c h
  by_contra hne
  push Not at hne
  have hall : ∀ x ∈ c, p x = true := fun x hx => by
    have := hne x hx; cases hpx : p x <;> simp_all
  have : c.Sublist (L.filter p) := by
    have h1 := hs.filter p
    rwa [List.filter_eq_self.mpr hall] at h1
  have := this.length_le
  omega

open Classical in
lemma countP_range (P : ℕ → Prop) :
    ∀ r, (List.range r).countP (fun j => decide (P j)) = ((Finset.range r).filter P).card
  | 0 => by simp
  | r + 1 => by
    rw [List.range_succ, List.countP_append, countP_range P r, Finset.range_add_one,
      Finset.filter_insert]
    by_cases hP : P r
    · rw [if_pos hP, Finset.card_insert_of_notMem (by simp)]; simp [hP]
    · rw [if_neg hP]; simp [hP]

open Classical in
lemma count_gates (n r : ℕ) (P : ℕ → Prop) :
    ((gates n r).filter (fun h => decide (P (h - n)))).length = ((Finset.range r).filter P).card := by
  unfold gates
  rw [List.range'_eq_map_range, List.filter_map, List.length_map]
  have : ((List.range r).filter ((fun h => decide (P (h - n))) ∘ (n + ·))) =
      (List.range r).filter (fun j => decide (P j)) := by
    congr 1; funext j; simp
  rw [this, ← List.countP_eq_length_filter, countP_range]

/-! ### The numbering only renames -/

/-- An event holds under the meaning assignment `ev`. -/
def Good (ev : M → Bool) : Ev → Prop
  | .decl _ => True
  | .cl c => ∃ l ∈ c, ev l.1 = l.2
  | .lazy _ defs => ∀ d ∈ defs, ∃ l ∈ d, ev l.1 = l.2

/-- A DIMACS literal is true when its variable's meaning has the literal's sign. -/
def LitTrue (ev : M → Bool) (D : Array M) (l : Int) : Prop :=
  l.natAbs ≠ 0 ∧ l.natAbs ≤ D.size ∧ ev (D[l.natAbs - 1]?.getD .neg) = decide (0 < l)

structure Inv (ev : M → Bool) (s : NS) : Prop where
  map_ok : ∀ m k, s.map[m]? = some k → k ≠ 0 ∧ k ≤ s.decls.size ∧ s.decls[k - 1]? = some m
  out_ok : ∀ c ∈ s.out, ∃ l ∈ c, LitTrue ev s.decls l

/-- `D'` extends `D`. -/
def Ext (D D' : Array M) : Prop := D.size ≤ D'.size ∧ ∀ i < D.size, D'[i]? = D[i]?

lemma ext_refl (D : Array M) : Ext D D := ⟨le_refl _, fun _ _ => rfl⟩

lemma ext_trans {D D' D'' : Array M} (h1 : Ext D D') (h2 : Ext D' D'') : Ext D D'' :=
  ⟨le_trans h1.1 h2.1, fun i hi => by rw [h2.2 i (by have := h1.1; omega), h1.2 i hi]⟩

lemma ext_push (D : Array M) (m : M) : Ext D (D.push m) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [Array.getElem?_push, if_neg (by omega)]

lemma litTrue_ext {ev : M → Bool} {D D' : Array M} (h : Ext D D') {l : Int} (hl : LitTrue ev D l) :
    LitTrue ev D' l := by
  obtain ⟨h1, h2, h3⟩ := hl
  exact ⟨h1, le_trans h2 h.1, by rw [h.2 _ (by omega)]; exact h3⟩

lemma mkLit_natAbs (k : ℕ) (b : Bool) : (mkLit k b).natAbs = k := by
  cases b <;> simp [mkLit]

lemma mkLit_pos (k : ℕ) (hk : k ≠ 0) (b : Bool) : decide (0 < mkLit k b) = b := by
  cases b <;> simp [mkLit] <;> omega

lemma inv_declare (ev : M → Bool) (s : NS) (m : M) (h : Inv ev s) : Inv ev (s.declare m) := by
  constructor
  · intro m' k hk
    simp only [NS.declare, Std.HashMap.getElem?_insert] at hk ⊢
    split_ifs at hk with hm
    · cases hk
      have : m = m' := by simpa using hm
      subst this
      refine ⟨by omega, by simp, ?_⟩
      simp [Array.getElem?_push]
    · obtain ⟨h1, h2, h3⟩ := h.map_ok m' k hk
      refine ⟨h1, by simp; omega, ?_⟩
      rw [(ext_push s.decls m).2 _ (by omega), h3]
  · intro c hc
    obtain ⟨l, hl, hl'⟩ := h.out_ok c hc
    exact ⟨l, hl, litTrue_ext (ext_push _ _) hl'⟩

/-- Numbering a literal: the result is true when the literal is, and the state stays well
formed. -/
lemma lit_spec (ev : M → Bool) (s : NS) (l : L) (h : Inv ev s) :
    Inv ev (s.lit l).1 ∧ Ext s.decls (s.lit l).1.decls ∧ (s.lit l).1.out = s.out ∧
      (ev l.1 = l.2 → LitTrue ev (s.lit l).1.decls (s.lit l).2) := by
  obtain ⟨m, b⟩ := l
  unfold NS.lit
  split
  · rename_i k hk
    obtain ⟨h1, h2, h3⟩ := h.map_ok m k hk
    refine ⟨h, ext_refl _, rfl, fun he => ?_⟩
    simp only at he ⊢
    refine ⟨by rw [mkLit_natAbs]; exact h1, by rw [mkLit_natAbs]; exact h2, ?_⟩
    rw [mkLit_natAbs, h3, mkLit_pos k h1]; exact he
  · refine ⟨inv_declare ev s m h, ext_push _ _, rfl, fun he => ?_⟩
    simp only at he ⊢
    refine ⟨by rw [mkLit_natAbs]; omega, by rw [mkLit_natAbs]; simp [NS.declare], ?_⟩
    rw [mkLit_natAbs, mkLit_pos _ (by omega)]
    simp [NS.declare, Array.getElem?_push, he]

lemma lits_spec (ev : M → Bool) : ∀ (c : List L) (s : NS), Inv ev s →
    Inv ev (s.lits c).1 ∧ Ext s.decls (s.lits c).1.decls ∧ (s.lits c).1.out = s.out ∧
      ((∃ l ∈ c, ev l.1 = l.2) → ∃ i ∈ (s.lits c).2, LitTrue ev (s.lits c).1.decls i)
  | [], s, h => ⟨h, ext_refl _, rfl, fun ⟨_, hl, _⟩ => by simp at hl⟩
  | l :: ls, s, h => by
    obtain ⟨h1, e1, o1, t1⟩ := lit_spec ev s l h
    obtain ⟨h2, e2, o2, t2⟩ := lits_spec ev ls _ h1
    have hl : s.lits (l :: ls) =
        (((s.lit l).1.lits ls).1, (s.lit l).2 :: ((s.lit l).1.lits ls).2) := rfl
    rw [hl]
    refine ⟨h2, ext_trans e1 e2, by rw [o2, o1], ?_⟩
    rintro ⟨l', hl', he⟩
    simp only [List.mem_cons] at hl' ⊢
    rcases hl' with rfl | hl'
    · exact ⟨_, Or.inl rfl, litTrue_ext e2 (t1 he)⟩
    · obtain ⟨i, hi, hi'⟩ := t2 ⟨l', hl', he⟩
      exact ⟨i, Or.inr hi, hi'⟩

lemma inv_clause (ev : M → Bool) (s : NS) (c : List L) (h : Inv ev s)
    (hc : ∃ l ∈ c, ev l.1 = l.2) : Inv ev (s.clause c) := by
  obtain ⟨h1, -, -, t1⟩ := lits_spec ev c s h
  have hc' : s.clause c = { (s.lits c).1 with out := (s.lits c).1.out.push (s.lits c).2 } := rfl
  rw [hc']
  constructor
  · exact h1.map_ok
  · intro c' hc'
    simp only [Array.mem_push] at hc'
    rcases hc' with hc' | rfl
    · exact h1.out_ok c' hc'
    · exact t1 hc

lemma inv_step (ev : M → Bool) (s : NS) (e : Ev) (h : Inv ev s) (he : Good ev e) :
    Inv ev (s.step e) := by
  cases e with
  | decl m => exact inv_declare ev s m h
  | cl c => exact inv_clause ev s c h he
  | lazy m defs =>
    simp only [NS.step]
    split_ifs
    · exact h
    · have : ∀ (ds : List (List L)) (s : NS), Inv ev s → (∀ d ∈ ds, ∃ l ∈ d, ev l.1 = l.2) →
          Inv ev (ds.foldl NS.clause s) := by
        intro ds
        induction ds with
        | nil => intro s h _; exact h
        | cons d ds ih =>
          intro s h hd
          exact ih _ (inv_clause ev s d h (hd d (by simp))) (fun d' hd' => hd d' (by simp [hd']))
      exact this defs _ (inv_declare ev s m h) he

lemma inv_number (ev : M → Bool) (evs : List Ev) (h : ∀ e ∈ evs, Good ev e) :
    Inv ev (number evs) := by
  have : ∀ (evs : List Ev) (s : NS), Inv ev s → (∀ e ∈ evs, Good ev e) →
      Inv ev (evs.foldl NS.step s) := by
    intro evs
    induction evs with
    | nil => intro s h _; exact h
    | cons e es ih =>
      intro s h he
      exact ih _ (inv_step ev s e h (he e (by simp))) (fun e' he' => he e' (by simp [he']))
  apply this evs {} _ h
  constructor
  · intro m k hk; simp at hk
  · intro c hc; simp at hc

/-- The assignment a list of events induces: variable `k + 1` gets its meaning's value. -/
def assign (ev : M → Bool) (evs : List Ev) (k : ℕ) : Bool := ev ((number evs).decls[k]?.getD .neg)

/-- **The numbered CNF is satisfied by the meanings' values.** -/
theorem number_sat (ev : M → Bool) (evs : List Ev) (h : ∀ e ∈ evs, Good ev e) :
    (toCNF (cnfOf evs)).eval (assign ev evs) = true := by
  have hI := inv_number ev evs h
  simp only [toCNF, cnfOf, Std.Sat.CNF.eval, List.all_toArray, List.all_map, List.all_eq_true,
    Array.mem_toList_iff]
  intro c hc
  obtain ⟨l, hl, h1, h2, h3⟩ := hI.out_ok c hc
  simp only [Function.comp, Std.Sat.CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨l, hl, by simp [litOf, assign, h3]⟩

/-! ### Rows -/

/-- Row `t` as an input list: input `i` is bit `i` of `t` (`tt_of`'s convention). -/
def row (n t : ℕ) : List Bool := (List.range n).map t.testBit

lemma row_length (n t : ℕ) : (row n t).length = n := by simp [row]

lemma row_getD (n t v : ℕ) (hv : v < n) : (row n t).getD v false = t.testBit v := by
  simp [row, List.getD_eq_getElem?_getD, hv]

/-- The index of a row. -/
def idx : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * idx bs

lemma idx_lt : ∀ x : List Bool, idx x < 2 ^ x.length
  | [] => by simp [idx]
  | b :: bs => by
    have := idx_lt bs
    simp only [idx, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

lemma testBit_idx : ∀ (x : List Bool) (i : ℕ) (hi : i < x.length), (idx x).testBit i = x[i]
  | [], i, hi => by simp at hi
  | b :: bs, 0, _ => by
    simp only [idx, List.getElem_cons_zero, Nat.testBit_zero]
    cases b <;> simp <;> omega
  | b :: bs, i + 1, hi => by
    simp only [idx, List.getElem_cons_succ, Nat.testBit_add_one]
    rw [← testBit_idx bs i (by simpa using hi)]
    congr 1; cases b <;> simp <;> omega

lemma row_idx (x : List Bool) : row x.length (idx x) = x := by
  apply List.ext_getElem (by simp [row])
  intro i h1 h2
  simp only [row, List.getElem_map, List.getElem_range]
  exact testBit_idx x i h2

lemma row_surj (n : ℕ) (x : List Bool) (hx : x.length = n) : ∃ t ∈ rows n, x = row n t :=
  ⟨idx x, (mem_rows _ _).mpr (hx ▸ idx_lt x), by rw [← hx, row_idx]⟩

/-- The rows `T` as a set of inputs. -/
def rowSet (n : ℕ) (T : List ℕ) : Set (List Bool) := {x | ∃ t ∈ T, x = row n t}

lemma rowSet_length (n : ℕ) (T : List ℕ) : ∀ x ∈ rowSet n T, x.length = n := by
  rintro x ⟨t, -, rfl⟩; exact row_length n t

lemma rowSet_all (n : ℕ) : rowSet n (rows n) = {x | x.length = n} := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩; exact row_length n t
  · intro hx; exact row_surj n x hx

/-- A `redundancy` row set is the set it describes. -/
lemma rowSet_where (n : ℕ) (p : ℕ → Bool) (P : List Bool → Prop)
    (hp : ∀ t < 2 ^ n, p t = true ↔ P (row n t)) :
    rowSet n ((rows n).filter p) = {x | x.length = n ∧ P x} := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_filter, mem_rows] at ht
    exact ⟨row_length n t, (hp t ht.1).mp ht.2⟩
  · rintro ⟨hx, hP⟩
    obtain ⟨t, ht, rfl⟩ := row_surj n x hx
    rw [mem_rows] at ht
    exact ⟨t, List.mem_filter.mpr ⟨(mem_rows _ _).mpr ht, (hp t ht).mpr hP⟩, rfl⟩

/-! ### What each variable means for a circuit -/

section Meaning
variable (n : ℕ) (gs : List Gate) (o : ℕ) (negb : Bool)

/-- Gate node `i`'s gate. -/
def gt (i : ℕ) : Gate := gs.getD (i - n) dflt

/-- Node `i`'s value on row `t`. -/
def nodeV (t i : ℕ) : Bool := V gs (row n t) i

open Classical in
/-- **The circuit's value for each meaning.** -/
noncomputable def ev : M → Bool
  | .sel i j k => decide ((gt n gs i).a = j ∧ (gt n gs i).b = k)
  | .fbit i p q => (gt n gs i).op p q
  | .val i t => nodeV n gs t i
  | .osel i => decide (o = i)
  | .neg => negb
  | .dd i i2 t => nodeV n gs t i ^^ nodeV n gs t i2
  | .kv v g c => decide (KC v c (gt n gs g))
  | .e1 v c h => decide (ElimHit n v c gs (h - n))
  | .e2 u v a b h => decide (Elim2Hit n u v a b gs (h - n))
  | .red T g => decide (Redundant n gs (rowSet n T) (g - n))
  | .diff h g t => nodeV n gs t h != nodeV n gs t g
  | .same h g t => nodeV n gs t h == nodeV n gs t g

end Meaning

lemma gt_eq (n : ℕ) (gs : List Gate) (i : ℕ) (h : i - n < gs.length) : gt n gs i = gs[i - n] := by
  simp [gt, List.getD_eq_getElem?_getD, h]

lemma nodeV_input (n : ℕ) (gs : List Gate) (t j : ℕ) (hj : j < n) : nodeV n gs t j = t.testBit j := by
  unfold nodeV V
  rw [run_getD_input _ _ _ (by rw [row_length]; exact hj), row_getD n t j hj]

/-- A gate's value from its two reads. -/
lemma nodeV_gate (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (i : ℕ) (hi1 : n ≤ i)
    (hi2 : i < n + gs.length) (t : ℕ) :
    (gt n gs i).a < (gt n gs i).b ∧ (gt n gs i).b < i ∧
      nodeV n gs t i = (gt n gs i).op (nodeV n gs t (gt n gs i).a) (nodeV n gs t (gt n gs i).b) := by
  have hj : i - n < gs.length := by omega
  have hsh := (shaped_iff n gs).mp hs (i - n) hj
  rw [gt_eq n gs i hj]
  refine ⟨hsh.1, by omega, ?_⟩
  unfold nodeV
  have := V_gate n (row n t) (row_length n t) gs (i - n) hj (by omega) (by omega)
  rwa [show n + (i - n) = i by omega] at this

/-- `ev` of a sel literal: true exactly for gate `i`'s own pair. -/
lemma ev_sel (n : ℕ) (gs : List Gate) (o : ℕ) (negb : Bool) (i j k : ℕ) :
    ev n gs o negb (.sel i j k) = true ↔ (gt n gs i).a = j ∧ (gt n gs i).b = k := by
  simp [ev]

/-! ### Generic clause shapes -/

lemma good_cl {ev : M → Bool} {c : List L} (l : L) (hl : l ∈ c) (h : ev l.1 = l.2) :
    Good ev (.cl c) := ⟨l, hl, h⟩

lemma good_ng {ev : M → Bool} {c : List L} (m : M) (hl : ng m ∈ c) (h : ev m = false) :
    Good ev (.cl c) := ⟨ng m, hl, h⟩

lemma good_pos {ev : M → Bool} {c : List L} (m : M) (hl : pos m ∈ c) (h : ev m = true) :
    Good ev (.cl c) := ⟨pos m, hl, h⟩

lemma exactlyOne_good (ev : M → Bool) (ms : List M) (hnd : ms.Nodup)
    (h1 : ∃ m ∈ ms, ev m = true) (h2 : ∀ a ∈ ms, ∀ b ∈ ms, ev a = true → ev b = true → a = b) :
    ∀ e ∈ exactlyOne ms, Good ev e := by
  intro e he
  simp only [exactlyOne, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨c, hc, rfl⟩
  · obtain ⟨m, hm, hv⟩ := h1
    exact good_cl (pos m) (List.mem_map_of_mem hm) hv
  · obtain ⟨a, b, rfl, hab⟩ := mem_combs2 ms c hc
    have hne : a ≠ b := by have := hnd.sublist hab; simpa using this
    by_cases ha : ev a = true
    · have hb : ev b = false := by
        by_contra hb; exact hne (h2 a (hab.subset (by simp)) b (hab.subset (by simp)) ha (by simpa using hb))
      exact good_ng b (by simp) hb
    · exact good_ng a (by simp) (by simpa using ha)

/-- At most `k − 1` of the `e h` are true, given a count. -/
lemma atMost_good (ev : M → Bool) (n r k : ℕ) (e : ℕ → M)
    (hc : ((gates n r).filter fun h => ev (e h)).length < k) : ∀ x ∈ atMost n r k e, Good ev x := by
  intro x hx
  simp only [atMost, List.mem_map] at hx
  obtain ⟨cc, hcc, rfl⟩ := hx
  obtain ⟨h, hh, hp⟩ := atMost_of_count (gates n r) (fun h => ev (e h)) k hc cc hcc
  exact good_ng (e h) (List.mem_map_of_mem hh) hp

/-! ### The encoding -/

section Core
variable (n : ℕ) (gs : List Gate) (o : ℕ) (negb : Bool)

lemma coreDecls_good : ∀ e ∈ coreDecls n gs.length, Good (ev n gs o negb) e := by
  intro e he
  have : ∃ m, e = .decl m := by
    simp only [coreDecls, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
      List.mem_singleton] at he
    aesop
  obtain ⟨m, rfl⟩ := this
  trivial

lemma ev_sel_false (i j k : ℕ) (h : ¬ ((gt n gs i).a = j ∧ (gt n gs i).b = k)) :
    ev n gs o negb (.sel i j k) = false := by
  simp only [ev, decide_eq_false_iff_not]; exact h

lemma litVal_ne (t j : ℕ) (p : Bool) (hne : nodeV n gs t j ≠ p) :
    litVal n j t p = .fls ∨ ∃ l ∈ (litVal n j t p).negs, ev n gs o negb l.1 = l.2 := by
  unfold litVal
  split_ifs with hj h
  · rw [nodeV_input n gs t j hj] at hne
    simp at h; exact absurd h hne
  · exact Or.inl rfl
  · right
    refine ⟨(.val j t, !p), by simp [LV.negs], ?_⟩
    simp only [ev]; cases p <;> simp_all

lemma litVal_eq (t j : ℕ) (p : Bool) (heq : nodeV n gs t j = p) : litVal n j t p ≠ .fls := by
  unfold litVal
  split_ifs with hj h
  · simp
  · rw [nodeV_input n gs t j hj] at heq; simp [heq] at h
  · simp

lemma valBlock_good (hs : Shaped n gs) (hn : Normal gs) (i j k t : ℕ) (hi1 : n ≤ i)
    (hi2 : i < n + gs.length) (p q : Bool) :
    ∀ e ∈ valBlock n i j k t p q, Good (ev n gs o negb) e := by
  intro e he
  simp only [valBlock] at he
  by_cases hA : litVal n j t p = .fls ∨ litVal n k t q = .fls
  · rw [if_pos hA] at he; simp at he
  rw [if_neg hA] at he
  -- every clause starts with the premise `¬sel ∨ ¬(x_j = p) ∨ ¬(x_k = q)`
  have prem : ∀ c : List L,
      (ng (.sel i j k) :: ((litVal n j t p).negs ++ (litVal n k t q).negs)).Sublist c →
      (¬ ((gt n gs i).a = j ∧ (gt n gs i).b = k) ∨ nodeV n gs t j ≠ p ∨ nodeV n gs t k ≠ q) →
      Good (ev n gs o negb) (.cl c) := by
    intro c hsub hcase
    rcases hcase with h | h | h
    · exact good_ng (.sel i j k) (hsub.subset (by simp)) (ev_sel_false n gs o negb i j k h)
    · rcases litVal_ne n gs o negb t j p h with h' | ⟨l, hl, hv⟩
      · exact absurd (Or.inl h') hA
      · exact good_cl l (hsub.subset (by simp [hl])) hv
    · rcases litVal_ne n gs o negb t k q h with h' | ⟨l, hl, hv⟩
      · exact absurd (Or.inr h') hA
      · exact good_cl l (hsub.subset (by simp [hl])) hv
  have hg : gt n gs i ∈ gs := by rw [gt_eq n gs i (by omega)]; exact List.getElem_mem _
  obtain ⟨-, -, hv⟩ := nodeV_gate n gs hs i hi1 hi2 t
  by_cases h2 : p = false ∧ q = false
  · rw [if_pos h2] at he
    simp only [List.mem_singleton] at he
    subst he
    by_cases hc : ((gt n gs i).a = j ∧ (gt n gs i).b = k) ∧ nodeV n gs t j = p ∧ nodeV n gs t k = q
    · obtain ⟨⟨ha, hb⟩, hP, hQ⟩ := hc
      refine good_ng (.val i t) (by simp) ?_
      simp only [ev]
      rw [hv, ha, hb, hP, hQ, h2.1, h2.2]; exact hn _ hg
    · exact prem _ (by simp) (by tauto)
  · rw [if_neg h2] at he
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    by_cases hc : ((gt n gs i).a = j ∧ (gt n gs i).b = k) ∧ nodeV n gs t j = p ∧ nodeV n gs t k = q
    · obtain ⟨⟨ha, hb⟩, hP, hQ⟩ := hc
      have hv' : nodeV n gs t i = (gt n gs i).op p q := by rw [hv, ha, hb, hP, hQ]
      rcases he with rfl | rfl
      · cases hx : nodeV n gs t i
        · exact good_ng (.val i t) (by simp) (by simp [ev, hx])
        · exact good_pos (.fbit i p q) (by simp) (by simp [ev, ← hv', hx])
      · cases hx : nodeV n gs t i
        · exact good_ng (.fbit i p q) (by simp) (by simp [ev, ← hv', hx])
        · exact good_pos (.val i t) (by simp) (by simp [ev, hx])
    · rcases he with rfl | rfl
      · exact prem _ (by simp) (by tauto)
      · exact prem _ (by simp) (by tauto)

lemma coreCls_good (hs : Shaped n gs) (hn : Normal gs) :
    ∀ e ∈ coreCls n gs.length, Good (ev n gs o negb) e := by
  intro e he
  simp only [coreCls, List.mem_flatMap, List.mem_append] at he
  obtain ⟨i, hi, he⟩ := he
  rw [mem_gates] at hi
  rcases he with he | ⟨p, hp, t, -, he⟩
  · obtain ⟨hab, hbi, -⟩ := nodeV_gate n gs hs i hi.1 hi.2 0
    refine exactlyOne_good _ _ ?_ ?_ ?_ e he
    · exact (pairs_nodup i).map (fun a b h => by simpa [Prod.ext_iff] using h)
    · exact ⟨.sel i (gt n gs i).a (gt n gs i).b,
        List.mem_map.mpr ⟨_, (mem_pairs i ((gt n gs i).a, (gt n gs i).b)).mpr ⟨hab, hbi⟩, rfl⟩,
        by simp [ev]⟩
    · intro a ha b hb hva hvb
      simp only [List.mem_map] at ha hb
      obtain ⟨pa, -, rfl⟩ := ha
      obtain ⟨pb, -, rfl⟩ := hb
      simp only [ev, decide_eq_true_eq] at hva hvb
      rw [← hva.1, ← hva.2, ← hvb.1, ← hvb.2]
  · simp only [valCls, List.mem_append] at he
    rcases he with ((he | he) | he) | he <;>
      exact valBlock_good n gs o negb hs hn i p.1 p.2 t hi.1 hi.2 _ _ e he

end Core

/-! ### `sym`, `order`, `allin`, `distinct` -/

section Fam
variable (n : ℕ) (f : List Bool → Bool) (R : Opts) (gs : List Gate) (o : ℕ) (negb : Bool)

lemma gt_mem (i : ℕ) (hi1 : n ≤ i) (hi2 : i < n + gs.length) : gt n gs i ∈ gs := by
  rw [gt_eq n gs i (by omega)]; exact List.getElem_mem _

/-- A gate node's pair is a `sel.items()` key. -/
lemma sel_mem (hs : Shaped n gs) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < n + gs.length) :
    (i, (gt n gs i).a, (gt n gs i).b) ∈ selItems n gs.length := by
  obtain ⟨h1, h2, -⟩ := nodeV_gate n gs hs i hi1 hi2 0
  exact (mem_selItems _ _ _).mpr ⟨⟨hi1, hi2⟩, h1, h2⟩

lemma ev_sel_self (i : ℕ) : ev n gs o negb (.sel i (gt n gs i).a (gt n gs i).b) = true := by
  simp [ev]

/-- Gate `n + j` is `gs[j]`. -/
lemma gt_add (j : ℕ) (hj : j < gs.length) : gt n gs (n + j) = gs[j] := by
  rw [gt_eq n gs _ (by omega)]; simp

lemma symCls_good (h : Adm n f R gs o negb) : ∀ e ∈ symCls n gs.length, Good (ev n gs o negb) e := by
  intro e he
  simp only [symCls, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at he
  obtain ⟨i, hi, he⟩ := he
  rw [mem_gates] at hi
  obtain ⟨n1, n2, n3⟩ := h.nondegenerate _ (gt_mem n gs i hi.1 hi.2)
  have three : ∀ (b1 b2 b3 : Bool) (c : List L),
      (.fbit i false true, b1) ∈ c → (.fbit i true false, b2) ∈ c → (.fbit i true true, b3) ∈ c →
      ¬ ((gt n gs i).op false true = !b1 ∧ (gt n gs i).op true false = !b2 ∧
        (gt n gs i).op true true = !b3) → Good (ev n gs o negb) (.cl c) := by
    intro b1 b2 b3 c h1 h2 h3 hn
    by_cases a : (gt n gs i).op false true = b1
    · exact good_cl _ h1 a
    by_cases b : (gt n gs i).op true false = b2
    · exact good_cl _ h2 b
    by_cases d : (gt n gs i).op true true = b3
    · exact good_cl _ h3 d
    refine absurd ⟨?_, ?_, ?_⟩ hn
    · revert a; cases (gt n gs i).op false true <;> cases b1 <;> simp
    · revert b; cases (gt n gs i).op true false <;> cases b2 <;> simp
    · revert d; cases (gt n gs i).op true true <;> cases b3 <;> simp
  rcases he with rfl | rfl | rfl | rfl
  · exact three true true true _ (by simp [pos]) (by simp [pos]) (by simp [pos]) (by simpa using n1)
  · exact three true false false _ (by simp [pos]) (by simp [ng]) (by simp [ng]) (by simpa using n2)
  · exact three false true false _ (by simp [ng]) (by simp [pos]) (by simp [ng]) (by simpa using n3)
  · rcases h.used (i - n) (by omega) with ho | ⟨k, hk, hjk, hr⟩
    · exact good_pos (.osel i) (by simp) (by simp [ev]; omega)
    · have hm := sel_mem n gs h.shaped (n + k) (by omega) (by omega)
      rw [gt_add n gs k hk] at hm
      refine good_pos (.sel (n + k) gs[k].a gs[k].b) (List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨_, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩)) ?_
      · simp only [decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rcases hr with hr | hr <;> [left; right] <;> omega
      · have := ev_sel_self n gs o negb (n + k); rwa [gt_add n gs k hk] at this

lemma orderCls_good (h : Adm n f R gs o negb) :
    ∀ e ∈ orderCls n gs.length, Good (ev n gs o negb) e := by
  intro e he
  simp only [orderCls, List.mem_flatMap, List.mem_filterMap, List.mem_filter, mem_gates] at he
  obtain ⟨i, hi, a, ha, b, ⟨hb, hbi⟩, he⟩ := he
  split_ifs at he with hlt
  cases he
  by_cases h1 : (gt n gs i).a = a.1 ∧ (gt n gs i).b = a.2
  · by_cases h2 : (gt n gs (i + 1)).a = b.1 ∧ (gt n gs (i + 1)).b = b.2
    · exfalso
      have hj : i - n + 1 < gs.length := by omega
      have hO := h.order (i - n) hj
      rw [← gt_add n gs (i - n + 1) hj, ← gt_add n gs (i - n) (by omega),
        show n + (i - n + 1) = i + 1 by omega, show n + (i - n) = i by omega] at hO
      have hbi := of_decide_eq_true hbi
      apply hO
      · rintro (hr | hr) <;> [exact hbi.1 (h2.1 ▸ hr); exact hbi.2 (h2.2 ▸ hr)]
      · unfold PairLt; rw [h1.1, h1.2, h2.1, h2.2]; unfold pairLt at hlt; simp at hlt; omega
    · exact good_ng (.sel (i + 1) b.1 b.2) (by simp) (ev_sel_false n gs o negb _ _ _ h2)
  · exact good_ng (.sel i a.1 a.2) (by simp) (ev_sel_false n gs o negb _ _ _ h1)

lemma flipAt_row (n t v : ℕ) (hv : v < n) : flipAt v (row n t) = row n (t ^^^ (1 <<< v)) := by
  show (row n t).set v (!(row n t).getD v false) = _
  apply List.ext_getElem (by simp [row])
  intro i h1 h2
  rw [List.getElem_set]
  simp only [row, List.getElem_map, List.getElem_range]
  rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases hiv : v = i
  · subst hiv; rw [if_pos rfl]; simp [List.getD_eq_getElem?_getD, hv]
  · rw [if_neg hiv]; simp [hiv]

/-- `essential_inputs` finds only essential inputs. -/
lemma essential_sound (tt : ℕ → Bool) (htt : ∀ t < 2 ^ n, tt t = f (row n t)) (v : ℕ)
    (hv : v ∈ essential n tt) : v < n ∧ Essential n f v := by
  unfold essential at hv
  rw [List.mem_filter, List.mem_range, List.any_eq_true] at hv
  obtain ⟨hvn, t, ht, hne⟩ := hv
  rw [mem_rows] at ht
  refine ⟨hvn, row n t, row_length n t, ?_⟩
  have ht' : t ^^^ (1 <<< v) < 2 ^ n :=
    Nat.xor_lt_two_pow ht (by rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by omega) hvn)
  rw [flipAt_row n t v hvn, ← htt _ ht', ← htt _ ht]
  intro heq; rw [heq] at hne; simp at hne

lemma allinCls_good (h : Adm n f R gs o negb) (hA : R.allin = true) (tt : ℕ → Bool)
    (htt : ∀ t < 2 ^ n, tt t = f (row n t)) :
    ∀ e ∈ allinCls n gs.length tt, Good (ev n gs o negb) e := by
  intro e he
  simp only [allinCls, List.mem_map] at he
  obtain ⟨v, hv, rfl⟩ := he
  obtain ⟨hvn, hess⟩ := essential_sound n f tt htt v hv
  obtain ⟨g, hg, hr⟩ := h.allin hA v hvn hess
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  have hm := sel_mem n gs h.shaped (n + k) (by omega) (by omega)
  rw [gt_add n gs k hk] at hm
  refine good_pos (.sel (n + k) gs[k].a gs[k].b) (List.mem_map.mpr
    ⟨_, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩) ?_
  · simp only [decide_eq_true_eq]; exact hr
  · have := ev_sel_self n gs o negb (n + k); rwa [gt_add n gs k hk] at this

lemma nodeV_eq_V (x : List Bool) (t : ℕ) (hx : x = row n t) (i : ℕ) : V gs x i = nodeV n gs t i := by
  subst hx; rfl

lemma distinctCls_good (h : Adm n f R gs o negb) :
    ∀ e ∈ distinctCls n gs.length, Good (ev n gs o negb) e := by
  have hT : ∀ x ∈ ({x | x.length = n} : Set (List Bool)), ∃ t ∈ rows n, x = row n t :=
    fun x hx => row_surj n x hx
  intro e he
  simp only [distinctCls, List.mem_append, List.mem_flatMap] at he
  rcases he with ⟨i, hi, g, hg, he⟩ | ⟨c, hc, he⟩
  · rw [mem_gates] at hi
    have hd := h.distinct (i - n) (by omega)
    have hgv : ∀ t, nodeV n gs t (n + (i - n)) = nodeV n gs t i := fun t => by
      rw [show n + (i - n) = i by omega]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · by_contra hcon
      apply hd
      have hall : ∀ t ∈ rows n, nodeV n gs t i = trivVal g t := by
        intro t ht
        by_contra hne
        apply hcon
        cases hx : trivVal g t
        · exact good_pos (.val i t) (List.mem_map.mpr ⟨t, ht, by simp [hx]⟩)
            (by simp only [ev]; simpa [hx] using hne)
        · exact good_ng (.val i t) (List.mem_map.mpr ⟨t, ht, by simp [hx]⟩)
            (by simp only [ev]; simpa [hx] using hne)
      cases g with
      | none =>
        refine Or.inl ⟨false, fun x hx => ?_⟩
        obtain ⟨t, ht, rfl⟩ := hT x hx
        rw [nodeV_eq_V n gs _ t rfl, hgv, hall t ht]; rfl
      | some v =>
        simp only [List.mem_cons, List.mem_map, List.mem_range, reduceCtorEq, false_or,
          Option.some.injEq] at hg
        obtain ⟨v, hv, rfl⟩ := hg
        refine Or.inr (Or.inl ⟨v, hv, false, fun x hx => ?_⟩)
        obtain ⟨t, ht, rfl⟩ := hT x hx
        rw [nodeV_eq_V n gs _ t rfl, hgv, hall t ht, row_getD n t v hv]; simp [trivVal]
    · by_contra hcon
      apply hd
      have hall : ∀ t ∈ rows n, nodeV n gs t i = !trivVal g t := by
        intro t ht
        by_contra hne
        apply hcon
        cases hx : trivVal g t
        · exact good_ng (.val i t) (List.mem_map.mpr ⟨t, ht, by simp [hx]⟩)
            (by simp only [ev]; simpa [hx] using hne)
        · exact good_pos (.val i t) (List.mem_map.mpr ⟨t, ht, by simp [hx]⟩)
            (by simp only [ev]; simpa [hx] using hne)
      cases g with
      | none =>
        refine Or.inl ⟨true, fun x hx => ?_⟩
        obtain ⟨t, ht, rfl⟩ := hT x hx
        rw [nodeV_eq_V n gs _ t rfl, hgv, hall t ht]; rfl
      | some v =>
        simp only [List.mem_cons, List.mem_map, List.mem_range, reduceCtorEq, false_or,
          Option.some.injEq] at hg
        obtain ⟨v, hv, rfl⟩ := hg
        refine Or.inr (Or.inl ⟨v, hv, true, fun x hx => ?_⟩)
        obtain ⟨t, ht, rfl⟩ := hT x hx
        rw [nodeV_eq_V n gs _ t rfl, hgv, hall t ht, row_getD n t v hv]; simp [trivVal]
  · obtain ⟨i, i2, rfl, hsub⟩ := mem_combs2 _ c hc
    have hlt := sublist_pair_lt _ (gates_sorted n gs.length) i i2 hsub
    have hi : i ∈ gates n gs.length := hsub.subset (by simp)
    have hi2 : i2 ∈ gates n gs.length := hsub.subset (by simp)
    rw [mem_gates] at hi hi2
    have hd := h.distinct (i2 - n) (by omega)
    have hgv : ∀ t, nodeV n gs t (n + (i2 - n)) = nodeV n gs t i2 := fun t => by
      rw [show n + (i2 - n) = i2 by omega]
    have hgv' : ∀ t, nodeV n gs t (n + (i - n)) = nodeV n gs t i := fun t => by
      rw [show n + (i - n) = i by omega]
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at he
    rcases he with ((⟨t, -, rfl⟩ | ⟨t, -, he⟩) | he)
    · trivial
    · rcases he with rfl | rfl | rfl | rfl <;>
        cases h1 : nodeV n gs t i <;> cases h2 : nodeV n gs t i2 <;> simp_all [Good, ev, pos, ng]
    · rcases he with rfl | rfl
      · by_contra hcon
        apply hd
        refine Or.inr (Or.inr ⟨i - n, by omega, false, fun x hx => ?_⟩)
        obtain ⟨t, ht, rfl⟩ := hT x hx
        rw [nodeV_eq_V n gs _ t rfl, nodeV_eq_V n gs _ t rfl, hgv, hgv']
        by_contra hne
        apply hcon
        refine good_pos (.dd i i2 t) (List.mem_map.mpr ⟨t, ht, rfl⟩) ?_
        simp only [ev]
        revert hne
        cases nodeV n gs t i <;> cases nodeV n gs t i2 <;> simp
      · by_contra hcon
        apply hd
        refine Or.inr (Or.inr ⟨i - n, by omega, true, fun x hx => ?_⟩)
        obtain ⟨t, ht, rfl⟩ := hT x hx
        rw [nodeV_eq_V n gs _ t rfl, nodeV_eq_V n gs _ t rfl, hgv, hgv']
        by_contra hne
        apply hcon
        refine good_ng (.dd i i2 t) (List.mem_map.mpr ⟨t, ht, rfl⟩) ?_
        simp only [ev]
        revert hne
        cases nodeV n gs t i <;> cases nodeV n gs t i2 <;> simp

end Fam

/-! ### `elim`, `elim2`, `redundancy` -/

section Bounds
variable (n : ℕ) (gs : List Gate) (o : ℕ) (negb : Bool)

lemma ev_fbit (i : ℕ) (p q : Bool) : ev n gs o negb (.fbit i p q) = (gt n gs i).op p q := rfl
lemma ev_kv (v g : ℕ) (c : Bool) : ev n gs o negb (.kv v g c) = true ↔ KC v c (gt n gs g) := by
  simp [ev]

lemma good_sel {c : List L} (i j k : ℕ) (hc : ng (.sel i j k) ∈ c)
    (h : (gt n gs i).a = j ∧ (gt n gs i).b = k → Good (ev n gs o negb) (.cl c)) :
    Good (ev n gs o negb) (.cl c) := by
  by_cases hs : (gt n gs i).a = j ∧ (gt n gs i).b = k
  · exact h hs
  · exact good_ng _ hc (ev_sel_false n gs o negb i j k hs)

/-- Three table bits, one of which has the wanted value. -/
lemma good_bits {c : List L} (i : ℕ) (b1 b2 : Bool) (p1 q1 p2 q2 : Bool)
    (h1 : (.fbit i p1 q1, b1) ∈ c) (h2 : (.fbit i p2 q2, b2) ∈ c)
    (h : (gt n gs i).op p1 q1 = !b1 → (gt n gs i).op p2 q2 = !b2 → Good (ev n gs o negb) (.cl c)) :
    Good (ev n gs o negb) (.cl c) := by
  by_cases a : (gt n gs i).op p1 q1 = b1
  · exact good_cl _ h1 a
  by_cases b : (gt n gs i).op p2 q2 = b2
  · exact good_cl _ h2 b
  exact h (by revert a; cases (gt n gs i).op p1 q1 <;> cases b1 <;> simp)
    (by revert b; cases (gt n gs i).op p2 q2 <;> cases b2 <;> simp)

lemma good_bit {c : List L} (i : ℕ) (b1 : Bool) (p1 q1 : Bool)
    (h1 : (.fbit i p1 q1, b1) ∈ c)
    (h : (gt n gs i).op p1 q1 = !b1 → Good (ev n gs o negb) (.cl c)) :
    Good (ev n gs o negb) (.cl c) := by
  by_cases a : (gt n gs i).op p1 q1 = b1
  · exact good_cl _ h1 a
  exact h (by revert a; cases (gt n gs i).op p1 q1 <;> cases b1 <;> simp)

lemma kCls_good (hn : Normal gs) (v : ℕ) :
    ∀ e ∈ kCls n gs.length v, Good (ev n gs o negb) e := by
  unfold kCls
  rw [List.forall_mem_append]
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · simp only [List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at he
    obtain ⟨g, -, rfl | rfl⟩ := he <;> trivial
  rw [List.mem_flatMap] at he
  obtain ⟨x, hx, he⟩ := he
  obtain ⟨⟨hg1, hg2⟩, -, -⟩ := (mem_selItems _ _ _).mp hx
  have h00 := hn _ (gt_mem n gs x.1 hg1 hg2)
  revert e he
  rw [List.forall_mem_append]
  constructor
  · split_ifs with hj
    · simp only [List.forall_mem_cons]
      refine ⟨good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hs => ?_,
        good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hs => ?_,
        good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hs => ?_, by simp⟩
      · refine good_bit n gs o negb x.1 true false true (by simp [pos]) fun a => ?_
        exact good_pos (.kv v x.1 false) (by simp) ((ev_kv n gs o negb _ _ _).mpr
          (Or.inl ⟨hs.1.trans hj, by rw [h00, a]; rfl⟩))
      · refine good_bits n gs o negb x.1 false false true false true true (by simp [ng])
          (by simp [ng]) fun a b => ?_
        exact good_pos (.kv v x.1 true) (by simp) ((ev_kv n gs o negb _ _ _).mpr
          (Or.inl ⟨hs.1.trans hj, by rw [a, b]⟩))
      · refine good_bits n gs o negb x.1 true true true false true true (by simp [pos])
          (by simp [pos]) fun a b => ?_
        exact good_pos (.kv v x.1 true) (by simp) ((ev_kv n gs o negb _ _ _).mpr
          (Or.inl ⟨hs.1.trans hj, by rw [a, b]⟩))
    · simp
  · split_ifs with hj
    · simp only [List.forall_mem_cons]
      refine ⟨good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hs => ?_,
        good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hs => ?_,
        good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hs => ?_, by simp⟩
      · refine good_bit n gs o negb x.1 true true false (by simp [pos]) fun a => ?_
        exact good_pos (.kv v x.1 false) (by simp) ((ev_kv n gs o negb _ _ _).mpr
          (Or.inr ⟨hs.2.trans hj, by rw [h00, a]; rfl⟩))
      · refine good_bits n gs o negb x.1 false false false true true true (by simp [ng])
          (by simp [ng]) fun a b => ?_
        exact good_pos (.kv v x.1 true) (by simp) ((ev_kv n gs o negb _ _ _).mpr
          (Or.inr ⟨hs.2.trans hj, by rw [a, b]⟩))
      · refine good_bits n gs o negb x.1 true true false true true true (by simp [pos])
          (by simp [pos]) fun a b => ?_
        exact good_pos (.kv v x.1 true) (by simp) ((ev_kv n gs o negb _ _ _).mpr
          (Or.inr ⟨hs.2.trans hj, by rw [a, b]⟩))
    · simp

/-- A key's reads come before it. -/
lemma sel_lt (x : ℕ × ℕ × ℕ) (hx : x ∈ selItems n gs.length) :
    (n ≤ x.1 ∧ x.1 < n + gs.length) ∧ x.2.1 < x.2.2 ∧ x.2.2 < x.1 := (mem_selItems _ _ _).mp hx

lemma reads_of_sel (i j k : ℕ) (hi1 : n ≤ i) (hi2 : i < n + gs.length)
    (hs : (gt n gs i).a = j ∧ (gt n gs i).b = k) (c : ℕ) (hc : j = c ∨ k = c) :
    Reads (gs[i - n]'(by omega)) c := by
  rw [← gt_eq n gs i (by omega)]
  rcases hc with rfl | rfl
  · exact Or.inl hs.1
  · exact Or.inr hs.2

open Classical in
lemma count_eq (P : ℕ → Prop) (mk : ℕ → M) (hmk : ∀ h, ev n gs o negb (mk h) = decide (P (h - n))) :
    ((gates n gs.length).filter fun h => ev n gs o negb (mk h)).length =
      ((Finset.range gs.length).filter P).card := by
  rw [← count_gates n gs.length P]
  congr 1
  exact List.filter_congr (fun h _ => hmk h)

lemma e1Cls_good (hs : Shaped n gs) (v : ℕ) (c : Bool) (B : ℕ) (hB : elimCount n v c gs ≤ B) :
    ∀ e ∈ e1Cls n gs.length v c B, Good (ev n gs o negb) e := by
  unfold e1Cls
  rw [List.forall_mem_append, List.forall_mem_append]
  refine ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · simp only [List.mem_map] at he; obtain ⟨h, -, rfl⟩ := he; trivial
  · rw [List.mem_flatMap] at he
    obtain ⟨x, hx, he⟩ := he
    obtain ⟨⟨hg1, hg2⟩, hjk, hkh⟩ := sel_lt n gs x hx
    revert e he
    rw [List.forall_mem_append]
    constructor
    · split_ifs with hj
      · simp only [List.forall_mem_cons]
        refine ⟨good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hsl => ?_, by simp⟩
        refine good_pos (.e1 v c x.1) (by simp) ?_
        simp only [ev, decide_eq_true_eq]
        exact ⟨by omega, Or.inl (reads_of_sel n gs _ _ _ hg1 hg2 hsl v hj)⟩
      · simp
    · intro e he
      simp only [List.mem_map, List.mem_filter, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, decide_eq_true_eq] at he
      obtain ⟨g, ⟨hg, hng⟩, rfl⟩ := he
      refine good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hsl => ?_
      by_cases hK : KC v c (gt n gs g)
      · refine good_pos (.e1 v c x.1) (by simp) ?_
        simp only [ev, decide_eq_true_eq]
        have hgh : g < x.1 := by rcases hg with rfl | rfl <;> omega
        refine ⟨by omega, Or.inr ⟨g - n, by omega, ?_, ?_⟩⟩
        · rw [show n + (g - n) = g by omega]
          exact reads_of_sel n gs _ _ _ hg1 hg2 hsl g (by rcases hg with rfl | rfl <;> simp)
        · rw [← gt_eq n gs g (by omega)]; exact hK
      · exact good_ng (.kv v g c) (by simp) (by simpa [ev] using hK)
  · apply atMost_good
    rw [count_eq n gs o negb (ElimHit n v c gs) (.e1 v c) (fun h => rfl)]
    unfold elimCount at hB
    convert Nat.lt_succ_of_le hB

lemma e2Cls_good (hs : Shaped n gs) (u v : ℕ) (a b : Bool) (B : ℕ)
    (hB : elim2Count n u v a b gs ≤ B) :
    ∀ e ∈ e2Cls n gs.length u v a b B, Good (ev n gs o negb) e := by
  unfold e2Cls
  rw [List.forall_mem_append, List.forall_mem_append]
  refine ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · simp only [List.mem_map] at he; obtain ⟨h, -, rfl⟩ := he; trivial
  · rw [List.mem_flatMap] at he
    obtain ⟨x, hx, he⟩ := he
    obtain ⟨⟨hg1, hg2⟩, hjk, hkh⟩ := sel_lt n gs x hx
    revert e he
    rw [List.forall_mem_append]
    constructor
    · split_ifs with hj
      · simp only [List.forall_mem_cons]
        refine ⟨good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hsl => ?_, by simp⟩
        refine good_pos (.e2 u v a b x.1) (by simp) ?_
        simp only [ev, decide_eq_true_eq]
        rcases hj with hj | hj
        · exact ⟨by omega, Or.inl (reads_of_sel n gs _ _ _ hg1 hg2 hsl u hj)⟩
        · exact ⟨by omega, Or.inr (Or.inl (reads_of_sel n gs _ _ _ hg1 hg2 hsl v hj))⟩
      · simp
    · intro e he
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, decide_eq_true_eq] at he
      obtain ⟨g, ⟨hg, hng⟩, he⟩ := he
      have hgh : g < x.1 := by rcases hg with rfl | rfl <;> omega
      have hit : (gt n gs x.1).a = x.2.1 ∧ (gt n gs x.1).b = x.2.2 →
          (KC u a (gs[g - n]'(by omega)) ∨ KC v b (gs[g - n]'(by omega)) ∨
          ((gs[g - n]'(by omega)).a = u ∧ (gs[g - n]'(by omega)).b = v)) →
          ev n gs o negb (.e2 u v a b x.1) = true := by
        intro hsl hK
        have hread : Reads (gs[x.1 - n]'(by omega)) (n + (g - n)) := by
          rw [show n + (g - n) = g by omega]
          exact reads_of_sel n gs _ _ _ hg1 hg2 hsl g (by rcases hg with rfl | rfl <;> simp)
        simp only [ev, decide_eq_true_eq]
        exact ⟨by omega, Or.inr (Or.inr ⟨g - n, by omega, hread, hK⟩)⟩
      have hgt := gt_eq n gs g (by omega)
      rcases he with rfl | rfl | rfl
      · refine good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hsl => ?_
        by_cases hK : KC u a (gt n gs g)
        · exact good_pos (.e2 u v a b x.1) (by simp) (hit hsl (Or.inl (hgt ▸ hK)))
        · exact good_ng (.kv u g a) (by simp) (by simpa [ev] using hK)
      · refine good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hsl => ?_
        by_cases hK : KC v b (gt n gs g)
        · exact good_pos (.e2 u v a b x.1) (by simp) (hit hsl (Or.inr (Or.inl (hgt ▸ hK))))
        · exact good_ng (.kv v g b) (by simp) (by simpa [ev] using hK)
      · refine good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hsl => ?_
        by_cases hK : (gt n gs g).a = u ∧ (gt n gs g).b = v
        · exact good_pos (.e2 u v a b x.1) (by simp) (hit hsl (Or.inr (Or.inr (hgt ▸ hK))))
        · exact good_ng (.sel g u v) (by simp) (ev_sel_false n gs o negb _ _ _ hK)
  · apply atMost_good
    rw [count_eq n gs o negb (Elim2Hit n u v a b gs) (.e2 u v a b) (fun h => rfl)]
    unfold elim2Count at hB
    convert Nat.lt_succ_of_le hB

lemma good_red {c : List L} (T : List ℕ) (g : ℕ) (hc : pos (.red T g) ∈ c)
    (h : ¬ Redundant n gs (rowSet n T) (g - n) → Good (ev n gs o negb) (.cl c)) :
    Good (ev n gs o negb) (.cl c) := by
  by_cases hR : Redundant n gs (rowSet n T) (g - n)
  · exact good_pos _ hc (by simpa [ev] using hR)
  · exact h hR

lemma redCls_good (hs : Shaped n gs) (T : List ℕ) (s : ℕ)
    (hT : s ≠ 0 → redCount n gs (rowSet n T) ≤ gs.length - s) :
    ∀ e ∈ redCls n gs.length T s, Good (ev n gs o negb) e := by
  unfold redCls
  split_ifs with hs0
  · simp
  have hV : ∀ g t, n ≤ g → V gs (row n t) (n + (g - n)) = nodeV n gs t g := fun g t hg => by
    rw [show n + (g - n) = g by omega]; rfl
  rw [List.forall_mem_append, List.forall_mem_append]
  refine ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · simp only [List.mem_map] at he; obtain ⟨g, -, rfl⟩ := he; trivial
  · rw [List.mem_flatMap] at he
    obtain ⟨g, hg, he⟩ := he
    rw [mem_gates] at hg
    revert e he
    rw [List.forall_mem_append, List.forall_mem_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [List.forall_mem_cons]
      refine ⟨good_red n gs o negb T g (by simp) fun hR => ?_,
        good_red n gs o negb T g (by simp) fun hR => ?_, by simp⟩
      · by_contra hcon
        refine hR (Or.inl ⟨false, ?_⟩)
        rintro x ⟨t, ht, rfl⟩
        rw [hV g t hg.1]
        by_contra hne
        exact hcon (good_pos (.val g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩)
          (by simpa [ev] using hne))
      · by_contra hcon
        refine hR (Or.inl ⟨true, ?_⟩)
        rintro x ⟨t, ht, rfl⟩
        rw [hV g t hg.1]
        by_contra hne
        exact hcon (good_ng (.val g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩)
          (by simpa [ev] using hne))
    · intro e he
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at he
      obtain ⟨u, hu, rfl | rfl⟩ := he
      · refine good_red n gs o negb T g (by simp) fun hR => ?_
        by_contra hcon
        refine hR (Or.inr (Or.inl ⟨u, hu, false, ?_⟩))
        rintro x ⟨t, ht, rfl⟩
        rw [hV g t hg.1, row_getD n t u hu]
        by_contra hne
        apply hcon
        cases hb : t.testBit u
        · exact good_pos (.val g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, by simp [hb]⟩)
            (by simp only [ev]; simpa [hb] using hne)
        · exact good_ng (.val g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, by simp [hb]⟩)
            (by simp only [ev]; simpa [hb] using hne)
      · refine good_red n gs o negb T g (by simp) fun hR => ?_
        by_contra hcon
        refine hR (Or.inr (Or.inl ⟨u, hu, true, ?_⟩))
        rintro x ⟨t, ht, rfl⟩
        rw [hV g t hg.1, row_getD n t u hu]
        by_contra hne
        apply hcon
        cases hb : t.testBit u
        · exact good_ng (.val g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, by simp [hb]⟩)
            (by simp only [ev]; simpa [hb] using hne)
        · exact good_pos (.val g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, by simp [hb]⟩)
            (by simp only [ev]; simpa [hb] using hne)
    · intro e he
      simp only [List.mem_flatMap, List.mem_filter, mem_gates, decide_eq_true_eq,
        List.mem_append, List.mem_map, List.mem_singleton] at he
      obtain ⟨h, ⟨hh, hhg⟩, he⟩ := he
      have hred : ∀ b : Bool, (∀ t ∈ T, nodeV n gs t g = (b ^^ nodeV n gs t h)) →
          Redundant n gs (rowSet n T) (g - n) := by
        intro b hb
        refine Or.inr (Or.inr ⟨h - n, by omega, b, ?_⟩)
        rintro x ⟨t, ht, rfl⟩
        rw [hV g t hg.1, hV h t hh.1]; exact hb t ht
      rcases he with ((⟨t, ht, rfl⟩ | rfl) | ⟨t, ht, rfl⟩) | rfl
      · intro d hd
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;>
          cases h1 : nodeV n gs t h <;> cases h2 : nodeV n gs t g <;> simp_all [ev, ng, pos]
      · refine good_red n gs o negb T g (by simp) fun hR => ?_
        by_contra hcon
        refine hR (hred false fun t ht => ?_)
        by_contra hne
        apply hcon
        refine good_pos (.diff h g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩) ?_
        simp only [ev]; revert hne
        cases nodeV n gs t h <;> cases nodeV n gs t g <;> simp
      · intro d hd
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;>
          cases h1 : nodeV n gs t h <;> cases h2 : nodeV n gs t g <;> simp_all [ev, ng, pos]
      · refine good_red n gs o negb T g (by simp) fun hR => ?_
        by_contra hcon
        refine hR (hred true fun t ht => ?_)
        by_contra hne
        apply hcon
        refine good_pos (.same h g t) (by simp [List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩) ?_
        simp only [ev]; revert hne
        cases nodeV n gs t h <;> cases nodeV n gs t g <;> simp
  · apply atMost_good
    rw [count_eq n gs o negb (Redundant n gs (rowSet n T)) (.red T) (fun h => rfl)]
    have := hT hs0
    unfold redCount at this
    convert Nat.lt_succ_of_le this

end Bounds

/-! ### `first01`, `symin`/`symvars`, the table clauses, the outputs -/

section Rest
variable (n : ℕ) (f : List Bool → Bool) (R : Opts) (gs : List Gate) (o : ℕ) (negb : Bool)

lemma chainCls_good (h : Adm n f R gs o negb) (hI : SymInOrd R.S gs) (u w : ℕ) (hu : R.S u)
    (hw : R.S w) (huw : u < w) : ∀ e ∈ chainCls n gs.length u w, Good (ev n gs o negb) e := by
  intro e he
  simp only [chainCls, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
  obtain ⟨x, ⟨hx, hxw⟩, rfl⟩ := he
  obtain ⟨⟨hg1, hg2⟩, -, -⟩ := sel_lt n gs x hx
  refine good_sel n gs o negb x.1 x.2.1 x.2.2 (by simp) fun hsl => ?_
  have hr := reads_of_sel n gs _ _ _ hg1 hg2 hsl w hxw
  obtain ⟨g, hg, hgu⟩ := hI u w hu hw huw (x.1 - n) (by omega) hr
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [List.length_take] at hk
  have hk' : k < gs.length := by omega
  rw [List.getElem_take] at hgu
  have hm := sel_mem n gs h.shaped (n + k) (by omega) (by omega)
  rw [gt_add n gs k hk'] at hm
  refine good_pos (.sel (n + k) gs[k].a gs[k].b) (List.mem_cons_of_mem _ (List.mem_map.mpr
    ⟨_, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩)) ?_
  · simp only [decide_eq_true_eq]; exact ⟨by omega, hgu⟩
  · have := ev_sel_self n gs o negb (n + k); rwa [gt_add n gs k hk'] at this

/-- The first gate's table, from `TableOK`. -/
lemma table_good (h : Adm n f R gs o negb) (hT : TableOK R.S gs) (c : List L)
    (h1 : ng (.fbit n false true) ∈ c) (h2 : pos (.fbit n true false) ∈ c)
    (h3 : pos (.fbit n true true) ∈ c) (hS : R.S (gt n gs n).a ∧ R.S (gt n gs n).b) :
    Good (ev n gs o negb) (.cl c) := by
  have hpos : 0 < gs.length := by have := h.out_lo; have := h.out_hi; omega
  have hg : gt n gs n = gs[0] := by rw [gt_eq n gs n (by omega)]; simp
  have hT' := hT hpos (hg ▸ hS.1) (hg ▸ hS.2)
  rw [← hg] at hT'
  unfold T100 at hT'
  by_cases a : (gt n gs n).op false true = false
  · exact good_ng _ h1 a
  by_cases b : (gt n gs n).op true false = true
  · exact good_pos _ h2 b
  by_cases d : (gt n gs n).op true true = true
  · exact good_pos _ h3 d
  exact absurd ⟨by simpa using a, by simpa using b, by simpa using d⟩ hT'

lemma outCls_good (h : Adm n f R gs o negb) (tt : ℕ → Bool) (htt : ∀ t < 2 ^ n, tt t = f (row n t)) :
    ∀ e ∈ outCls n gs.length tt, Good (ev n gs o negb) e := by
  unfold outCls
  rw [List.forall_mem_append]
  constructor
  · refine exactlyOne_good _ _ ((gates_nodup _ _).map (fun a b h => by cases h; rfl)) ?_ ?_
    · exact ⟨.osel o, List.mem_map.mpr ⟨o, (mem_gates _ _ _).mpr ⟨h.out_lo, h.out_hi⟩, rfl⟩,
        by simp [ev]⟩
    · intro a ha b hb hva hvb
      simp only [List.mem_map] at ha hb
      obtain ⟨i, -, rfl⟩ := ha
      obtain ⟨i', -, rfl⟩ := hb
      simp only [ev, decide_eq_true_eq] at hva hvb
      rw [← hva, ← hvb]
  · intro e he
    simp only [List.mem_flatMap] at he
    obtain ⟨i, -, t, ht, he⟩ := he
    rw [mem_rows] at ht
    have hout : (negb ^^ nodeV n gs t o) = tt t := by
      rw [htt t ht]; exact h.computes (row n t) (row_length n t)
    by_cases hoi : o = i
    swap
    · split_ifs at he <;> simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at he <;> rcases he with rfl | rfl <;>
        exact good_ng (.osel i) (by simp) (by simpa [ev] using hoi)
    subst hoi
    have h3 : ∀ {l1 l2 l3 : L}, (ev n gs o negb l2.1 = l2.2 ∨ ev n gs o negb l3.1 = l3.2) →
        Good (ev n gs o negb) (.cl [l1, l2, l3]) := by
      intro l1 l2 l3 h
      rcases h with h | h
      · exact ⟨l2, by simp, h⟩
      · exact ⟨l3, by simp, h⟩
    cases htv : tt t <;> simp only [htv, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at he <;> rcases he with rfl | rfl <;>
      refine h3 ?_ <;> simp only [ev, pos, ng] <;> revert hout <;> rw [htv] <;>
      cases nodeV n gs t o <;> cases negb <;> simp

end Rest

/-! ### The whole encoding -/

/-- The encoder options ask for nothing the run's `Opts` does not grant. -/
structure Fits (n : ℕ) (R : Opts) (o : EOpts) : Prop where
  first01 : o.first01 = true → R.first01 = true
  allin : o.allin = true → R.allin = true
  elim : ∀ s, o.elim = some s → ∃ e, R.elim = some e ∧ s.1 ≤ e false ∧ s.2 ≤ e true
  elim2 : ∀ s, o.elim2 = some s → ∃ e, R.elim2 = some e ∧
    ∀ a b : Bool, [s.1, s.2.1, s.2.2].getD (a.toNat + b.toNat) 0 ≤ e a b
  red : ∀ x ∈ o.red, x.2 ≠ 0 → ∃ s', R.sem (rowSet n x.1) s' ∧ x.2 ≤ s'
  symin : o.symin = true → R.symin = true ∧ ∀ u < n, R.S u
  symvars : ∀ S, o.symvars = some S → R.symin = true ∧ R.table = true ∧ (∀ u ∈ S, R.S u) ∧
    ∀ p ∈ S.zip S.tail, p.1 < p.2
  table : o.table = true → R.table = true ∧ ∀ u < n, R.S u

/-- **Every event of the run's encoding holds for an `Adm` circuit.** -/
theorem events_good (n : ℕ) (f : List Bool → Bool) (R : Opts) (gs : List Gate) (o : ℕ)
    (negb : Bool) (h : Adm n f R gs o negb) (tt : ℕ → Bool)
    (htt : ∀ t < 2 ^ n, tt t = f (row n t)) (eo : EOpts) (hF : Fits n R eo) :
    ∀ e ∈ events n gs.length tt eo, Good (ev n gs o negb) e := by
  have hpos : 0 < gs.length := by have := h.out_lo; have := h.out_hi; omega
  have hg0 : gt n gs n = gs[0] := by rw [gt_eq n gs n (by omega)]; simp
  unfold events
  simp only [List.forall_mem_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨coreDecls_good n gs o negb, coreCls_good n gs o negb h.shaped h.normal⟩,
    symCls_good n f R gs o negb h⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · split_ifs
    · exact orderCls_good n f R gs o negb h
    · simp
  · split_ifs with hA
    · exact allinCls_good n f R gs o negb h (hF.allin hA) tt htt
    · simp
  · split_ifs
    · exact distinctCls_good n f R gs o negb h
    · simp
  · split
    · rename_i s hs
      obtain ⟨e, he, h0, h1⟩ := hF.elim s hs
      intro x hx
      simp only [elimCls, List.mem_flatMap, List.mem_range, List.mem_append] at hx
      obtain ⟨v, hv, (hx | hx) | hx⟩ := hx
      · exact kCls_good n gs o negb h.normal v x hx
      · exact e1Cls_good n gs o negb h.shaped v false _ (by have := h.elim e he v hv false; omega) x hx
      · exact e1Cls_good n gs o negb h.shaped v true _ (by have := h.elim e he v hv true; omega) x hx
    · simp
  · split
    · rename_i s hs
      obtain ⟨e, he, hle⟩ := hF.elim2 s hs
      intro x hx
      simp only [elim2Cls, List.mem_flatMap] at hx
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨u, v, rfl, hsub⟩ := mem_combs2 _ c hc
      have huv := sublist_pair_lt _ (List.pairwise_lt_range) u v hsub
      have hu : u < n := List.mem_range.mp (hsub.subset (by simp))
      have hv : v < n := List.mem_range.mp (hsub.subset (by simp))
      simp only [List.flatMap_cons, List.flatMap_nil, List.mem_append, List.not_mem_nil,
        or_false] at hx
      have key : ∀ a b : Bool, ∀ y ∈ e2Cls n gs.length u v a b
          (gs.length - [s.1, s.2.1, s.2.2].getD (a.toNat + b.toNat) 0), Good (ev n gs o negb) y :=
        fun a b => e2Cls_good n gs o negb h.shaped u v a b _
          (by have := h.elim2 e he u hu v hv huv a b; have := hle a b; omega)
      rcases hx with hx | hx | hx | hx
      · exact key false false x hx
      · exact key false true x hx
      · exact key true false x hx
      · exact key true true x hx
    · simp
  · intro x hx
    simp only [List.mem_flatMap] at hx
    obtain ⟨y, hy, hx⟩ := hx
    refine redCls_good n gs o negb h.shaped y.1 y.2 (fun hs0 => ?_) x hx
    obtain ⟨s', hs', hle⟩ := hF.red y hy hs0
    have := h.sem _ _ hs'
    omega
  · split_ifs with h01
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨ha, hb⟩ := h.first01 (hF.first01 h01) hpos
      exact good_pos (.sel n 0 1) (by simp) (by simp [ev, hg0, ha, hb])
    · simp
  · split_ifs with hS
    · obtain ⟨hR, hall⟩ := hF.symin hS
      intro x hx
      simp only [syminCls, List.mem_flatMap, List.mem_range] at hx
      obtain ⟨u, hu, hx⟩ := hx
      exact chainCls_good n f R gs o negb h (h.symin hR) u (u + 1) (hall u (by omega))
        (hall (u + 1) (by omega)) (by omega) x hx
    · simp
  · split
    · rename_i S hS
      obtain ⟨hR, hT, hall, hch⟩ := hF.symvars S hS
      intro x hx
      simp only [symvarsCls, List.mem_append, List.mem_flatMap] at hx
      rcases hx with ⟨p, hp, hx⟩ | ⟨c, hc, hx⟩
      · have hp1 : p.1 ∈ S := (List.of_mem_zip hp).1
        have hp2 : p.2 ∈ S := List.mem_of_mem_tail (List.of_mem_zip hp).2
        exact chainCls_good n f R gs o negb h (h.symin hR) p.1 p.2 (hall _ hp1) (hall _ hp2)
          (hch p hp) x hx
      · obtain ⟨a, b, rfl, hsub⟩ := mem_combs2 _ c hc
        simp only [List.mem_singleton] at hx
        subst hx
        refine good_sel n gs o negb n a b (by simp [tableCl]) fun hsl => ?_
        exact table_good n f R gs o negb h (h.table hT) _ (by simp [tableCl]) (by simp [tableCl])
          (by simp [tableCl]) ⟨hsl.1 ▸ hall a (hsub.subset (by simp)),
            hsl.2 ▸ hall b (hsub.subset (by simp))⟩
    · simp
  · exact outCls_good n f R gs o negb h tt htt
  · split_ifs with hT
    · obtain ⟨hR, hall⟩ := hF.table hT
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨hab, hbn, -⟩ := nodeV_gate n gs h.shaped n (le_refl n) (by omega) 0
      exact table_good n f R gs o negb h (h.table hR) _ (by simp [firstTableCl])
        (by simp [firstTableCl]) (by simp [firstTableCl]) ⟨hall _ (by omega), hall _ (by omega)⟩
    · simp

/-- **An `Adm` circuit of `r` gates in a cube satisfies the cube's CNF for `r`.** -/
theorem adm_sat (n : ℕ) (f : List Bool → Bool) (R : Opts) (gs : List Gate) (o : ℕ) (negb : Bool)
    (h : Adm n f R gs o negb) (tt : ℕ → Bool) (htt : ∀ t < 2 ^ n, tt t = f (row n t))
    (eo : EOpts) (hF : Fits n R eo) (cube : List L)
    (hcube : ∀ l ∈ cube, ev n gs o negb l.1 = l.2) :
    ¬ (toCNF (cnfOf (events n gs.length tt eo ++ cube.map fun l => .cl [l]))).Unsat := by
  intro hU
  have hgood : ∀ e ∈ events n gs.length tt eo ++ cube.map (fun l => .cl [l]),
      Good (ev n gs o negb) e := by
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact events_good n f R gs o negb h tt htt eo hF e he
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      exact ⟨l, by simp, hcube l hl⟩
  have := number_sat _ _ hgood
  rw [hU] at this
  exact Bool.false_ne_true this

end CnfSound
