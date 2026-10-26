/-
# From a minimum circuit to the CNF's shape, and back

The SAT runs in `research/circuits/` search a restricted shape (`SymCanon.Shaped`, `Normal`, output
any gate xor `neg`) under extra constraints. This file connects that shape to `CircuitDual`'s bare
model (output = last node, any table, any reads), where "size" is defined.

Proved (axioms: the standard three):
* `shape_of_min`: for `f` neither constant nor a literal, a minimum bare circuit has a shaped,
  normal circuit of the same length computing `f` with output its last node. (Every gate of a
  minimum circuit reads two distinct in-range nodes, else it is redundant; sort each pair; push
  negations forward so every table is 0 on 00.)
* `bare_of_shaped`: a shaped circuit with output `o` gives a bare circuit of `o − n + 1` gates.
  So in a shaped circuit of minimum length, the output is the last gate.
* `delete_dead`: a gate that is neither the output nor read by a later gate can be deleted.
* `unread_input`: an input that no gate reads does not affect any gate.
* `redundant_of_const_arg`: a gate with an argument that is constant on `T` is redundant on `T`
  (the fact behind `elim`/`elim2`).

Then `minimal_canonical` assembles, for a function symmetric in all inputs: a minimum circuit
yields one of the same length, in the CNF's shape, satisfying `order`, `symin`, `first01`, the
table clause, `sym` (no dead gate; no degenerate gate), `distinct` and `allin`, together with a
bare circuit of the same length whose gates are redundant exactly where the shaped one's are.
-/
import Garden.SymCanon

namespace Reduction
open CircuitDual GateElim SymBreak SymCanon

/-- A bare circuit computing `f` on `n`-bit rows. -/
def BareComputes (n : ℕ) (f : List Bool → Bool) (gs : List Gate) : Prop :=
  gs ≠ [] ∧ ∀ x : List Bool, x.length = n → out x gs = f x

/-! ### A gate's value, from its two reads -/

/-- What gate `j` reads at node `c`: the value among the first `n + j` nodes, `false` past them. -/
lemma gate_val' (x : List Bool) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    V gs x (x.length + j) = gs[j].op ((run x (gs.take j)).getD gs[j].a false)
      ((run x (gs.take j)).getD gs[j].b false) := by
  unfold V
  rw [run_take_getD x gs (j + 1) _ (by omega) (by omega), gate_val x gs j hj]

lemma read_val (x : List Bool) (gs : List Gate) (j c : ℕ) (hj : j < gs.length) :
    (run x (gs.take j)).getD c false = if c < x.length + j then V gs x c else false := by
  split_ifs with h
  · unfold V; rw [run_take_getD x gs j _ hj.le h]
  · rw [List.getD_eq_default]; rw [run_length, List.length_take, min_eq_left hj.le]; omega

lemma bool_fun (φ : Bool → Bool) : (∃ c, ∀ y, φ y = c) ∨ (∃ b, ∀ y, φ y = (b ^^ y)) := by
  cases h0 : φ false <;> cases h1 : φ true
  · exact Or.inl ⟨false, fun y => by cases y <;> assumption⟩
  · exact Or.inr ⟨false, fun y => by cases y <;> simp [*]⟩
  · exact Or.inr ⟨true, fun y => by cases y <;> simp [*]⟩
  · exact Or.inl ⟨true, fun y => by cases y <;> assumption⟩

/-- A gate whose value on `T` is a function of one earlier node is redundant on `T`. -/
lemma redundant_of_fun (n : ℕ) (gs : List Gate) (T : Set (List Bool))
    (hT : ∀ x ∈ T, x.length = n) (j y : ℕ) (hy : y < n + j) (φ : Bool → Bool)
    (h : ∀ x ∈ T, V gs x (n + j) = φ (V gs x y)) : Redundant n gs T j := by
  rcases bool_fun φ with ⟨c, hc⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨c, fun x hx => by rw [h x hx, hc]⟩
  · by_cases hyn : y < n
    · refine Or.inr (Or.inl ⟨y, hyn, b, fun x hx => ?_⟩)
      rw [h x hx, hb]; unfold V; rw [run_getD_input _ _ _ (by rw [hT x hx]; exact hyn)]
    · refine Or.inr (Or.inr ⟨y - n, by omega, b, fun x hx => ?_⟩)
      rw [h x hx, hb, show n + (y - n) = y by omega]

/-- Gate `j` reads two in-range nodes: its value is its table applied to theirs. -/
lemma V_gate (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (ha : gs[j].a < n + j) (hb : gs[j].b < n + j) :
    V gs x (n + j) = gs[j].op (V gs x gs[j].a) (V gs x gs[j].b) := by
  have := gate_val' x gs j hj
  rw [read_val x gs j _ hj, read_val x gs j _ hj, hx, if_pos ha, if_pos hb] at this
  exact this

/-- **A gate with an argument that is constant on `T` is redundant on `T`.** -/
lemma redundant_of_const_arg (n : ℕ) (gs : List Gate) (T : Set (List Bool))
    (hT : ∀ x ∈ T, x.length = n) (j : ℕ) (hj : j < gs.length) (ha : gs[j].a < n + j)
    (hb : gs[j].b < n + j)
    (hc : (∃ c, ∀ x ∈ T, V gs x gs[j].a = c) ∨ (∃ c, ∀ x ∈ T, V gs x gs[j].b = c)) :
    Redundant n gs T j := by
  rcases hc with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply redundant_of_fun n gs T hT j gs[j].b hb (fun v => gs[j].op c v)
    intro x hx; rw [V_gate n x (hT x hx) gs j hj ha hb, hc x hx]
  · apply redundant_of_fun n gs T hT j gs[j].a ha (fun u => gs[j].op u c)
    intro x hx; rw [V_gate n x (hT x hx) gs j hj ha hb, hc x hx]

/-- In a circuit with no gate redundant on all rows, every gate reads two distinct in-range
nodes. -/
lemma reads_ok (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hnr : ¬ Redundant n gs {x | x.length = n} j) :
    gs[j].a < n + j ∧ gs[j].b < n + j ∧ gs[j].a ≠ gs[j].b := by
  have hT : ∀ x ∈ ({x | x.length = n} : Set (List Bool)), x.length = n := fun x hx => hx
  have val : ∀ x : List Bool, x.length = n → V gs x (n + j) = gs[j].op
      (if gs[j].a < n + j then V gs x gs[j].a else false)
      (if gs[j].b < n + j then V gs x gs[j].b else false) := by
    intro x hx
    have := gate_val' x gs j hj
    rw [read_val x gs j _ hj, read_val x gs j _ hj, hx] at this
    exact this
  by_contra hbad
  apply hnr
  by_cases ha : gs[j].a < n + j
  · by_cases hb : gs[j].b < n + j
    · have he : gs[j].a = gs[j].b := by omega
      apply redundant_of_fun n gs _ hT j gs[j].a ha (fun v => gs[j].op v v)
      intro x hx; rw [val x hx, if_pos ha, if_pos hb, ← he]
    · apply redundant_of_fun n gs _ hT j gs[j].a ha (fun v => gs[j].op v false)
      intro x hx; rw [val x hx, if_pos ha, if_neg hb]
  · by_cases hb : gs[j].b < n + j
    · apply redundant_of_fun n gs _ hT j gs[j].b hb (fun v => gs[j].op false v)
      intro x hx; rw [val x hx, if_neg ha, if_pos hb]
    · exact Or.inl ⟨gs[j].op false false, fun x hx => by rw [val x hx, if_neg ha, if_neg hb]⟩

/-! ### Normal tables: push each gate's value on `00` forward -/

/-- Normalize one gate, given which nodes so far are stored negated (`fl`). It reads the same
pair, stores its value xor `t`, and `t` makes its table 0 on 00. -/
def normG (fl : List Bool) (g : Gate) : Gate × Bool :=
  (⟨g.a, g.b, fun u v => g.op (fl.getD g.a false) (fl.getD g.b false) ^^
      g.op (fl.getD g.a false ^^ u) (fl.getD g.b false ^^ v)⟩,
    g.op (fl.getD g.a false) (fl.getD g.b false))

def normL : List Bool → List Gate → List Gate × List Bool
  | fl, [] => ([], fl)
  | fl, g :: gs => ((normG fl g).1 :: (normL (fl ++ [(normG fl g).2]) gs).1,
      (normL (fl ++ [(normG fl g).2]) gs).2)

/-- `l'` stores `l` xor `fl`. -/
def NRel (fl l' l : List Bool) : Prop :=
  l'.length = l.length ∧ fl.length = l.length ∧
    ∀ i, l'.getD i false = (l.getD i false ^^ fl.getD i false)

lemma nrel_step (fl l' l : List Bool) (g : Gate) (h : NRel fl l' l) :
    NRel (fl ++ [(normG fl g).2]) (step l' (normG fl g).1) (step l g) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp [step, h1], by simp [step, h2], fun i => ?_⟩
  simp only [step, normG]
  rw [getD_append_single, getD_append_single, getD_append_single, h1, h2]
  simp only [h3]
  have e : ∀ p q : Bool, (p ^^ (q ^^ p)) = q := by decide
  simp only [e]
  split_ifs with hi hi'
  · rfl
  · cases g.op (fl.getD g.a false) (fl.getD g.b false) <;>
      cases g.op (l.getD g.a false) (l.getD g.b false) <;> rfl
  · rfl

lemma nrel_run (gs : List Gate) : ∀ (fl l' l : List Bool), NRel fl l' l →
    NRel (normL fl gs).2 (run l' (normL fl gs).1) (run l gs) := by
  induction gs with
  | nil => intro fl l' l h; simpa [normL, run] using h
  | cons g gs ih =>
    intro fl l' l h
    simpa [normL, run] using ih _ _ _ (nrel_step fl l' l g h)

lemma normL_length (gs : List Gate) : ∀ fl, (normL fl gs).1.length = gs.length := by
  induction gs with
  | nil => intro; rfl
  | cons g gs ih => intro fl; simp [normL, ih]

lemma normL_getElem (gs : List Gate) : ∀ fl (i : ℕ) (h : i < (normL fl gs).1.length),
    (normL fl gs).1[i].a = (gs[i]'(by rw [normL_length] at h; exact h)).a ∧
    (normL fl gs).1[i].b = (gs[i]'(by rw [normL_length] at h; exact h)).b := by
  induction gs with
  | nil => intro fl i h; simp [normL] at h
  | cons g gs ih =>
    intro fl i h
    cases i with
    | zero => simp [normL, normG]
    | succ i => simpa [normL] using ih _ i (by simpa [normL] using h)

lemma normL_normal (gs : List Gate) : ∀ fl, Normal (normL fl gs).1 := by
  induction gs with
  | nil => intro fl g hg; simp [normL] at hg
  | cons g gs ih =>
    intro fl g' hg'
    simp only [normL, List.mem_cons] at hg'
    rcases hg' with rfl | h
    · simp [normG]
    · exact ih _ g' h

/-! ### A minimum circuit in the CNF's shape -/

/-- **A minimum bare circuit, in the CNF's shape.** For `f` neither constant nor a literal, a
minimum bare circuit has a shaped, normal circuit of the same length computing `f`, with output
its last node. -/
theorem shape_of_min (n : ℕ) (f : List Bool → Bool) (gs : List Gate) (hgs : BareComputes n f gs)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (hmin : ∀ gs', BareComputes n f gs' → gs.length ≤ gs'.length) :
    ∃ gs1 neg, gs1.length = gs.length ∧ Shaped n gs1 ∧ Normal gs1 ∧
      ComputesAt n f gs1 (n + gs.length - 1) neg := by
  have h0 := minimum_no_redundant n gs f hgs.1 hgs.2 hc hl (fun gs' h1 h2 => hmin gs' ⟨h1, h2⟩)
  have hnr : ∀ j (hj : j < gs.length), ¬ Redundant n gs {x | x.length = n} j := by
    classical
    intro j hj hr
    simp only [redCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_range] at h0
    exact h0 hj hr
  set gsS := gs.map sortG with hgsS
  set N := normL (List.replicate n false) gsS with hN
  have hlenS : gsS.length = gs.length := by simp [gsS]
  have hlenN : N.1.length = gs.length := by rw [hN, normL_length, hlenS]
  refine ⟨N.1, N.2.getD (n + gs.length - 1) false, hlenN, ?_, ?_, ?_⟩
  · rw [shaped_iff]
    intro i hi
    obtain ⟨ea, eb⟩ := normL_getElem gsS _ i hi
    have hi' : i < gs.length := by omega
    obtain ⟨ha, hb, hne⟩ := reads_ok n gs i hi' (hnr i hi')
    rw [ea, eb]
    simp only [gsS, List.getElem_map, sortG]
    split_ifs <;> (try dsimp only at *) <;> omega
  · exact normL_normal gsS _
  · intro x hx
    have hR := nrel_run gsS (List.replicate n false) x x
      ⟨rfl, by simp [hx], fun i => by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> simp⟩
    have hne : gs.length ≠ 0 := by simpa using hgs.1
    unfold outAt
    rw [hR.2.2, ← hgs.2 x hx, out, getLastD_eq_getD, run_length, hx, ← hN,
      show run x gsS = run x gs from run_map_sortG x gs]
    cases N.2.getD (n + gs.length - 1) false <;> simp

/-! ### Reading the output off a gate -/

/-- The bare circuit read off a shaped one with output `(o, neg)`: the gates up to `o`, with
`neg` folded into gate `o`. -/
def toBare (n : ℕ) (gs : List Gate) (o : ℕ) (neg : Bool) : List Gate :=
  gs.take (o - n) ++ [negOut neg (gs.getD (o - n) dflt)]

/-- A shaped circuit with output `o` gives a bare circuit of `o − n + 1` gates computing the same
function. -/
theorem bare_of_shaped (n : ℕ) (f : List Bool → Bool) (gs : List Gate) (o : ℕ) (neg : Bool)
    (ho1 : n ≤ o) (ho2 : o < n + gs.length) (hc : ComputesAt n f gs o neg) :
    (toBare n gs o neg).length = o - n + 1 ∧ BareComputes n f (toBare n gs o neg) := by
  have hm : o - n < gs.length := by omega
  refine ⟨by simp [toBare]; omega, by simp [toBare], fun x hx => ?_⟩
  rw [toBare, out_snoc, ← hc x hx, outAt, List.getD_eq_getElem _ _ hm]
  have := gate_val' x gs (o - n) hm
  rw [hx, show n + (o - n) = o by omega] at this
  unfold V at this
  rw [this]; rfl

/-! ### Deleting a dead gate -/

/-- Where node `i` of the shorter circuit came from, when node `p` is deleted. -/
def up (p i : ℕ) : ℕ := if i < p then i else i + 1

/-- Renumber reads past the deleted node `p`. -/
def dl (p i : ℕ) : ℕ := if p < i then i - 1 else i

def DRel (p : ℕ) (l' l : List Bool) : Prop :=
  l.length = l'.length + 1 ∧ p ≤ l'.length ∧ ∀ i, l'.getD i false = l.getD (up p i) false

lemma drel_step (p : ℕ) (l' l : List Bool) (g : Gate) (h : DRel p l' l) (ha : g.a ≠ p)
    (hb : g.b ≠ p) : DRel p (step l' (mapG (dl p) g)) (step l g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have ud : ∀ c, c ≠ p → up p (dl p c) = c := by intro c hc; unfold up dl; split_ifs <;> omega
  refine ⟨by simp [step, h1], by simp [step]; omega, fun i => ?_⟩
  simp only [step, mapG]
  rw [getD_append_single, getD_append_single]
  simp only [h3]
  rw [ud _ ha, ud _ hb, h1]
  unfold up; split_ifs <;> first | rfl | omega

lemma drel_run (p : ℕ) (B : List Gate) (hB : ∀ g ∈ B, g.a ≠ p ∧ g.b ≠ p) :
    ∀ l' l, DRel p l' l → DRel p (run l' (B.map (mapG (dl p)))) (run l B) := by
  induction B with
  | nil => intro l' l h; simpa [run] using h
  | cons g B ih =>
    intro l' l h
    have hg := hB g (by simp)
    simpa [run] using ih (fun g' hg' => hB g' (by simp [hg'])) _ _ (drel_step p l' l g h hg.1 hg.2)

/-- **Deleting a gate that no later gate reads.** Every node of the shorter circuit is the old
node it came from. -/
theorem delete_nodes (x : List Bool) (A B : List Gate) (g : Gate)
    (hB : ∀ h ∈ B, ¬ Reads h (x.length + A.length)) (i : ℕ) :
    (run x (A ++ B.map (mapG (dl (x.length + A.length))))).getD i false =
      (run x (A ++ g :: B)).getD (up (x.length + A.length) i) false := by
  set p := x.length + A.length
  have split : ∀ (P Q : List Gate) (y : List Bool), run y (P ++ Q) = run (run y P) Q := by
    intro P Q y; simp only [run, List.foldl_append]
  have hlen : (run x A).length = p := by rw [run_length]
  have h0 : DRel p (run x A) (step (run x A) g) := by
    refine ⟨by simp [step], by omega, fun j => ?_⟩
    simp only [step]; rw [getD_append_single]; unfold up
    split_ifs <;> first | rfl | omega | (rw [List.getD_eq_default _ _ (by omega)])
  have := drel_run p B (fun h hh => by have := hB h hh; unfold Reads at this; omega) _ _ h0
  rw [split, split, show g :: B = [g] ++ B from rfl, split]
  simpa [run] using this.2.2 i

/-! ### An input nobody reads -/

def ARel (u : ℕ) (l l' : List Bool) : Prop :=
  l.length = l'.length ∧ u < l.length ∧ ∀ i, i ≠ u → l.getD i false = l'.getD i false

lemma arel_run (u : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, ¬ Reads g u) :
    ∀ l l', ARel u l l' → ARel u (run l gs) (run l' gs) := by
  induction gs with
  | nil => intro l l' h; simpa [run] using h
  | cons g gs ih =>
    intro l l' h
    obtain ⟨h1, h2, h3⟩ := h
    have hg := hgs g (by simp); unfold Reads at hg; push Not at hg
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    refine ⟨by simp [step, h1], by simp [step]; omega, fun i hi => ?_⟩
    simp only [step]
    rw [getD_append_single, getD_append_single, h1, h3 _ hg.1, h3 _ hg.2]
    split_ifs <;> first | rfl | exact h3 i hi

/-- Flip input `u`. -/
def flipAt (u : ℕ) (x : List Bool) : List Bool := x.set u (!x.getD u false)

/-- **An input that no gate reads does not affect any gate.** -/
theorem unread_input (x : List Bool) (u : ℕ) (hu : u < x.length) (gs : List Gate)
    (hgs : ∀ g ∈ gs, ¬ Reads g u) (i : ℕ) (hi : i ≠ u) :
    (run x gs).getD i false = (run (flipAt u x) gs).getD i false := by
  apply (arel_run u gs hgs x (flipAt u x) ⟨by simp [flipAt], hu, fun j hj => ?_⟩).2.2 i hi
  simp [flipAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]

/-! ### Folding the output's negation into the last gate keeps every gate's redundancy -/

lemma redundant_congr (n : ℕ) (gs1 gs2 : List Gate) (T : Set (List Bool)) (j : ℕ) (e : Bool)
    (hj : ∀ x ∈ T, V gs1 x (n + j) = (e ^^ V gs2 x (n + j)))
    (hh : ∀ x ∈ T, ∀ h < j, V gs1 x (n + h) = V gs2 x (n + h)) :
    Redundant n gs1 T j ↔ Redundant n gs2 T j := by
  have e2 : ∀ x ∈ T, V gs2 x (n + j) = (e ^^ V gs1 x (n + j)) := by
    intro x hx; rw [hj x hx]; cases e <;> simp
  constructor
  · rintro (⟨c, hc⟩ | ⟨u, hu, b, hb⟩ | ⟨h, hh', b, hb⟩)
    · exact Or.inl ⟨e ^^ c, fun x hx => by rw [e2 x hx, hc x hx]⟩
    · exact Or.inr (Or.inl ⟨u, hu, e ^^ b, fun x hx => by rw [e2 x hx, hb x hx]; cases e <;> simp⟩)
    · exact Or.inr (Or.inr ⟨h, hh', e ^^ b, fun x hx => by
        rw [e2 x hx, hb x hx, hh x hx h hh']; cases e <;> simp⟩)
  · rintro (⟨c, hc⟩ | ⟨u, hu, b, hb⟩ | ⟨h, hh', b, hb⟩)
    · exact Or.inl ⟨e ^^ c, fun x hx => by rw [hj x hx, hc x hx]⟩
    · exact Or.inr (Or.inl ⟨u, hu, e ^^ b, fun x hx => by rw [hj x hx, hb x hx]; cases e <;> simp⟩)
    · exact Or.inr (Or.inr ⟨h, hh', e ^^ b, fun x hx => by
        rw [hj x hx, hb x hx, ← hh x hx h hh']; cases e <;> simp⟩)

/-- `toBare` at the last gate has exactly the redundant gates of the shaped circuit, on every
row set. -/
theorem redCount_toBare (n : ℕ) (gs : List Gate) (neg : Bool) (hne : gs ≠ [])
    (T : Set (List Bool)) (hT : ∀ x ∈ T, x.length = n) :
    redCount n (toBare n gs (n + gs.length - 1) neg) T = redCount n gs T := by
  classical
  have hL : gs.length ≠ 0 := by simpa using hne
  set m := gs.length - 1 with hm
  have hm' : m < gs.length := by omega
  have hgs : gs = gs.take m ++ [gs[m]] := by
    rw [← take_succ' gs m hm', show m + 1 = gs.length by omega, List.take_length]
  have hb : toBare n gs (n + gs.length - 1) neg = gs.take m ++ [negOut neg gs[m]] := by
    simp only [toBare, show n + gs.length - 1 - n = m by omega, List.getD_eq_getElem _ _ hm']
  have hlen : (toBare n gs (n + gs.length - 1) neg).length = gs.length := by
    rw [hb]; simp; omega
  -- node values of the two circuits
  have hV : ∀ x : List Bool, x.length = n → ∀ i,
      V (toBare n gs (n + gs.length - 1) neg) x i =
        if i = n + m then (neg ^^ V gs x i) else V gs x i := by
    intro x hx i
    unfold V
    rw [hb]; conv_rhs => rw [hgs]
    rw [run_append, run_append, step, step, getD_append_single, getD_append_single, run_length,
      List.length_take, min_eq_left hm'.le, hx]
    split_ifs <;> first | rfl | omega
  unfold redCount
  rw [hlen]
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_range] at hj
  apply redundant_congr n _ _ T j (if j = m then neg else false)
  · intro x hx; rw [hV x (hT x hx)]; split_ifs <;> first | rfl | omega | simp
  · intro x hx h hh; rw [hV x (hT x hx), if_neg (by omega)]

/-! ### Assembly -/

/-- `sym`'s no-dead-gate half, with the output at the last gate: every other gate is read by a
later one. -/
def NoDead (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (_ : j + 1 < gs.length), ∃ k, ∃ hk : k < gs.length, j < k ∧ Reads gs[k] (n + j)

/-- `allin`: every input is read by some gate. -/
def AllIn (n : ℕ) (gs : List Gate) : Prop := ∀ u < n, ∃ g ∈ gs, Reads g u

/-- An input the function depends on: flipping it changes `f` on some row. This is
`optimal_circuit.essential_inputs`. -/
def Essential (n : ℕ) (f : List Bool → Bool) (u : ℕ) : Prop :=
  ∃ x : List Bool, x.length = n ∧ f (flipAt u x) ≠ f x

/-- **A minimum circuit, canonicalized, for a function symmetric in a set `S` of inputs.** Let
`f` on `n` inputs be unchanged by swapping any two inputs of `S`, and neither constant nor a
literal. A minimum bare circuit for `f` yields a circuit of the same length in the CNF's shape,
with output its last gate, satisfying `order`, `SymInOrd S`, `TableOK S`, no dead gate, `allin`
for every essential input, and no gate redundant on all rows (`distinct`, and `sym`'s
no-degenerate half); and `toBare` of it is a bare circuit for `f` of the same length. -/
theorem minimal_canonical_on (n : ℕ) (f : List Bool → Bool) (S : ℕ → Prop)
    (hS : ∀ u, S u → u < n) (hsym : SymOn n S f)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (gs : List Gate) (hgs : BareComputes n f gs)
    (hmin : ∀ gs', BareComputes n f gs' → gs.length ≤ gs'.length) :
    ∃ gs' neg, gs'.length = gs.length ∧ Shaped n gs' ∧ Normal gs' ∧
      ComputesAt n f gs' (n + gs'.length - 1) neg ∧ Order n gs' ∧ SymInOrd S gs' ∧
      TableOK S gs' ∧ NoDead n gs' ∧ (∀ u < n, Essential n f u → ∃ g ∈ gs', Reads g u) ∧
      (∀ j < gs'.length, ¬ Redundant n gs' {x | x.length = n} j) ∧
      BareComputes n f (toBare n gs' (n + gs'.length - 1) neg) ∧
      (toBare n gs' (n + gs'.length - 1) neg).length = gs'.length := by
  have hne : gs.length ≠ 0 := by simpa using hgs.1
  obtain ⟨gs1, neg, hl1, hs1, hn1, hc1⟩ := shape_of_min n f gs hgs hc hl hmin
  obtain ⟨gs', o', hl', hs', hn', ho1, ho2, hc', hO, hI, hT⟩ :=
    canonical n S hS f hsym neg gs1 (n + gs.length - 1) hs1 hn1 (by omega) (by omega) hc1
  rw [hl1] at hl'
  have ho : o' = n + gs'.length - 1 := by
    have := hmin _ (bare_of_shaped n f gs' o' neg ho1 ho2 hc').2
    rw [(bare_of_shaped n f gs' o' neg ho1 ho2 hc').1] at this; omega
  subst ho
  obtain ⟨hblen, hbare⟩ := bare_of_shaped n f gs' _ neg ho1 ho2 hc'
  have hblen' : (toBare n gs' (n + gs'.length - 1) neg).length = gs'.length := by
    rw [hblen]; omega
  refine ⟨gs', neg, hl', hs', hn', hc', hO, hI, hT, ?_, ?_, ?_, hbare, hblen'⟩
  · -- no dead gate: delete it and get a shorter circuit
    intro j hj
    by_contra hnone
    push Not at hnone
    have hj' : j < gs'.length := by omega
    have hsplit : gs' = gs'.take j ++ gs'[j] :: gs'.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop j gs']
      rw [List.drop_eq_getElem_cons hj']
    have hAlen : (gs'.take j).length = j := by simp; omega
    have hB : ∀ h ∈ gs'.drop (j + 1), ¬ Reads h (n + j) := by
      intro h hh
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hh
      rw [List.getElem_drop]
      exact hnone (j + 1 + k) (by simp at hk; omega) (by omega)
    set gsD := gs'.take j ++ (gs'.drop (j + 1)).map (mapG (dl (n + j))) with hgsD
    have hDlen : gsD.length = gs'.length - 1 := by simp [gsD]; omega
    have hcD : ComputesAt n f gsD (n + gs'.length - 2) neg := by
      intro x hx
      have := delete_nodes x (gs'.take j) (gs'.drop (j + 1)) gs'[j]
        (by rw [hx, hAlen]; exact hB) (n + gs'.length - 2)
      rw [hx, hAlen] at this
      unfold outAt
      rw [this, ← hsplit, show up (n + j) (n + gs'.length - 2) = n + gs'.length - 1 by
        unfold up; rw [if_neg (by omega)]; omega]
      exact hc' x hx
    have h2 := bare_of_shaped n f gsD (n + gs'.length - 2) neg (by omega) (by omega) hcD
    have := hmin _ h2.2
    rw [h2.1] at this; omega
  · -- `allin`: an unread input would not matter, but an essential one does
    intro u hu hess
    by_contra hnone
    push Not at hnone
    obtain ⟨x, hx, hfx⟩ := hess
    apply hfx
    rw [← hc' (flipAt u x) (by simp [flipAt, hx]), ← hc' x hx]
    unfold outAt
    rw [unread_input x u (by omega) gs' hnone (n + gs'.length - 1) (by omega)]
  · -- no redundant gate: `toBare` of it is minimum
    classical
    have h0 := minimum_no_redundant n _ f (by simp [toBare]) hbare.2 hc hl
      (fun gs'' h1 h2 => by rw [hblen', hl']; exact hmin gs'' ⟨h1, h2⟩)
    rw [redCount_toBare n gs' neg (by intro h; simp [h] at hl'; omega) {x | x.length = n}
      (fun x hx => hx)] at h0
    intro j hj hr
    simp only [redCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_range] at h0
    exact h0 hj hr

/-- **A minimum circuit, canonicalized.** Let `f` on `n` inputs be symmetric, neither constant
nor a literal, and depend on every input. A minimum bare circuit for `f` yields a circuit of the
same length in the CNF's shape, with output its last gate, satisfying `order`, `symin`, `first01`,
the table clause, no dead gate, `allin`, and no gate redundant on all rows (`distinct`, and `sym`'s
no-degenerate half); and `toBare` of it is a bare circuit for `f` of the same length. The case
`S` = all inputs of `minimal_canonical_on`, plus `first01_of_symin`. -/
theorem minimal_canonical (n : ℕ) (f : List Bool → Bool) (hsym : SymOn n (· < n) f)
    (hc : ¬ ∃ c : Bool, ∀ x : List Bool, x.length = n → f x = c)
    (hl : ¬ ∃ u < n, ∃ b : Bool, ∀ x : List Bool, x.length = n → f x = (b ^^ x.getD u false))
    (hess : ∀ u < n, ∃ x : List Bool, x.length = n ∧ f (flipAt u x) ≠ f x)
    (gs : List Gate) (hgs : BareComputes n f gs)
    (hmin : ∀ gs', BareComputes n f gs' → gs.length ≤ gs'.length) :
    ∃ gs' neg, gs'.length = gs.length ∧ Shaped n gs' ∧ Normal gs' ∧
      ComputesAt n f gs' (n + gs'.length - 1) neg ∧ Order n gs' ∧ SymInOrd (· < n) gs' ∧
      (∀ h : 0 < gs'.length, gs'[0].a = 0 ∧ gs'[0].b = 1 ∧ ¬ T100 gs'[0]) ∧
      NoDead n gs' ∧ AllIn n gs' ∧
      (∀ j < gs'.length, ¬ Redundant n gs' {x | x.length = n} j) ∧
      BareComputes n f (toBare n gs' (n + gs'.length - 1) neg) ∧
      (toBare n gs' (n + gs'.length - 1) neg).length = gs'.length := by
  obtain ⟨gs', neg, hl', hs', hn', hc', hO, hI, hT, hND, hAI, hNR, hbare, hblen⟩ :=
    minimal_canonical_on n f (· < n) (fun _ h => h) hsym hc hl gs hgs hmin
  refine ⟨gs', neg, hl', hs', hn', hc', hO, hI, fun h => ?_, hND, fun u hu => hAI u hu (hess u hu),
    hNR, hbare, hblen⟩
  have hshape := (shaped_iff n gs').mp hs'
  obtain ⟨ha, hb⟩ := first01_of_symin n gs' hs' hI h
  have := hshape 0 h
  exact ⟨ha, hb, hT h (show gs'[0].a < n by omega) (show gs'[0].b < n by omega)⟩

end Reduction
