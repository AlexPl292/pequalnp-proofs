import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_270

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

section Main

variable (n : ℕ) (C : Circuit)

def val (x : Fin n → Bool) (r : ℕ) : Bool := (C.wires (List.ofFn x)).getD r false

def rd (x : Fin n → Bool) (r c : ℕ) : Bool := if c < r then val n C x c else false

def gt (r : ℕ) : Gate := C.gates.getD (r - n) ⟨GateOp.or, []⟩

def ia (r : ℕ) : ℕ := (gt n C r).inputs.getD 0 0

def ib (r : ℕ) : ℕ := (gt n C r).inputs.getD 1 0

lemma wires_eq (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma val_input (x : Fin n → Bool) (r : ℕ) (hr : r < n) : val n C x r = x ⟨r, hr⟩ := by
  unfold val
  rw [wires_eq, wiresFrom_getD_lt _ _ _ (by simpa using hr)]
  simp [List.getD, hr]

lemma val_void (x : Fin n → Bool) (r : ℕ) (hr : n + C.gates.length ≤ r) :
    val n C x r = false := by
  unfold val
  rw [List.getD_eq_default]
  rw [wires_eq, wiresFrom_length]
  simpa using hr

lemma val_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val n C x (n + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun c => rd n C x (n + j) c) := by
  unfold val
  rw [wires_eq]
  have h := wiresFrom_getD_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro c _
  unfold rd val
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wiresFrom_length, List.length_take, List.length_ofFn, Nat.min_eq_left (by omega)]
  split_ifs with hc
  · have hw : wiresFrom C.gates (List.ofFn x) =
        wiresFrom (C.gates.drop j) (wiresFrom (C.gates.take j) (List.ofFn x)) := by
      rw [← wiresFrom_append, List.take_append_drop]
    rw [wires_eq, hw, wiresFrom_getD_lt (C.gates.drop j) (wiresFrom (C.gates.take j) (List.ofFn x))
      c (by rw [hlen]; exact hc)]
  · rw [List.getD_eq_default _ _ (by omega)]

variable {n C}

lemma gt_eq (r : ℕ) (h1 : n ≤ r) (h2 : r < n + C.gates.length) :
    gt n C r = C.gates[r - n]'(by omega) := by
  unfold gt
  rw [List.getD_eq_getElem]

lemma gate_inputs (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (r : ℕ) (h1 : n ≤ r) (h2 : r < n + C.gates.length) :
    ((gt n C r).op = GateOp.and ∨ (gt n C r).op = GateOp.or) ∧
      (gt n C r).inputs = [ia n C r, ib n C r] := by
  have hmem : gt n C r ∈ C.gates := by
    rw [gt_eq r h1 h2]
    exact List.getElem_mem _
  obtain ⟨hop, hlen⟩ := hg _ hmem
  refine ⟨hop, ?_⟩
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
  simp [ia, ib, hab]

lemma val_eq (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (r : ℕ) (h1 : n ≤ r) (h2 : r < n + C.gates.length) (x : Fin n → Bool) :
    val n C x r = (gt n C r).op.eval [rd n C x r (ia n C r), rd n C x r (ib n C r)] := by
  obtain ⟨_, hin⟩ := gate_inputs hg r h1 h2
  have hj : r - n < C.gates.length := by omega
  have e := val_gate n C x (r - n) hj
  rw [show n + (r - n) = r by omega] at e
  rw [e, ← gt_eq r h1 h2, hin]
  rfl

lemma val_and (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (r : ℕ) (h1 : n ≤ r) (h2 : r < n + C.gates.length) (hop : (gt n C r).op = GateOp.and)
    (x : Fin n → Bool) :
    val n C x r = (rd n C x r (ia n C r) && rd n C x r (ib n C r)) := by
  rw [val_eq hg r h1 h2, hop]
  simp [GateOp.eval]

lemma val_or (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (r : ℕ) (h1 : n ≤ r) (h2 : r < n + C.gates.length) (hop : (gt n C r).op = GateOp.or)
    (x : Fin n → Bool) :
    val n C x r = (rd n C x r (ia n C r) || rd n C x r (ib n C r)) := by
  rw [val_eq hg r h1 h2, hop]
  simp [GateOp.eval]

lemma val_mono (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ r, val n C x r = true → val n C y r = true := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hx
    by_cases hr : r < n
    · rw [val_input n C x r hr] at hx
      rw [val_input n C y r hr]
      exact hxy _ hx
    by_cases hr2 : n + C.gates.length ≤ r
    · rw [val_void n C x r hr2] at hx
      exact absurd hx (by simp)
    have h1 : n ≤ r := by omega
    have h2 : r < n + C.gates.length := by omega
    have hrd : ∀ c, rd n C x r c = true → rd n C y r c = true := by
      intro c hc
      unfold rd at hc ⊢
      split_ifs at hc ⊢ with hcr
      exact ih c hcr hc
    rcases (gate_inputs hg r h1 h2).1 with hop | hop
    · rw [val_and hg r h1 h2 hop] at hx ⊢
      simp only [Bool.and_eq_true] at hx ⊢
      exact ⟨hrd _ hx.1, hrd _ hx.2⟩
    · rw [val_or hg r h1 h2 hop] at hx ⊢
      simp only [Bool.or_eq_true] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (hrd _ hx)
      · exact Or.inr (hrd _ hx)

variable (n C)

def e (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def P (r : ℕ) : Finset (Fin n) := Finset.univ.filter (fun p => val n C (e n p) r = true)

def ab (S : Finset (Fin n)) (r : ℕ) : Bool :=
  if ¬ P n C r ⊆ S then true
  else if (P n C r).card ≤ 1 then false
  else
    match (gt n C r).op with
    | GateOp.and =>
      (if h : ia n C r < r then ab S (ia n C r) else false) &&
        (if h : ib n C r < r then ab S (ib n C r) else false)
    | _ =>
      (if h : ia n C r < r then ab S (ia n C r) else false) ||
        (if h : ib n C r < r then ab S (ib n C r) else false)
termination_by r

def cnt (S : Finset (Fin n)) (M : ℕ) : ℕ :=
  ((Finset.range M).filter (fun r => P n C r ⊆ S ∧ 2 ≤ (P n C r).card)).card

variable {n C}

lemma P_input (r : ℕ) (hr : r < n) : P n C r = {⟨r, hr⟩} := by
  ext p
  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [val_input n C _ r hr]
  simp [e, eq_comm]

lemma P_void (r : ℕ) (hr : n + C.gates.length ≤ r) : P n C r = ∅ := by
  ext p
  simp [P, val_void n C _ r hr]

lemma priv_range (r : ℕ) (h : 2 ≤ (P n C r).card) : n ≤ r ∧ r < n + C.gates.length := by
  constructor
  · by_contra hr
    rw [P_input r (by omega)] at h
    simp at h
  · by_contra hr
    rw [P_void r (by omega)] at h
    simp at h

lemma cnt_mono (S : Finset (Fin n)) (M : ℕ) : cnt n C S M ≤ cnt n C S (M + 1) := by
  unfold cnt
  apply Finset.card_le_card
  intro r
  simp only [Finset.mem_filter, Finset.mem_range]
  intro h
  exact ⟨by omega, h.2⟩

lemma cnt_succ (S : Finset (Fin n)) (M : ℕ) (hS : P n C M ⊆ S) (h2 : 2 ≤ (P n C M).card) :
    cnt n C S (M + 1) = cnt n C S M + 1 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert, if_pos ⟨hS, h2⟩, Finset.card_insert_of_notMem]
  simp

lemma ab_and (S : Finset (Fin n)) (r : ℕ) (hS : P n C r ⊆ S) (h2 : 2 ≤ (P n C r).card)
    (hop : (gt n C r).op = GateOp.and) :
    ab n C S r = ((if ia n C r < r then ab n C S (ia n C r) else false) &&
        (if ib n C r < r then ab n C S (ib n C r) else false)) := by
  rw [ab, if_neg (by simpa using hS), if_neg (by omega), hop]
  simp only [dite_eq_ite]

lemma ab_or (S : Finset (Fin n)) (r : ℕ) (hS : P n C r ⊆ S) (h2 : 2 ≤ (P n C r).card)
    (hop : (gt n C r).op = GateOp.or) :
    ab n C S r = ((if ia n C r < r then ab n C S (ia n C r) else false) ||
        (if ib n C r < r then ab n C S (ib n C r) else false)) := by
  rw [ab, if_neg (by simpa using hS), if_neg (by omega), hop]
  simp only [dite_eq_ite]

lemma ab_leave (S : Finset (Fin n)) (r : ℕ) (hS : ¬ P n C r ⊆ S) : ab n C S r = true := by
  rw [ab, if_pos hS]

lemma ab_tiny (S : Finset (Fin n)) (r : ℕ) (hS : P n C r ⊆ S) (h1 : (P n C r).card ≤ 1) :
    ab n C S r = false := by
  rw [ab, if_neg (by simpa using hS), if_pos h1]

lemma mem_P {r : ℕ} {p : Fin n} : p ∈ P n C r ↔ val n C (e n p) r = true := by
  simp [P]

lemma rd_true {x : Fin n → Bool} {r c : ℕ} (h : rd n C x r c = true) : c < r ∧ val n C x c = true := by
  unfold rd at h
  split_ifs at h with hc
  exact ⟨hc, h⟩

lemma lemZ (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) : ∀ M : ℕ, ∀ T : Finset ℕ, (∀ t ∈ T, t < M ∧ ab n C S t = false) →
      (T.biUnion (P n C)).card ≤ T.card + cnt n C S M := by
  intro M
  induction M with
  | zero =>
    intro T hT
    have : T = ∅ := by
      ext t
      simp only [Finset.notMem_empty, iff_false]
      intro ht
      exact absurd (hT t ht).1 (by omega)
    subst this
    simp
  | succ M ih =>
    intro T hT
    by_cases hM : M ∈ T
    · have habM := (hT M hM).2
      have hS : P n C M ⊆ S := by
        by_contra h
        rw [ab_leave S M h] at habM
        exact absurd habM (by simp)
      have hTe : ∀ t ∈ T.erase M, t < M ∧ ab n C S t = false := by
        intro t ht
        rw [Finset.mem_erase] at ht
        have := hT t ht.2
        exact ⟨by omega, this.2⟩
      have hTcard : (T.erase M).card + 1 = T.card := Finset.card_erase_add_one hM
      have hsplit : T.biUnion (P n C) = P n C M ∪ (T.erase M).biUnion (P n C) := by
        conv_lhs => rw [← Finset.insert_erase hM]
        rw [Finset.biUnion_insert]
      by_cases h1 : (P n C M).card ≤ 1
      · have := ih _ hTe
        rw [hsplit]
        have hc := cnt_mono (n := n) (C := C) S M
        calc (P n C M ∪ (T.erase M).biUnion (P n C)).card
            ≤ (P n C M).card + ((T.erase M).biUnion (P n C)).card := Finset.card_union_le _ _
          _ ≤ T.card + cnt n C S (M + 1) := by omega
      have h2 : 2 ≤ (P n C M).card := by omega
      obtain ⟨hr1, hr2⟩ := priv_range M h2
      rw [cnt_succ S M hS h2]
      rcases (gate_inputs hg M hr1 hr2).1 with hop | hop
      · rw [ab_and S M hS h2 hop] at habM
        have key : ∃ c, c < M ∧ ab n C S c = false ∧ P n C M ⊆ P n C c := by
          rcases Bool.and_eq_false_iff.1 habM with ha | ha
          · split_ifs at ha with hc
            · refine ⟨_, hc, ha, ?_⟩
              intro p hp
              rw [mem_P, val_and hg M hr1 hr2 hop] at hp
              simp only [Bool.and_eq_true] at hp
              exact mem_P.2 (rd_true hp.1).2
            · exfalso
              have : P n C M = ∅ := by
                ext p
                simp only [Finset.notMem_empty, iff_false]
                intro hp
                rw [mem_P, val_and hg M hr1 hr2 hop] at hp
                simp only [Bool.and_eq_true] at hp
                exact hc (rd_true hp.1).1
              rw [this] at h2
              simp at h2
          · split_ifs at ha with hc
            · refine ⟨_, hc, ha, ?_⟩
              intro p hp
              rw [mem_P, val_and hg M hr1 hr2 hop] at hp
              simp only [Bool.and_eq_true] at hp
              exact mem_P.2 (rd_true hp.2).2
            · exfalso
              have : P n C M = ∅ := by
                ext p
                simp only [Finset.notMem_empty, iff_false]
                intro hp
                rw [mem_P, val_and hg M hr1 hr2 hop] at hp
                simp only [Bool.and_eq_true] at hp
                exact hc (rd_true hp.2).1
              rw [this] at h2
              simp at h2
        obtain ⟨c, hc, habc, hsub⟩ := key
        have hT' : ∀ t ∈ insert c (T.erase M), t < M ∧ ab n C S t = false := by
          intro t ht
          rw [Finset.mem_insert] at ht
          rcases ht with rfl | ht
          · exact ⟨hc, habc⟩
          · exact hTe t ht
        have := ih _ hT'
        have hsub2 : T.biUnion (P n C) ⊆ (insert c (T.erase M)).biUnion (P n C) := by
          rw [hsplit, Finset.biUnion_insert]
          exact Finset.union_subset_union hsub (subset_refl _)
        have hcard := Finset.card_insert_le c (T.erase M)
        have := Finset.card_le_card hsub2
        omega
      · rw [ab_or S M hS h2 hop] at habM
        simp only [Bool.or_eq_false_iff] at habM
        obtain ⟨ha, hb⟩ := habM
        set A : Finset ℕ := (({ia n C M, ib n C M} : Finset ℕ).filter (· < M)) with hA
        have hT' : ∀ t ∈ A ∪ T.erase M, t < M ∧ ab n C S t = false := by
          intro t ht
          rw [Finset.mem_union] at ht
          rcases ht with ht | ht
          · rw [hA, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ht
            obtain ⟨rfl | rfl, hlt⟩ := ht
            · rw [if_pos hlt] at ha
              exact ⟨hlt, ha⟩
            · rw [if_pos hlt] at hb
              exact ⟨hlt, hb⟩
          · exact hTe t ht
        have := ih _ hT'
        have hsub2 : T.biUnion (P n C) ⊆ (A ∪ T.erase M).biUnion (P n C) := by
          rw [hsplit, Finset.union_biUnion]
          apply Finset.union_subset_union _ (subset_refl _)
          intro p hp
          rw [mem_P, val_or hg M hr1 hr2 hop] at hp
          simp only [Bool.or_eq_true] at hp
          rw [Finset.mem_biUnion]
          rcases hp with hp | hp
          · obtain ⟨hlt, hv⟩ := rd_true hp
            exact ⟨_, by simp [hA, hlt], mem_P.2 hv⟩
          · obtain ⟨hlt, hv⟩ := rd_true hp
            exact ⟨_, by simp [hA, hlt], mem_P.2 hv⟩
        have hAc : A.card ≤ 2 := by
          calc A.card ≤ ({ia n C M, ib n C M} : Finset ℕ).card := Finset.card_filter_le _ _
            _ ≤ 2 := Finset.card_le_two
        have hcard := Finset.card_union_le A (T.erase M)
        have := Finset.card_le_card hsub2
        omega
    · have hT' : ∀ t ∈ T, t < M ∧ ab n C S t = false := by
        intro t ht
        have := hT t ht
        refine ⟨?_, this.2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 this.1 with h | h
        · exact h
        · exact absurd (h ▸ ht) hM
      have := ih T hT'
      have := cnt_mono (n := n) (C := C) S M
      omega

lemma lemW (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) : ∀ M : ℕ, ∀ T : Finset ℕ, (∀ t ∈ T, t < M ∧ ab n C S t = true) →
      ∃ X : Finset (Fin n), (∀ q ∈ X, q ∉ S) ∧ X.card ≤ T.card + cnt n C S M ∧
        ∀ y : Fin n → Bool, (∀ q ∈ X, y q = true) → ∀ t ∈ T, val n C y t = true := by
  intro M
  induction M with
  | zero =>
    intro T hT
    refine ⟨∅, by simp, by simp, ?_⟩
    intro y _ t ht
    exact absurd (hT t ht).1 (by omega)
  | succ M ih =>
    intro T hT
    by_cases hM : M ∈ T
    · have habM := (hT M hM).2
      have hTe : ∀ t ∈ T.erase M, t < M ∧ ab n C S t = true := by
        intro t ht
        rw [Finset.mem_erase] at ht
        have := hT t ht.2
        exact ⟨by omega, this.2⟩
      have hTcard : (T.erase M).card + 1 = T.card := Finset.card_erase_add_one hM
      by_cases hS : P n C M ⊆ S
      · have h2 : 2 ≤ (P n C M).card := by
          by_contra h
          rw [ab_tiny S M hS (by omega)] at habM
          exact absurd habM (by simp)
        obtain ⟨hr1, hr2⟩ := priv_range M h2
        rw [cnt_succ S M hS h2]
        rcases (gate_inputs hg M hr1 hr2).1 with hop | hop
        · rw [ab_and S M hS h2 hop] at habM
          simp only [Bool.and_eq_true] at habM
          obtain ⟨ha, hb⟩ := habM
          split_ifs at ha with hca
          split_ifs at hb with hcb
          have hT' : ∀ t ∈ insert (ia n C M) (insert (ib n C M) (T.erase M)),
              t < M ∧ ab n C S t = true := by
            intro t ht
            simp only [Finset.mem_insert] at ht
            rcases ht with rfl | rfl | ht
            · exact ⟨hca, ha⟩
            · exact ⟨hcb, hb⟩
            · exact hTe t ht
          obtain ⟨X, hX1, hX2, hX3⟩ := ih _ hT'
          refine ⟨X, hX1, ?_, ?_⟩
          · have h1 := Finset.card_insert_le (ia n C M) (insert (ib n C M) (T.erase M))
            have h2 := Finset.card_insert_le (ib n C M) (T.erase M)
            omega
          · intro y hy t ht
            by_cases htM : t = M
            · subst htM
              rw [val_and hg _ hr1 hr2 hop]
              simp only [rd, if_pos hca, if_pos hcb, Bool.and_eq_true]
              exact ⟨hX3 y hy _ (by simp), hX3 y hy _ (by simp)⟩
            · exact hX3 y hy t (by simp [Finset.mem_erase, htM, ht])
        · rw [ab_or S M hS h2 hop] at habM
          have key : ∃ c, c < M ∧ ab n C S c = true ∧
              ∀ y : Fin n → Bool, val n C y c = true → val n C y M = true := by
            simp only [Bool.or_eq_true] at habM
            rcases habM with ha | ha
            · split_ifs at ha with hc
              refine ⟨_, hc, ha, fun y hy => ?_⟩
              rw [val_or hg _ hr1 hr2 hop]
              simp [rd, hc, hy]
            · split_ifs at ha with hc
              refine ⟨_, hc, ha, fun y hy => ?_⟩
              rw [val_or hg _ hr1 hr2 hop]
              simp [rd, hc, hy]
          obtain ⟨c, hc, habc, hcM⟩ := key
          have hT' : ∀ t ∈ insert c (T.erase M), t < M ∧ ab n C S t = true := by
            intro t ht
            rw [Finset.mem_insert] at ht
            rcases ht with rfl | ht
            · exact ⟨hc, habc⟩
            · exact hTe t ht
          obtain ⟨X, hX1, hX2, hX3⟩ := ih _ hT'
          refine ⟨X, hX1, ?_, ?_⟩
          · have h1 := Finset.card_insert_le c (T.erase M)
            omega
          · intro y hy t ht
            by_cases htM : t = M
            · subst htM
              exact hcM y (hX3 y hy c (by simp))
            · exact hX3 y hy t (by simp [Finset.mem_erase, htM, ht])
      · obtain ⟨p, hpP, hpS⟩ := Finset.not_subset.1 hS
        obtain ⟨X, hX1, hX2, hX3⟩ := ih _ hTe
        refine ⟨insert p X, ?_, ?_, ?_⟩
        · intro q hq
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact hpS
          · exact hX1 q hq
        · have := Finset.card_insert_le p X
          have := cnt_mono (n := n) (C := C) S M
          omega
        · intro y hy t ht
          by_cases htM : t = M
          · subst htM
            apply val_mono hg (e n p) y _ t (mem_P.1 hpP)
            intro q hq
            simp only [e, decide_eq_true_eq] at hq
            subst hq
            exact hy _ (by simp)
          · exact hX3 y (fun q hq => hy q (by simp [hq])) t
              (by simp [Finset.mem_erase, htM, ht])
    · have hT' : ∀ t ∈ T, t < M ∧ ab n C S t = true := by
        intro t ht
        have := hT t ht
        refine ⟨?_, this.2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 this.1 with h | h
        · exact h
        · exact absurd (h ▸ ht) hM
      obtain ⟨X, hX1, hX2, hX3⟩ := ih T hT'
      have := cnt_mono (n := n) (C := C) S M
      exact ⟨X, hX1, by omega, hX3⟩

lemma one_output (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (k : ℕ) (S : Finset (Fin n)) (o c : ℕ)
    (hout : ∀ p : Fin n, val n C (e n p) o = true ↔ p ∈ S)
    (hk : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val n C x o = false)
    (hck : c ≤ k) (hcS : c + 1 ≤ S.card) : c ≤ cnt n C S (o + 1) := by
  have hPo : P n C o = S := by
    ext p
    rw [mem_P]
    exact hout p
  cases hab : ab n C S o
  · have := lemZ hg S (o + 1) {o} (by simp [hab])
    simp only [Finset.singleton_biUnion, Finset.card_singleton, hPo] at this
    omega
  · by_contra hlt
    obtain ⟨X, hX1, hX2, hX3⟩ := lemW hg S (o + 1) {o} (by simp [hab])
    simp only [Finset.card_singleton] at hX2
    have hy := hX3 (fun q => decide (q ∈ X)) (by simp) o (by simp)
    have hfalse := hk (fun q => decide (q ∈ X)) (by
        have : (Finset.univ.filter (fun q : Fin n => decide (q ∈ X) = true)) = X := by
          ext q
          simp
        rw [this]
        omega) (by
        intro q hq
        simp only [decide_eq_false_iff_not]
        intro hqX
        exact hX1 q hqX hq)
    rw [hy] at hfalse
    exact absurd hfalse (by simp)

lemma cnt_le (S : Finset (Fin n)) (M : ℕ) :
    cnt n C S M ≤ ((Finset.range (n + C.gates.length)).filter
      (fun r => P n C r ⊆ S ∧ 2 ≤ (P n C r).card)).card := by
  unfold cnt
  apply Finset.card_le_card
  intro r
  simp only [Finset.mem_filter, Finset.mem_range]
  intro h
  exact ⟨(priv_range r h.2.2).2, h.2⟩

end Main

end PEqualNP.Outside.L_meta_270

open PEqualNP.Outside.L_meta_270

theorem PEqualNP.Outside.L_meta_270 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS2 _ hg hout hk hck hcS
  have hQ : ∀ i, c i ≤ ((Finset.range (n + C.gates.length)).filter
      (fun r => P n C r ⊆ S i ∧ 2 ≤ (P n C r).card)).card := by
    intro i
    exact le_trans (one_output hg k (S i) (o i) (c i) (hout i) (hk i) (hck i) (hcS i))
      (cnt_le (S i) (o i + 1))
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
      Disjoint ((Finset.range (n + C.gates.length)).filter
        (fun r => P n C r ⊆ S i ∧ 2 ≤ (P n C r).card))
        ((Finset.range (n + C.gates.length)).filter
        (fun r => P n C r ⊆ S j ∧ 2 ≤ (P n C r).card)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro r hri hrj
    rw [Finset.mem_filter] at hri hrj
    have hsub : P n C r ⊆ S i ∩ S j := Finset.subset_inter hri.2.1 hrj.2.1
    have := Finset.card_le_card hsub
    have := hS2 i j hij
    omega
  calc ∑ i : Fin m, c i
      ≤ ∑ i : Fin m, ((Finset.range (n + C.gates.length)).filter
          (fun r => P n C r ⊆ S i ∧ 2 ≤ (P n C r).card)).card := Finset.sum_le_sum (fun i _ => hQ i)
    _ = (Finset.univ.biUnion (fun i : Fin m => (Finset.range (n + C.gates.length)).filter
          (fun r => P n C r ⊆ S i ∧ 2 ≤ (P n C r).card))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := by
        apply Finset.card_le_card
        intro r hr
        rw [Finset.mem_biUnion] at hr
        obtain ⟨i, _, hr⟩ := hr
        rw [Finset.mem_filter] at hr
        have := priv_range (C := C) r hr.2.2
        rw [Finset.mem_Ico]
        exact this
    _ = C.size := by simp [Circuit.size]
