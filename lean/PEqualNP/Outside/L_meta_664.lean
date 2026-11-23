import Mathlib

namespace PEqualNP.Outside.L_meta_664

open Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

def Qf (b : F) (x : F × F) : F := x.1 ^ 2 + b * x.1 * x.2 + x.2 ^ 2

def lineHom (a c : F) : F →+ F where
  toFun t := a * t ^ 2 + c * t
  map_zero' := by ring
  map_add' x y := by
    rw [CharTwo.add_sq]
    ring

lemma lineHom_apply (a c t : F) : lineHom a c t = a * t ^ 2 + c * t := rfl

lemma expand (b t : F) (p d : F × F) :
    Qf b (p + t • d) = Qf b p + lineHom (Qf b d) (b * (p.1 * d.2 + p.2 * d.1)) t := by
  simp only [Qf, lineHom_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  linear_combination (p.1 * t * d.1 + p.2 * t * d.2) * (CharTwo.two_eq_zero : (2 : F) = 0)

lemma aniso (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (x : F × F) (h : Qf b x = 0) :
    x = 0 := by
  simp only [Qf] at h
  by_cases h2 : x.2 = 0
  · rw [h2] at h
    have h1 : x.1 = 0 := by simpa using h
    exact Prod.ext h1 h2
  · exfalso
    apply hb (x.1 / x.2)
    have e : (x.1 / x.2) ^ 2 + b * (x.1 / x.2) + 1
        = (x.1 ^ 2 + b * x.1 * x.2 + x.2 ^ 2) / x.2 ^ 2 := by
      field_simp
    rw [e, h, zero_div]

lemma ker_iff (a c t : F) (ha : a ≠ 0) : lineHom a c t = 0 ↔ t = 0 ∨ t = c / a := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [lineHom_apply]
  constructor
  · intro h
    have h' : t * (a * t + c) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact Or.inl h0
    · right
      rw [eq_div_iff ha]
      linear_combination h0 - c * two
  · rintro (rfl | rfl)
    · ring
    · field_simp
      linear_combination c ^ 2 * two

lemma card_ker (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) : Nat.card (lineHom a c).ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨0, by simp⟩, ⟨c / a, (ker_iff a c _ ha).2 (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    have h' := congrArg Subtype.val h
    simp only at h'
    exact hc (by rw [eq_comm, div_eq_zero_iff] at h'; tauto)
  · ext ⟨t, ht⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (ker_iff a c t ha).1 ht with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

lemma card_comap_eq {G : Type} [AddCommGroup G] [Finite G] (f : G →+ G)
    (A : AddSubgroup G) (hk : Nat.card f.ker = 2) (α : G) (hα : α ∈ A)
    (hαR : α ∉ f.range) : Nat.card (A.comap f) = Nat.card A := by
  have h1 := AddSubgroup.card_ker_mul_card_range f
  rw [hk] at h1
  have h2 := AddSubgroup.card_mul_index f.range
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hR : f.range.index = 2 := by
    have : Nat.card f.range * f.range.index = Nat.card f.range * 2 := by omega
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h3 : f.range.relIndex A = 2 := by
    rw [AddSubgroup.relIndex_eq_two_iff]
    refine ⟨α, hα, fun b _ => ?_⟩
    rw [AddSubgroup.add_mem_iff_of_index_two hR]
    by_cases hb : b ∈ f.range <;> simp [hb, hαR]
  have h4 := AddSubgroup.relIndex_mul_card (H := f.range) (K := A)
  have h5 := AddSubgroup.relIndex_mul_card (H := A) (K := f.range)
  have h6 := AddSubgroup.card_mul_index (A.comap f)
  rw [AddSubgroup.index_comap] at h6
  rw [h3, inf_comm] at h4
  have hr : A.relIndex f.range ≠ 0 := by
    intro h0
    rw [h0] at h5
    omega
  have : Nat.card (A.comap f) * A.relIndex f.range
      = (2 * Nat.card (A ⊓ f.range :)) * A.relIndex f.range := by
    rw [h6, ← h1, ← h5]
    ring
  rw [← h4]
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr) this

lemma card_filter_comap (f : F →+ F) (A : AddSubgroup F) [DecidablePred (· ∈ A)] :
    (univ.filter fun t => f t ∈ A).card = Nat.card (A.comap f) := by
  have e : Nat.card (A.comap f) = Nat.card {t // f t ∈ A} := rfl
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma card_filter_shift (f : F →+ F) (q t0 : F) (A : AddSubgroup F) [DecidablePred (· ∈ A)]
    (ht0 : q + f t0 ∈ A) :
    (univ.filter fun t => q + f t ∈ A).card = (univ.filter fun t => f t ∈ A).card := by
  have key : ∀ t, q + f t ∈ A ↔ f (t - t0) ∈ A := by
    intro t
    have e : q + f t = (q + f t0) + f (t - t0) := by rw [map_sub]; ring
    rw [e, AddSubgroup.add_mem_cancel_left A ht0]
  refine Finset.card_nbij' (fun t => t - t0) (fun t => t + t0) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht ⊢
    exact (key t).1 ht
  · intro t ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht ⊢
    rw [key, add_sub_cancel_right]
    exact ht
  · intro t _
    simp
  · intro t _
    simp

lemma main (b : F) (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (A : AddSubgroup F)
    [DecidablePred (· ∈ A)] (p d : F × F) (hd : d ≠ 0) :
    ((univ.filter fun t : F => Qf b (p + t • d) ∈ A).card = 0 ∨
      (univ.filter fun t : F => Qf b (p + t • d) ∈ A).card = Nat.card A) ∧
    (p = 0 → (univ.filter fun t : F => Qf b (p + t • d) ∈ A).card = Nat.card A) := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  set a := Qf b d with ha_def
  set c := b * (p.1 * d.2 + p.2 * d.1) with hc_def
  have ha : a ≠ 0 := fun h => hd (aniso b hb d h)
  set f := lineHom a c with hf_def
  have hS : (univ.filter fun t : F => Qf b (p + t • d) ∈ A)
      = univ.filter fun t => Qf b p + f t ∈ A := by
    apply Finset.filter_congr
    intro t _
    rw [expand]
  rw [hS]
  by_cases hc : c = 0
  · have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro t ht
      rw [hf_def, lineHom_apply, hc, zero_mul, add_zero] at ht
      rcases mul_eq_zero.1 ht with h | h
      · exact absurd h ha
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
    obtain ⟨t0, ht0⟩ := hbij.2 (Qf b p)
    have hmem : Qf b p + f t0 ∈ A := by
      rw [ht0, CharTwo.add_self_eq_zero]
      exact A.zero_mem
    have key : (univ.filter fun t => Qf b p + f t ∈ A).card = Nat.card A := by
      rw [card_filter_shift f _ t0 A hmem, card_filter_comap]
      exact Nat.card_congr ((Equiv.ofBijective f hbij).subtypeEquiv fun t => Iff.rfl)
    exact ⟨Or.inr key, fun _ => key⟩
  · have hp : p ≠ 0 := by
      rintro rfl
      apply hc
      simp [c]
    refine ⟨?_, fun h => absurd h hp⟩
    by_cases hne : ∃ t0, Qf b p + f t0 ∈ A
    · right
      obtain ⟨t0, ht0⟩ := hne
      rw [card_filter_shift f _ t0 A ht0, card_filter_comap]
      have hout : ∃ α ∈ A, α ∉ f.range := by
        by_contra hall
        push_neg at hall
        obtain ⟨t1, ht1⟩ := hall _ ht0
        have hq : Qf b (p + (t1 + t0) • d) = 0 := by
          rw [expand, ← hf_def, map_add, ht1]
          linear_combination (Qf b p + f t0) * two
        have hz := aniso b hb _ hq
        apply hc
        have e1 : p.1 = -((t1 + t0) * d.1) := by
          have := congrArg Prod.fst hz
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero] at this
          linear_combination this
        have e2 : p.2 = -((t1 + t0) * d.2) := by
          have := congrArg Prod.snd hz
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero] at this
          linear_combination this
        rw [hc_def, e1, e2]
        linear_combination (-(b * (t1 + t0) * d.1 * d.2)) * two
      obtain ⟨α, hα, hαR⟩ := hout
      exact card_comap_eq f A (card_ker a c ha hc) α hα hαR
    · left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _ ht
      exact hne ⟨t, ht⟩

end PEqualNP.Outside.L_meta_664

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  exact PEqualNP.Outside.L_meta_664.main b hb A p d hd
