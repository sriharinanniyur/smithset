import Mathlib

open Finset

variable {n : ℕ}

def Asymmetric (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ i j, i ≠ j → M i j + M j i ≤ 1

def Dominating (M : Matrix (Fin n) (Fin n) ℕ) (D : Finset (Fin n)) : Prop :=
  ∀ a ∈ D, ∀ b ∉ D, M a b = 1

def IsSmithSet (M : Matrix (Fin n) (Fin n) ℕ) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ Dominating M S ∧ ∀ D, D.Nonempty → Dominating M D → S ⊆ D

def SmithCriterion {P : Type} (pairwise : P → Matrix (Fin n) (Fin n) ℕ) (f : P → Fin n) : Prop :=
  ∀ p S, IsSmithSet (pairwise p) S → f p ∈ S

def smithSet (n : ℕ) (M : Matrix (Fin n) (Fin n) ℕ) : Finset (Fin n) := Id.run do
  let mut A : List (Fin n × ℕ) := []
  for i in List.finRange n do
    let mut s := 0
    for j in List.finRange n do
      if j ≠ i then
        if M i j = 1 then
          s := s + 2
        else if M j i = 0 then
          s := s + 1
    A := A ++ [(i, s)]
  A := A.mergeSort (fun a b => a.2 ≥ b.2)
  let mut S : List (Fin n × ℕ) := []
  for a in A do
    let mut total := 0
    for b in S do
      total := total + b.2
    let k := S.length
    if S ≠ [] ∧ total = 2 * (k.choose 2 + k * (n - k)) then
      break
    S := a :: S
  return (S.map Prod.fst).toFinset

#eval smithSet 4 !![0, 1, 0, 1;
                    0, 0, 1, 1;
                    1, 0, 0, 1;
                    0, 0, 0, 0]

#eval smithSet 4 !![0, 1, 0, 1;
                    0, 0, 0, 1;
                    1, 1, 0, 1;
                    0, 0, 0, 0]

#eval smithSet 3 !![0, 0, 1;
                    0, 0, 1;
                    0, 0, 0]

#eval smithSet 4 !![0, 0, 1, 1;
                    0, 0, 0, 1;
                    0, 0, 0, 1;
                    0, 0, 0, 0]

namespace Smith

variable {M : Matrix (Fin n) (Fin n) ℕ}

def w (M : Matrix (Fin n) (Fin n) ℕ) (i j : Fin n) : ℕ :=
  if M i j = 1 then 2 else if M j i = 0 then 1 else 0

def score (M : Matrix (Fin n) (Fin n) ℕ) (i : Fin n) : ℕ := ∑ j, if j ≠ i then w M i j else 0

def pick (n : ℕ) : List (Fin n × ℕ) → List (Fin n × ℕ) → List (Fin n × ℕ)
  | [], S => S
  | a :: rest, S =>
    if S ≠ [] ∧ List.foldl (fun b a => b + a.2) 0 S = 2 * (S.length.choose 2 + S.length * (n - S.length))
    then S else pick n rest (a :: S)

def sortedList (M : Matrix (Fin n) (Fin n) ℕ) : List (Fin n × ℕ) :=
  ((List.finRange n).map fun i => (i, score M i)).mergeSort (fun a b => a.2 ≥ b.2)

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (x y : β) :
    (if c then (pure (ForInStep.yield x) : Id (ForInStep β)) else pure (ForInStep.yield y)) =
      pure (ForInStep.yield (if c then x else y)) := by
  split <;> rfl

theorem forIn_eq_pick (L S : List (Fin n × ℕ)) :
    (forIn L S fun a S =>
      if S ≠ [] ∧ List.foldl (fun b a => b + a.2) 0 S = 2 * (S.length.choose 2 + S.length * (n - S.length))
      then (pure (ForInStep.done S) : Id _) else pure (ForInStep.yield (a :: S))) = pure (pick n L S) := by
  induction L generalizing S with
  | nil => simp [pick]
  | cons a rest ih =>
    rw [List.forIn_cons]
    split_ifs with h <;> simp [pick, h, ih]

theorem foldl_append_singleton {α β : Type} (g : α → β) (l : List α) (acc : List β) :
    l.foldl (fun A i => A ++ [g i]) acc = acc ++ l.map g := by
  induction l generalizing acc <;> simp [*]

theorem foldl_score (M : Matrix (Fin n) (Fin n) ℕ) (i : Fin n) :
    List.foldl (fun s j => if j ≠ i then if M i j = 1 then s + 2 else if M j i = 0 then s + 1 else s else s)
      0 (List.finRange n) = score M i := by
  have : (fun s j => if j ≠ i then if M i j = 1 then s + 2 else if M j i = 0 then s + 1 else s else s) =
      fun s (j : Fin n) => s + (if j ≠ i then w M i j else 0) := by
    funext s j; simp only [w]; split_ifs <;> omega
  rw [this, score, Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]

theorem smithSet_eq (M : Matrix (Fin n) (Fin n) ℕ) :
    smithSet n M = ((pick n (sortedList M) []).map Prod.fst).toFinset := by
  simp only [smithSet, Id.run, bind_pure_comp, pure_bind, ite_pure_yield, List.forIn_pure_yield_eq_foldl,
    map_pure, foldl_score, foldl_append_singleton, forIn_eq_pick, List.nil_append]
  rfl

theorem w_le_two (i j : Fin n) : w M i j ≤ 2 := by
  unfold w; split_ifs <;> omega

theorem w_eq_two (i j : Fin n) : w M i j = 2 ↔ M i j = 1 := by
  unfold w; split_ifs <;> simp_all

theorem w_add_w (hM : Asymmetric M) {i j : Fin n} (h : i ≠ j) : w M i j + w M j i = 2 := by
  have := hM i j h
  unfold w; split_ifs <;> omega

theorem w_eq_zero (hM : Asymmetric M) {i j : Fin n} (h : i ≠ j) (hji : M j i = 1) : w M i j = 0 := by
  have := hM i j h
  unfold w; split_ifs <;> omega

theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  rw [Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)]

theorem sum_score_split (S : Finset (Fin n)) :
    ∑ a ∈ S, score M a =
      ∑ a ∈ S, ∑ b ∈ S, (if b ≠ a then w M a b else 0) + ∑ a ∈ S, ∑ b ∈ Sᶜ, w M a b := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [score, ← Finset.sum_add_sum_compl S]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  rw [ite_eq_left]
  rintro rfl
  exact (Finset.mem_compl.1 hb) ha

theorem sum_within (hM : Asymmetric M) (S : Finset (Fin n)) :
    ∑ a ∈ S, ∑ b ∈ S, (if b ≠ a then w M a b else 0) = 2 * S.card.choose 2 := by
  set W := ∑ a ∈ S, ∑ b ∈ S, (if b ≠ a then w M a b else 0) with hW
  have hswap : W = ∑ a ∈ S, ∑ b ∈ S, (if b ≠ a then w M b a else 0) := by
    rw [hW, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
    simp only [ne_comm]
  have h2 : W + W = 2 * (S.card * (S.card - 1)) := by
    calc W + W = ∑ a ∈ S, ∑ b ∈ S, ((if b ≠ a then w M a b else 0) + (if b ≠ a then w M b a else 0)) := by
          simp only [Finset.sum_add_distrib]; rw [← hW, ← hswap]
      _ = ∑ a ∈ S, ∑ b ∈ S, (if b ≠ a then 2 else 0) := by
          apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
          split_ifs with h
          · exact w_add_w hM (Ne.symm h)
          · rfl
      _ = ∑ a ∈ S, 2 * (S.card - 1) := by
          apply Finset.sum_congr rfl; intro a ha
          simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem ha, mul_comm]
      _ = 2 * (S.card * (S.card - 1)) := by rw [Finset.sum_const, smul_eq_mul]; ring
  rw [two_mul_choose_two]
  omega

theorem sum_outside_eq_iff (S : Finset (Fin n)) :
    ∑ a ∈ S, ∑ b ∈ Sᶜ, w M a b = 2 * (S.card * (n - S.card)) ↔ Dominating M S := by
  have hc : 2 * (S.card * (n - S.card)) = ∑ a ∈ S, ∑ b ∈ Sᶜ, (2 : ℕ) := by
    simp [Finset.card_compl]; ring
  rw [hc, Finset.sum_eq_sum_iff_of_le (fun a _ => Finset.sum_le_sum fun b _ => w_le_two a b)]
  unfold Dominating
  apply forall₂_congr; intro a _
  rw [Finset.sum_eq_sum_iff_of_le (fun b _ => w_le_two a b)]
  simp [w_eq_two]

theorem cond_iff (hM : Asymmetric M) (S : Finset (Fin n)) :
    ∑ a ∈ S, score M a = 2 * (S.card.choose 2 + S.card * (n - S.card)) ↔ Dominating M S := by
  rw [sum_score_split, sum_within hM, mul_add, add_right_inj, sum_outside_eq_iff]

theorem score_lt (hM : Asymmetric M) {D : Finset (Fin n)} (hD : Dominating M D) {a b : Fin n}
    (ha : a ∈ D) (hb : b ∉ D) : score M b < score M a := by
  have hbc : b ∈ Dᶜ := Finset.mem_compl.2 hb
  have h1 : 2 * Dᶜ.card ≤ score M a := by
    calc 2 * Dᶜ.card = ∑ c ∈ Dᶜ, (if c ≠ a then w M a c else 0) := by
          rw [Finset.card_eq_sum_ones, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro c hc
          have hc' := Finset.mem_compl.1 hc
          have hca : c ≠ a := fun h => hc' (h ▸ ha)
          rw [ite_eq_left hca, (w_eq_two a c).2 (hD a ha c hc')]
          rfl
      _ ≤ ∑ c ∈ D, (if c ≠ a then w M a c else 0) + ∑ c ∈ Dᶜ, (if c ≠ a then w M a c else 0) :=
          Nat.le_add_left _ _
      _ = score M a := by rw [score, Finset.sum_add_sum_compl]
  have h2 : score M b ≤ 2 * (Dᶜ.card - 1) := by
    calc score M b = ∑ c ∈ D, (if c ≠ b then w M b c else 0) + ∑ c ∈ Dᶜ, (if c ≠ b then w M b c else 0) := by
          rw [score, Finset.sum_add_sum_compl]
      _ = ∑ c ∈ Dᶜ, (if c ≠ b then w M b c else 0) := by
          rw [Finset.sum_eq_zero, zero_add]
          intro c hc
          have hcb : c ≠ b := fun h => hb (h ▸ hc)
          rw [ite_eq_left hcb, w_eq_zero hM (Ne.symm hcb) (hD c hc b hb)]
      _ ≤ ∑ c ∈ Dᶜ, (if c ≠ b then 2 else 0) := by
          apply Finset.sum_le_sum; intro c _
          split_ifs with h
          · exact w_le_two b c
          · exact le_rfl
      _ = 2 * (Dᶜ.card - 1) := by
          simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem hbc, mul_comm]
  have h3 : 0 < Dᶜ.card := Finset.card_pos.2 ⟨b, hbc⟩
  omega

theorem sortedList_perm :
    (sortedList M).Perm ((List.finRange n).map fun i => (i, score M i)) :=
  List.mergeSort_perm _ _

theorem sortedList_sorted : (sortedList M).Pairwise (fun a b => b.2 ≤ a.2) := by
  have := List.pairwise_mergeSort (le := fun a b : Fin n × ℕ => decide (a.2 ≥ b.2))
    (by intros; simp_all; omega) (by intros; simp; omega)
    ((List.finRange n).map fun i => (i, score M i))
  unfold sortedList
  exact this.imp fun h => by simpa using h

theorem sortedList_score {p : Fin n × ℕ} (hp : p ∈ sortedList M) : p.2 = score M p.1 := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 (sortedList_perm.mem_iff.1 hp)
  rfl

theorem sortedList_mem (i : Fin n) : (i, score M i) ∈ sortedList M :=
  sortedList_perm.mem_iff.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

theorem sortedList_nodup : ((sortedList M).map Prod.fst).Nodup := by
  rw [(sortedList_perm.map Prod.fst).nodup_iff]
  simp [List.map_map, Function.comp_def, List.nodup_finRange]

theorem sortedList_length : (sortedList M).length = n := by
  rw [sortedList_perm.length_eq]; simp

theorem pick_ne_nil (rest : List (Fin n × ℕ)) {S : List (Fin n × ℕ)} (hS : S ≠ []) :
    pick n rest S ≠ [] := by
  induction rest generalizing S with
  | nil => simpa [pick]
  | cons a rest ih =>
    simp only [pick]
    split_ifs
    · exact hS
    · exact ih (List.cons_ne_nil a S)

theorem foldl_eq_sum (S : List (Fin n × ℕ)) :
    List.foldl (fun b a => b + a.2) 0 S = (S.map Prod.snd).sum := by
  rw [List.sum_eq_foldl, List.foldl_map]

theorem prefix_facts {S rest : List (Fin n × ℕ)} (h : S.reverse ++ rest = sortedList M) :
    (S.map Prod.fst).Nodup ∧ (∀ p ∈ S, p.2 = score M p.1) := by
  constructor
  · have := sortedList_nodup (M := M)
    rw [← h] at this
    simp [List.nodup_append] at this
    exact this.1
  · intro p hp
    apply sortedList_score
    rw [← h]
    simp [hp]

theorem cond_iff_list (hM : Asymmetric M) {S rest : List (Fin n × ℕ)}
    (h : S.reverse ++ rest = sortedList M) :
    (S ≠ [] ∧ List.foldl (fun b a => b + a.2) 0 S = 2 * (S.length.choose 2 + S.length * (n - S.length))) ↔
      (S ≠ [] ∧ Dominating M (S.map Prod.fst).toFinset) := by
  obtain ⟨hnd, hsc⟩ := prefix_facts h
  rw [← cond_iff hM, List.sum_toFinset _ hnd, List.toFinset_card_of_nodup hnd, List.length_map,
    foldl_eq_sum, List.map_map]
  have : S.map Prod.snd = S.map (score M ∘ Prod.fst) := List.map_congr_left fun p hp => hsc p hp
  rw [this]

theorem pick_spec (hM : Asymmetric M) :
    ∀ (rest S : List (Fin n × ℕ)), S.reverse ++ rest = sortedList M →
      (∀ D, D.Nonempty → Dominating M D → (S.map Prod.fst).toFinset ⊆ D) →
      (∀ D, D.Nonempty → Dominating M D → ((pick n rest S).map Prod.fst).toFinset ⊆ D) ∧
        Dominating M ((pick n rest S).map Prod.fst).toFinset := by
  intro rest
  induction rest with
  | nil =>
    intro S h hinv
    simp only [pick]
    refine ⟨hinv, ?_⟩
    intro a _ b hb
    exfalso
    apply hb
    have := sortedList_mem (M := M) b
    rw [← h] at this
    simp at this ⊢
    exact ⟨_, this⟩
  | cons a rest ih =>
    intro S h hinv
    simp only [pick]
    split_ifs with hc
    · exact ⟨hinv, ((cond_iff_list hM h).1 hc).2⟩
    · apply ih
      · rw [← h]; simp
      · intro D hD hdom
        have hSD := hinv D hD hdom
        simp only [List.map_cons, List.toFinset_cons, Finset.insert_subset_iff]
        refine ⟨?_, hSD⟩
        have hne : (S.map Prod.fst).toFinset ≠ D := by
          intro heq
          apply hc
          rw [cond_iff_list hM h]
          refine ⟨?_, heq ▸ hdom⟩
          rintro rfl
          simp at heq
          exact hD.ne_empty heq.symm
        obtain ⟨d, hdD, hdS⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hSD hne)
        have hd : (d, score M d) ∈ S.reverse ++ a :: rest := by rw [h]; exact sortedList_mem d
        simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hd
        rcases hd with hd | hd | hd
        · exact absurd (by simpa using List.mem_map_of_mem (f := Prod.fst) hd) hdS
        · exact hd ▸ hdD
        · by_contra haD
          have hsorted := sortedList_sorted (M := M)
          rw [← h, List.pairwise_append] at hsorted
          have hle := (List.pairwise_cons.1 hsorted.2.1).1 _ hd
          have ha2 : a.2 = score M a.1 := sortedList_score (by rw [← h]; simp)
          have := score_lt hM hdom hdD haD
          simp at hle
          omega

end Smith

theorem smithSet_correct (n : ℕ) (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℕ)
    (hM : Asymmetric M) : IsSmithSet M (smithSet n M) := by
  rw [Smith.smithSet_eq]
  obtain ⟨hmin, hdom⟩ := Smith.pick_spec hM (Smith.sortedList M) [] (by simp) (by simp)
  refine ⟨?_, hdom, hmin⟩
  rw [List.toFinset_nonempty_iff]
  obtain ⟨a, rest, hL⟩ : ∃ a rest, Smith.sortedList M = a :: rest := by
    cases hL : Smith.sortedList M with
    | nil => have := Smith.sortedList_length (M := M); rw [hL] at this; simp at this; omega
    | cons a rest => exact ⟨a, rest, rfl⟩
  rw [hL]
  simp only [Smith.pick, ne_eq, not_true_eq_false, false_and, ite_false, List.map_eq_nil_iff]
  exact Smith.pick_ne_nil rest (List.cons_ne_nil a [])
