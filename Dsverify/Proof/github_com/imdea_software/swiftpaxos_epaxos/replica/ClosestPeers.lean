/-
`ComputeClosestPeers` and `UpdatePreferredPeerOrder`: beacons to the live peers, the latencies'
ranking (`quorumOf`), the new preferred order (`updOrder`: the quorum without the own id, then
the own id), read-only from then on.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Beacon

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure facts: the ranking and the new order -/

/-- The ids `0..4` as `int32`s. -/
def R5 : List w32 := (List.range 5).map (fun j : Nat => W32 (j : Int))

theorem R5_nodup : R5.Nodup := by decide

theorem R5_length : R5.length = 5 := by decide

theorem mem_R5 (x : w32) : x ∈ R5 ↔ ∃ j : Nat, j < 5 ∧ x = W32 (j : Int) := by
  unfold R5
  rw [List.mem_map]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, List.mem_range.mp hj, h.symm⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, List.mem_range.mpr hj, h.symm⟩

/-- `j` comes before `i` in the latencies' order (`ComputeClosestPeers`'s test). -/
def lbefore (ls : List w64) (j i : Nat) : Bool :=
  decide (sint.Z (ls.getD j (W64 0)) < sint.Z (ls.getD i (W64 0))) ||
    (decide (ls.getD j (W64 0) = ls.getD i (W64 0)) && decide (j < i))

/-- `i`'s position: the ids before it. -/
def lrank (ls : List w64) (i : Nat) : Nat := (List.range 5).countP (fun j => lbefore ls j i)

/-- The quorum array after the ranking loop over the first `n` ids. -/
def quorumN (ls : List w64) (n : Nat) : List w32 :=
  (List.range n).foldl (fun q i => q.set (lrank ls i) (W32 (i : Int))) (List.replicate 5 (W32 0))

def quorumOf (ls : List w64) : List w32 := quorumN ls 5

theorem lbefore_irrefl (ls : List w64) (i : Nat) : lbefore ls i i = false := by
  unfold lbefore; simp

theorem lbefore_trans (ls : List w64) (j i k : Nat) (h1 : lbefore ls j i = true)
    (h2 : lbefore ls i k = true) : lbefore ls j k = true := by
  unfold lbefore at *
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; omega
  · left; rw [← h2]; exact h1
  · left; rw [h1]; exact h2
  · right; exact ⟨h1.trans h2, by omega⟩

theorem lbefore_total (ls : List w64) (i k : Nat) (h : i ≠ k) :
    lbefore ls i k = true ∨ lbefore ls k i = true := by
  unfold lbefore
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  by_cases he : ls.getD i (W64 0) = ls.getD k (W64 0)
  · rcases Nat.lt_or_gt_of_ne h with hik | hik
    · left; right; exact ⟨he, hik⟩
    · right; right; exact ⟨he.symm, hik⟩
  · have : sint.Z (ls.getD i (W64 0)) ≠ sint.Z (ls.getD k (W64 0)) := by
      intro h'; exact he (BitVec.toInt_inj.mp h')
    rcases Int.lt_or_gt_of_ne this with h' | h'
    · left; left; exact h'
    · right; left; exact h'

theorem countP_lt_of_mono {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
      l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | a :: l, hm, ⟨x, hx, hq, hp⟩ => by
    simp only [List.countP_cons]
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left (fun y hy hpy => hm y (List.mem_cons_of_mem a hy) hpy)
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hp, hq]; omega
    · have := countP_lt_of_mono p q l (fun y hy => hm y (List.mem_cons_of_mem a hy)) ⟨x, hx, hq, hp⟩
      have ha := hm a (List.mem_cons_self)
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

theorem lrank_lt (ls : List w64) (i : Nat) (hi : i < 5) : lrank ls i < 5 := by
  unfold lrank
  have h := countP_lt_of_mono (fun j => lbefore ls j i) (fun _ => true) (List.range 5)
    (fun _ _ _ => rfl) ⟨i, List.mem_range.mpr hi, rfl, lbefore_irrefl ls i⟩
  simpa using h

theorem lrank_lt_of_before (ls : List w64) (i k : Nat) (hi : i < 5)
    (h : lbefore ls i k = true) : lrank ls i < lrank ls k :=
  countP_lt_of_mono _ _ (List.range 5) (fun j _ hj => lbefore_trans ls j i k hj h)
    ⟨i, List.mem_range.mpr hi, h, lbefore_irrefl ls i⟩

theorem lrank_inj (ls : List w64) (i k : Nat) (hi : i < 5) (hk : k < 5) (h : i ≠ k) :
    lrank ls i ≠ lrank ls k := by
  rcases lbefore_total ls i k h with h' | h'
  · have := lrank_lt_of_before ls i k hi h'; omega
  · have := lrank_lt_of_before ls k i hk h'; omega

theorem foldl_set_length {β : Type} (f : Nat → Nat) (g : Nat → β) :
    ∀ (l : List Nat) (q : List β), (l.foldl (fun q i => q.set (f i) (g i)) q).length = q.length
  | [], _ => rfl
  | a :: l, q => by
    rw [List.foldl_cons, foldl_set_length f g l]; simp

theorem quorumN_length (ls : List w64) (n : Nat) : (quorumN ls n).length = 5 := by
  unfold quorumN
  rw [foldl_set_length (lrank ls) (fun i : Nat => W32 (i : Int))]
  simp

theorem quorumN_get (ls : List w64) (n : Nat) (hn : n ≤ 5) (i : Nat) (hi : i < n) :
    (quorumN ls n)[lrank ls i]? = some (W32 (i : Int)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hq : quorumN ls (n + 1) = (quorumN ls n).set (lrank ls n) (W32 (n : Int)) := by
      unfold quorumN; rw [List.range_succ, List.foldl_append]; rfl
    rw [hq]
    by_cases hin : i = n
    · subst hin
      rw [List.getElem?_set_self]
      rw [quorumN_length]; exact lrank_lt ls i (by omega)
    · rw [List.getElem?_set_ne (lrank_inj ls n i (by omega) (by omega) (Ne.symm hin))]
      exact ih (by omega) (by omega)

theorem quorumOf_perm (ls : List w64) : (quorumOf ls).Perm R5 := by
  have hsub : R5 ⊆ quorumOf ls := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_R5 x).mp hx
    exact List.mem_of_getElem? (quorumN_get ls 5 (Nat.le_refl _) j hj)
  have := List.Subperm.perm_of_length_le (List.subperm_of_subset R5_nodup hsub)
    (by unfold quorumOf; rw [quorumN_length, R5_length]; exact Nat.le_refl 5)
  exact this.symm


/-! ## `UpdatePreferredPeerOrder` -/

/-- One step of the second loop: append `p` unless already there. -/
def updStep (cur : List w32) (p : w32) : List w32 := if p ∈ cur then cur else cur ++ [p]

/-- The quorum without the own id. -/
def updPre (q : List w32) (id : Nat) : List w32 := q.filter (fun x => x ≠ W32 (id : Int))

/-- `UpdatePreferredPeerOrder(q)`'s result on the old order `ord`. -/
def updOrder (q ord : List w32) (id : Nat) : List w32 := ord.foldl updStep (updPre q id)

theorem updStep_fold (pre : List w32) :
    ∀ (t s : List w32), (s ++ t).Nodup → (∀ x ∈ s, x ∉ pre) →
      t.foldl updStep (pre ++ s) = pre ++ s ++ t.filter (fun x => x ∉ pre)
  | [], s, _, _ => by simp
  | p :: t, s, hn, hs => by
    rw [List.foldl_cons]
    have hps : p ∉ s := by
      intro h
      have := (List.nodup_append.mp hn).2.2 p h p (List.mem_cons_self)
      exact this rfl
    by_cases hp : p ∈ pre
    · have : updStep (pre ++ s) p = pre ++ s := by
        unfold updStep; rw [if_pos (List.mem_append_left _ hp)]
      rw [this, updStep_fold pre t s (by
        have := hn; rw [List.nodup_append] at this ⊢
        exact ⟨this.1, (List.nodup_cons.mp this.2.1).2,
          fun a ha b hb => this.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩) hs]
      simp [hp]
    · have : updStep (pre ++ s) p = pre ++ (s ++ [p]) := by
        unfold updStep
        rw [if_neg (by
          intro h; rcases List.mem_append.mp h with h | h
          · exact hp h
          · exact hps h)]
        simp
      rw [this, updStep_fold pre t (s ++ [p]) (by simpa using hn) (by
        intro x hx; rcases List.mem_append.mp hx with hx | hx
        · exact hs x hx
        · simp at hx; subst hx; exact hp)]
      simp [hp]

theorem perm_R5_nodup (q : List w32) (h : q.Perm R5) : q.Nodup := h.nodup_iff.mpr R5_nodup

theorem R5_filter_ne_length (id : Nat) (hid : id < 5) :
    (R5.filter (fun x => x ≠ W32 (id : Int))).length = 4 := by
  rcases id with _ | _ | _ | _ | _ | id <;> first | decide | omega

theorem R5_filter_eq (id : Nat) (hid : id < 5) :
    R5.filter (fun x => decide (x = W32 (id : Int))) = [W32 (id : Int)] := by
  rcases id with _ | _ | _ | _ | _ | id <;> first | decide | omega

theorem W32_mem_R5 (id : Nat) (hid : id < 5) : W32 (id : Int) ∈ R5 := (mem_R5 _).mpr ⟨id, hid, rfl⟩

theorem updOrder_eq (q ord : List w32) (id : Nat) (hid : id < 5) (hq : q.Perm R5)
    (ho : ord.Perm R5) : updOrder q ord id = updPre q id ++ [W32 (id : Int)] := by
  unfold updOrder
  have h := updStep_fold (updPre q id) ord [] (by simpa using perm_R5_nodup ord ho) (by simp)
  simp only [List.append_nil] at h
  rw [h]
  congr 1
  have hp := List.Perm.filter (fun x => decide (x ∉ updPre q id)) ho
  have hc : R5.filter (fun x => decide (x ∉ updPre q id)) =
      R5.filter (fun x => decide (x = W32 (id : Int))) := by
    apply List.filter_congr
    intro x hx
    unfold updPre
    simp only [List.mem_filter, decide_eq_true_eq, not_and, decide_not]
    have hxq : x ∈ q := hq.symm.subset hx
    by_cases hxi : x = W32 (id : Int) <;> simp [hxi, hxq]
  rw [hc, R5_filter_eq id hid] at hp
  exact List.perm_singleton.mp hp

theorem updPre_length (q : List w32) (id : Nat) (hid : id < 5) (hq : q.Perm R5) :
    (updPre q id).length = 4 := by
  unfold updPre
  rw [(hq.filter _).length_eq, R5_filter_ne_length id hid]

theorem updOrder_perm (q ord : List w32) (id : Nat) (hid : id < 5) (hq : q.Perm R5)
    (ho : ord.Perm R5) : (updOrder q ord id).Perm R5 ∧
      (updOrder q ord id)[4]? = some (W32 (id : Int)) := by
  rw [updOrder_eq q ord id hid hq ho]
  refine ⟨?_, ?_⟩
  · have hsub : R5 ⊆ updPre q id ++ [W32 (id : Int)] := by
      intro x hx
      by_cases hxi : x = W32 (id : Int)
      · simp [hxi]
      · apply List.mem_append_left
        unfold updPre
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hq.symm.subset hx, hxi⟩
    exact (List.Subperm.perm_of_length_le (List.subperm_of_subset R5_nodup hsub)
      (by simp [updPre_length q id hid hq, R5_length])).symm
  · rw [List.getElem?_append_right (by rw [updPre_length q id hid hq]; exact Nat.le_refl 4)]
    simp [updPre_length q id hid hq]

theorem R5_map_sint : R5.map (fun x => sint.nat x) = List.range 5 := by decide

theorem set_pad {A : Type} (cur : List A) (x z : A) (n : Nat) (hn : cur.length < n) :
    (cur ++ List.replicate (n - cur.length) z).set cur.length x =
      (cur ++ [x]) ++ List.replicate (n - (cur.length + 1)) z := by
  obtain ⟨m, hm⟩ : ∃ m, n - cur.length = m + 1 := ⟨n - cur.length - 1, by omega⟩
  rw [hm, show n - (cur.length + 1) = m by omega]
  rw [List.set_append_right _ _ (by omega)]
  simp [List.replicate_succ]

theorem take_succ_eq {A : Type} (l : List A) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk]; rfl

theorem updStep_nodup_sub (acc : List w32) :
    ∀ (t : List w32), acc.Nodup → (∀ x ∈ acc, x ∈ R5) → (∀ x ∈ t, x ∈ R5) →
      (t.foldl updStep acc).Nodup ∧ ∀ x ∈ t.foldl updStep acc, x ∈ R5
  | [], h1, h2, _ => ⟨h1, h2⟩
  | a :: t, h1, h2, h3 => by
    rw [List.foldl_cons]
    apply updStep_nodup_sub _ t
    · unfold updStep; split
      · exact h1
      · rename_i h; exact List.nodup_append.mpr ⟨h1, by simp, by simp; intro x hx hxa; subst hxa; exact h hx⟩
    · unfold updStep; split
      · exact h2
      · intro x hx; rcases List.mem_append.mp hx with hx | hx
        · exact h2 x hx
        · simp at hx; subst hx; exact h3 _ (List.mem_cons_self)
    · intro x hx; exact h3 x (List.mem_cons_of_mem _ hx)

/-- The first loop's prefix after `k` entries of the quorum. -/
def pre1 (q : List w32) (id k : Nat) : List w32 := (q.take k).filter (fun x => x ≠ W32 (id : Int))

theorem pre1_succ (q : List w32) (id k : Nat) (hk : k < q.length) :
    pre1 q id (k + 1) = pre1 q id k ++ (if q[k] = W32 (id : Int) then [] else [q[k]]) := by
  unfold pre1; rw [take_succ_eq q k hk, List.filter_append]
  by_cases h : q[k] = W32 (id : Int)
  · simp [h]
  · simp [h, List.filter_cons]

theorem pre1_length_le (q : List w32) (id k : Nat) : (pre1 q id k).length ≤ k := by
  unfold pre1
  exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

theorem pre1_full (q : List w32) (id : Nat) (hq : q.length = 5) : pre1 q id 5 = updPre q id := by
  unfold pre1 updPre; rw [List.take_of_length_le (by omega)]

/-- The second loop's prefix after `k` entries of the old order. -/
def cur2 (q ord : List w32) (id k : Nat) : List w32 := (ord.take k).foldl updStep (updPre q id)

theorem cur2_succ (q ord : List w32) (id k : Nat) (hk : k < ord.length) :
    cur2 q ord id (k + 1) = updStep (cur2 q ord id k) ord[k] := by
  unfold cur2; rw [take_succ_eq ord k hk, List.foldl_append]; rfl

theorem cur2_full (q ord : List w32) (id : Nat) (ho : ord.length = 5) :
    cur2 q ord id 5 = updOrder q ord id := by
  unfold cur2 updOrder; rw [List.take_of_length_le (by omega)]

theorem cur2_ok (q ord : List w32) (id k : Nat) (hq : q.Perm R5) (ho : ord.Perm R5) :
    (cur2 q ord id k).Nodup ∧ ∀ x ∈ cur2 q ord id k, x ∈ R5 := by
  unfold cur2
  apply updStep_nodup_sub
  · unfold updPre; exact (perm_R5_nodup q hq).filter _
  · intro x hx; unfold updPre at hx; exact hq.subset (List.mem_filter.mp hx).1
  · intro x hx; exact ho.subset (List.mem_of_mem_take hx)

theorem cur2_length_lt (q ord : List w32) (id k : Nat) (hq : q.Perm R5) (ho : ord.Perm R5)
    (x : w32) (hx : x ∈ R5) (hn : x ∉ cur2 q ord id k) : (cur2 q ord id k).length < 5 := by
  obtain ⟨h1, h2⟩ := cur2_ok q ord id k hq ho
  have hnd : (cur2 q ord id k ++ [x]).Nodup :=
    List.nodup_append.mpr ⟨h1, by simp, by simp; intro y hy hyx; subst hyx; exact hn hy⟩
  have := List.Nodup.length_le_of_subset hnd (by
    intro y hy; rcases List.mem_append.mp hy with hy | hy
    · exact h2 y hy
    · simp at hy; subst hy; exact hx)
  simp [R5_length] at this; omega

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

theorem wp_UpdatePreferredPeerOrder (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) (qsl po : GoSlice) (q ord : List w32)
    (hq : q.Perm R5) (ho : ord.Perm R5) :
    {{ pkgInit_replica ∗ fwRO γ r id L p ∗ sync.isMutex (fld r go!"M") (fwLockInv γ id L p Rext) ∗
        qsl ↦* q ∗ fld r go!"PreferredPeerOrder" ↦ po ∗ po ↦* ord }}
      (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"UpdatePreferredPeerOrder"))
        (Val #qsl))
    {{ RET #(); qsl ↦* q ∗ ∃ aux : GoSlice, fld r go!"PreferredPeerOrder" ↦ aux ∗
        aux ↦* updOrder q ord id }} := by
  wp_start as ⟨#Hro, #Hmu, Hq, Hpf, Hpo⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, #HRPC, -, -, -, #HShut, -, -, -, -, -, -, #HEwma, #HLat, #HDt, %HL, #HLf,
    #HCI, -, -⟩
  have hL5 : L.length = 5 := HL.1
  have hid5 : id < 5 := by have := HL.2; omega
  rw [hL5]
  wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %aux ⟨Haux, -⟩
  · ipureintro; decide
  rename_i ic_ptr
  irename : (ic_ptr ↦ W64 0 : IProp GF) => Hic
  have hql : q.length = 5 := by rw [hq.length_eq, R5_length]
  ihave %Hqs := ownSlice_len _ _ _ $$ Hq
  have hqsl : sint.Z qsl.len = 5 := by have h1 := Hqs.1; rw [hql] at h1; have := Hqs.2; word
  -- the first loop: the quorum without the own id
  ihave HI : (∃ (k : Nat) (pv : w32),
      "i" ∷ i_ptr ↦ W64 (k : Int) ∗
      "Hic" ∷ ic_ptr ↦ W64 ((pre1 q id k).length : Int) ∗
      "Haux" ∷ aux ↦* (pre1 q id k ++ List.replicate (5 - (pre1 q id k).length) (W32 0)) ∗
      "p" ∷ p_ptr ↦ pv ∗ "%Hk" ∷ ⌜k ≤ 5⌝ : IProp GF) $$ [i Hic Haux p]
  · iexists 0, _
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · -- an iteration
    have hk5 : k < 5 := by rw [hqsl] at Hif; word
    have hkq : q[k]? = some (q[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z qsl.len by
      rw [hqsl]; constructor <;> word)]
    rw [show sint.Z (W64 (k : Int)) = (k : Int) by word]
    wp_apply wp_load_slice_index qsl (k : Int) q (DFrac.own 1) (q[k]'(by omega)) (by omega)
      $$ [Hq] as Hq
    · iframe; ipureintro; simpa using hkq
    have hsucc := pre1_succ q id k (by omega)
    have hle := pre1_length_le q id (k + 1)
    by_cases hqk : q[k]'(by omega) = W32 (id : Int)
    · rw [show decide (q[k]'(by omega) = W32 (id : Int)) = true from decide_eq_true hqk]
      wp_auto
      wp_for_post
      iframe
      iexists k + 1, _
      rw [hsucc, if_pos hqk, List.append_nil]
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe
      ipureintro; omega
    · rw [show decide (q[k]'(by omega) = W32 (id : Int)) = false from decide_eq_false hqk]
      wp_auto
      rw [hsucc, if_neg hqk] at hle
      simp only [List.length_append, List.length_singleton] at hle
      have hn5 : (pre1 q id k).length < 5 := by omega
      ihave %Hal := ownSlice_len _ _ _ $$ Haux
      have hal : sint.Z aux.len = 5 := by
        have h1 := Hal.1; simp only [List.length_append, List.length_replicate] at h1
        have := Hal.2; rw [show (pre1 q id k).length + (5 - (pre1 q id k).length) = 5 by omega] at h1
        word
      have hz : sint.Z (W64 ((pre1 q id k).length : Int)) = ((pre1 q id k).length : Int) := by
        word
      rw [hz, hal, if_pos (by omega)]
      wp_apply wp_store_slice_index aux _ _ (q[k]'(hql ▸ hk5)) $$ [Haux] as Haux
      · iframe; ipureintro; simp; omega
      wp_for_post
      iframe
      iexists k + 1, _
      rw [hsucc, if_neg hqk]
      simp only [Int.toNat_natCast]
      rw [set_pad _ _ _ 5 hn5]
      simp only [List.length_append, List.length_singleton]
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word,
        show W64 ((pre1 q id k).length : Int) + W64 1 =
          W64 (((pre1 q id k).length + 1 : Nat) : Int) by word]
      iframe
      ipureintro; omega
  -- the second loop: the old order's entries not yet there
  have hk : k = 5 := by rw [hqsl] at Hif; have : ¬ ((k : Int) < 5) := by word
                        omega
  subst hk
  rw [pre1_full q id hql]
  have hpl := updPre_length q id hid5 hq
  have hol : ord.length = 5 := by rw [ho.length_eq, R5_length]
  ihave %Hos := ownSlice_len _ _ _ $$ Hpo
  have hosl : sint.Z po.len = 5 := by have h1 := Hos.1; rw [hol] at h1; have := Hos.2; word
  ihave HI : (∃ (k : Nat) (pv : w32),
      "i" ∷ i_ptr ↦ W64 (k : Int) ∗
      "Hic" ∷ ic_ptr ↦ W64 ((cur2 q ord id k).length : Int) ∗
      "Haux" ∷ aux ↦* (cur2 q ord id k ++ List.replicate (5 - (cur2 q ord id k).length) (W32 0)) ∗
      "p" ∷ p_ptr ↦ pv ∗ "%Hk" ∷ ⌜k ≤ 5⌝ : IProp GF) $$ [i Hic Haux p]
  · iexists 0, _
    unfold cur2
    simp only [List.take_zero, List.foldl_nil]
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hk5 : k < 5 := by rw [hosl] at Hif; word
    have hko : ord[k]? = some (ord[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z po.len by
      rw [hosl]; constructor <;> word)]
    rw [show sint.Z (W64 (k : Int)) = (k : Int) by word]
    wp_apply wp_load_slice_index po (k : Int) ord (DFrac.own 1) (ord[k]'(by omega)) (by omega)
      $$ [Hpo] as Hpo
    · iframe; ipureintro; simpa using hko
    have hsucc := cur2_succ q ord id k (by omega)
    have hmem : ord[k]'(by omega) ∈ R5 := ho.subset (List.getElem_mem _)
    ihave %Hal := ownSlice_len _ _ _ $$ Haux
    have hcl5 : (cur2 q ord id k).length ≤ 5 := by
      obtain ⟨h1, h2⟩ := cur2_ok q ord id k hq ho
      have := List.Nodup.length_le_of_subset h1 h2; rw [R5_length] at this; exact this
    have hal : sint.Z aux.len = 5 := by
      have h1 := Hal.1; simp only [List.length_append, List.length_replicate] at h1
      have := Hal.2
      rw [show (cur2 q ord id k).length + (5 - (cur2 q ord id k).length) = 5 by omega] at h1
      word
    ihave HJ : (∃ jn : Nat, "j" ∷ j_ptr ↦ W64 (jn : Int) ∗ "found" ∷ found_ptr ↦ false ∗
        "%Hj" ∷ ⌜jn ≤ (cur2 q ord id k).length ∧
          ord[k]'(by omega) ∉ (cur2 q ord id k).take jn⌝ : IProp GF) $$ [j found]
    · iexists 0; iframe; ipureintro; simp
    wp_for HJ
    have hcz : sint.Z (W64 ((cur2 q ord id k).length : Int)) = ((cur2 q ord id k).length : Int) := by
      word
    wp_if_destruct
    · -- compare `aux[j]`
      have hjl : jn < (cur2 q ord id k).length := by rw [hcz] at Hif; have := Hj.1; word
      have hjz : sint.Z (W64 (jn : Int)) = (jn : Int) := by word
      rw [hjz, hal, if_pos (by omega)]
      have hgj : (cur2 q ord id k ++ List.replicate (5 - (cur2 q ord id k).length) (W32 0))[jn]? =
          some ((cur2 q ord id k)[jn]'hjl) := by
        rw [List.getElem?_append_left hjl, List.getElem?_eq_getElem hjl]
      wp_apply wp_load_slice_index aux (jn : Int) _ (DFrac.own 1) ((cur2 q ord id k)[jn]'hjl)
        (by omega) $$ [Haux] as Haux
      · iframe; ipureintro; simpa using hgj
      by_cases heq : (cur2 q ord id k)[jn]'hjl = ord[k]'(by omega)
      · rw [show decide ((cur2 q ord id k)[jn]'hjl = ord[k]'(by omega)) = true from
          decide_eq_true heq]
        wp_auto
        wp_for_post
        -- found: nothing appended
        have hin : ord[k]'(by omega) ∈ cur2 q ord id k := by rw [← heq]; exact List.getElem_mem _
        have hst : cur2 q ord id (k + 1) = cur2 q ord id k := by
          rw [hsucc]; unfold updStep; rw [if_pos hin]
        wp_for_post
        iframe
        iexists k + 1, _
        rw [hst, show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe
        ipureintro; omega
      · rw [show decide ((cur2 q ord id k)[jn]'hjl = ord[k]'(by omega)) = false from
          decide_eq_false heq]
        wp_auto
        wp_for_post
        iframe
        iexists jn + 1
        rw [show W64 (jn : Int) + W64 1 = W64 ((jn + 1 : Nat) : Int) by word]
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        rw [take_succ_eq _ _ hjl]
        intro h; rcases List.mem_append.mp h with h | h
        · exact Hj.2 h
        · simp at h; exact heq h.symm
    · -- not found: appended
      have hjl : jn = (cur2 q ord id k).length := by
        rw [hcz] at Hif; have := Hj.1; have : ¬ ((jn : Int) < (cur2 q ord id k).length) := by word
        omega
      have hnin : ord[k]'(by omega) ∉ cur2 q ord id k := by
        have := Hj.2; rw [hjl, List.take_length] at this; exact this
      have hlt := cur2_length_lt q ord id k hq ho _ hmem hnin
      have hst : cur2 q ord id (k + 1) = cur2 q ord id k ++ [ord[k]'(by omega)] := by
        rw [hsucc]; unfold updStep; rw [if_neg hnin]
      rw [hcz, hal]; rw [if_pos (by omega)]
      wp_apply wp_store_slice_index aux _ _ (ord[k]'(hol ▸ hk5)) $$ [Haux] as Haux
      · iframe; ipureintro; simp; omega
      wp_for_post
      iframe
      iexists k + 1, _
      rw [hst]
      simp only [Int.toNat_natCast]
      rw [set_pad _ _ _ 5 hlt]
      simp only [List.length_append, List.length_singleton]
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word,
        show W64 ((cur2 q ord id k).length : Int) + W64 1 =
          W64 (((cur2 q ord id k).length + 1 : Nat) : Int) by word]
      iframe
      ipureintro; omega
  have hk : k = 5 := by rw [hosl] at Hif; have : ¬ ((k : Int) < 5) := by word
                        omega
  subst hk
  rw [cur2_full q ord id hol]
  have hul : (updOrder q ord id).length = 5 := by
    rw [(updOrder_perm q ord id hid5 hq ho).1.length_eq, R5_length]
  rw [hul]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked $HR]
  iapply HΦ
  iframe

theorem replica.Replica.ComputeClosestPeers.spec_holds (hSB : replica.Replica.SendBeacon.spec (GF := GF))
    (hPrintln : dlog.Logger.Println.spec (GF := GF)) : replica.Replica.ComputeClosestPeers.spec (GF := GF) := by
  intro γ r id L p Rext
  wp_start as ⟨#Hfw, Hpref⟩
  ihave #Hfw' := isReplicaFw_def $$ Hfw
  iunfold isReplicaFwDef at Hfw'
  icases Hfw' with ⟨#Hro, #Hfz, #Hmu, #Hph1, #Hph2⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, #HRPC, -, -, -, #HShut, -, -, -, -, -, -, #HEwma, #HLat, #HDt, %HL, #HLf,
    #HCI, -, -⟩
  unfold fwPrefOwn
  icases Hpref with ⟨%po, %ord, Hpf, Hpo, %Hord⟩
  have ho : ord.Perm R5 := Hord.1
  have hL5 : L.length = 5 := HL.1
  have hid5 : id < 5 := by have := HL.2; omega
  unfold fwMethod
  wp_method_call
  wp_call
  rw [hL5]
  wp_auto
  -- the beacons: 20 rounds over the live peers
  ihave HO : (∃ jv : w64, "j" ∷ j_ptr ↦ jv : IProp GF) $$ [j]
  · iexists _; iframe
  wp_for HO
  wp_if_destruct
  · ihave HI : (∃ n : Nat, "i" ∷ i_ptr ↦ W32 (n : Int) ∗ "%Hn" ∷ ⌜n ≤ 5⌝ : IProp GF) $$ [i]
    · iexists 0; iframe; ipureintro; omega
    wp_for HI
    wp_if_destruct
    · have hn5 : n < 5 := by
        have : sint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int)))) = 5 := by decide
        rw [this] at Hif; word
      by_cases hni : n = id
      · subst hni
        rw [show decide (W32 (n : Int) = W32 (n : Int)) = true by simp]
        wp_auto
        wp_for_post
        iframe
        iexists n + 1
        rw [show W32 (n : Int) + W32 1 = W32 ((n + 1 : Nat) : Int) by word]
        iframe; ipureintro; omega
      · rw [show decide (W32 (n : Int) = W32 (id : Int)) = false by
          simp only [decide_eq_false_iff_not]; intro h; apply hni; word]
        wp_auto
        wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
        iunfold fwLockInv at HR
        icases HR with ⟨Hcore, HRext⟩
        ihave Hacc := fwCore_peers_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hcore Hlc1
        iapply fupd_wp
        imod Hacc with ⟨Hpeers, Hcore⟩
        imodintro
        iunfold fwPeers at Hpeers
        icases Hpeers with ⟨%cs, %ws, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hsl⟩
        ihave %Hal := ownSlice_len _ _ _ $$ Has
        ihave %Hll := ownSlice_len _ _ _ $$ Hls
        have hal : sint.Z p.alive.len = 5 := by
          have h1 := Hal.1; rw [Hlen.2.2.1, hL5] at h1; have := Hal.2; word
        have hll : sint.Z p.lat.len = 5 := by
          have h1 := Hll.1; rw [Hlen.2.2.2, hL5] at h1; have := Hll.2; word
        have hnz : sint.Z (W64 (sint.Z (W32 (n : Int)))) = (n : Int) := by word
        rw [hnz, if_pos (by rw [hal]; omega)]
        have hga : als[n]? = some (als.getD n false) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
        wp_apply wp_load_slice_index p.alive (n : Int) als (DFrac.own 1) (als.getD n false)
          (by omega) $$ [Has] as Has
        · iframe; ipureintro; simpa using hga
        cases hb : als.getD n false
        · -- not alive: the latency is the maximum
          wp_auto
          rw [hnz, if_pos (by rw [hll]; omega)]
          wp_apply wp_store_slice_index p.lat (n : Int) ls _ $$ [Hls] as Hls
          · iframe; ipureintro; omega
          ihave Hcore := Hcore $$ [Hps Hws Has Hls Hsl]
          · iunfold fwPeers
            iexists cs, ws, als, _
            iframe
            ipureintro; simp [Hlen]
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
          · unfold fwLockInv; iframe
          wp_for_post
          iframe
          iexists n + 1
          rw [show W32 (n : Int) + W32 1 = W32 ((n + 1 : Nat) : Int) by word]
          iframe; ipureintro; omega
        · -- alive: a beacon
          wp_auto
          ihave Hcore := Hcore $$ [Hps Hws Has Hls Hsl]
          · iunfold fwPeers
            iexists cs, ws, als, ls
            iframe
            ipureintro; exact Hlen
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
          · unfold fwLockInv; iframe
          wp_apply hSB γ r id L p Rext n $$ [Hfw]
          · iframe #; ipureintro; exact ⟨by omega, hni⟩
          wp_for_post
          iframe
          iexists n + 1
          rw [show W32 (n : Int) + W32 1 = W32 ((n + 1 : Nat) : Int) by word]
          iframe; ipureintro; omega
    · wp_apply time.Sleep.wp_proof
      wp_for_post
      iframe
      iexists _; iframe
  -- the ranking, under `r.M`
  wp_apply (wp_slice_make2 (V := w32) (W64 ((5 : Nat) : Int))) as %qsl ⟨Hqs, -⟩
  · ipureintro; decide
  wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold fwLockInv at HR
  icases HR with ⟨Hcore, HRext⟩
  ihave Hacc := fwCore_peers_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hcore Hlc1
  iapply fupd_wp
  imod Hacc with ⟨Hpeers, Hcore⟩
  imodintro
  iunfold fwPeers at Hpeers
  icases Hpeers with ⟨%cs, %ws, %als, %ls, Hps, Hws, Has, Hls, %Hlen, Hsl⟩
  ihave %Hll := ownSlice_len _ _ _ $$ Hls
  have hll : sint.Z p.lat.len = 5 := by
    have h1 := Hll.1; rw [Hlen.2.2.2, hL5] at h1; have := Hll.2; word
  have hls5 : ls.length = 5 := by rw [Hlen.2.2.2, hL5]
  have hz : (Perennial.zero_val w32) = W32 0 := rfl
  rw [hz, show List.replicate (sint.nat (W64 ((5 : Nat) : Int))) (W32 0) = quorumN ls 0 by
      unfold quorumN; rfl]
  ihave HQ : (∃ n : Nat, "i" ∷ i_ptr ↦ W32 (n : Int) ∗ "Hqs" ∷ qsl ↦* quorumN ls n ∗
      "%Hn" ∷ ⌜n ≤ 5⌝ : IProp GF) $$ [i Hqs]
  · iexists 0; iframe; ipureintro; omega
  wp_for HQ
  wp_if_destruct
  · have hn5 : n < 5 := by
      have : sint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int)))) = 5 := by decide
      rw [this] at Hif; word
    ihave HP : (∃ m : Nat, "j" ∷ j_ptr ↦ W32 (m : Int) ∗
        "pos" ∷ pos_ptr ↦ W64 (((List.range m).countP (fun j => lbefore ls j n) : Nat) : Int) ∗
        "%Hm" ∷ ⌜m ≤ 5⌝ : IProp GF) $$ [j pos]
    · iexists 0; iframe; ipureintro; omega
    wp_for HP
    have hnz : sint.Z (W64 (sint.Z (W32 (n : Int)))) = (n : Int) := by word
    wp_if_destruct
    · have hm5 : m < 5 := by
        have : sint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int)))) = 5 := by decide
        rw [this] at Hif; word
      have hmz : sint.Z (W64 (sint.Z (W32 (m : Int)))) = (m : Int) := by word
      have hgm : ls[m]? = some (ls.getD m (W64 0)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have hgn : ls[n]? = some (ls.getD n (W64 0)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have hcs : (List.range (m + 1)).countP (fun j => lbefore ls j n) =
          (List.range m).countP (fun j => lbefore ls j n) + (if lbefore ls m n then 1 else 0) := by
        rw [List.range_succ, List.countP_append]; simp [List.countP_cons]
      rw [hmz, if_pos (by rw [hll]; omega)]
      wp_apply wp_load_slice_index p.lat (m : Int) ls (DFrac.own 1) (ls.getD m (W64 0)) (by omega)
        $$ [Hls] as Hls
      · iframe; ipureintro; simpa using hgm
      rw [hnz, if_pos (by rw [hll]; omega)]
      wp_apply wp_load_slice_index p.lat (n : Int) ls (DFrac.own 1) (ls.getD n (W64 0)) (by omega)
        $$ [Hls] as Hls
      · iframe; ipureintro; simpa using hgn
      by_cases hlt : sint.Z (ls.getD m (W64 0)) < sint.Z (ls.getD n (W64 0))
      · have hbv : lbefore ls m n = true := by unfold lbefore; rw [decide_eq_true hlt]
        rw [show decide (sint.Z (ls.getD m (W64 0)) < sint.Z (ls.getD n (W64 0))) = true from
          decide_eq_true hlt]
        wp_auto
        wp_for_post
        iframe
        iexists m + 1
        rw [show W32 (m : Int) + W32 1 = W32 ((m + 1 : Nat) : Int) by word, hcs, hbv]
        simp only [ite_true]
        rw [show W64 ((((List.range m).countP (fun j => lbefore ls j n) : Nat) : Int)) + W64 1 =
          W64 (((List.range m).countP (fun j => lbefore ls j n) + 1 : Nat) : Int) by
            have := List.countP_le_length (p := fun j => lbefore ls j n) (l := List.range m)
            simp at this; word]
        iframe; ipureintro; omega
      · rw [show decide (sint.Z (ls.getD m (W64 0)) < sint.Z (ls.getD n (W64 0))) = false from
          decide_eq_false hlt]
        wp_auto
        rw [hmz, if_pos (by rw [hll]; omega)]
        wp_apply wp_load_slice_index p.lat (m : Int) ls (DFrac.own 1) (ls.getD m (W64 0)) (by omega)
          $$ [Hls] as Hls
        · iframe; ipureintro; simpa using hgm
        rw [hnz, if_pos (by rw [hll]; omega)]
        wp_apply wp_load_slice_index p.lat (n : Int) ls (DFrac.own 1) (ls.getD n (W64 0)) (by omega)
          $$ [Hls] as Hls
        · iframe; ipureintro; simpa using hgn
        by_cases heq : ls.getD m (W64 0) = ls.getD n (W64 0)
        · rw [show decide (ls.getD m (W64 0) = ls.getD n (W64 0)) = true from decide_eq_true heq]
          wp_auto
          by_cases hmn : m < n
          · have hbv : lbefore ls m n = true := by
              unfold lbefore; rw [decide_eq_false hlt, decide_eq_true heq, decide_eq_true hmn]; rfl
            rw [show decide (sint.Z (W32 (m : Int)) < sint.Z (W32 (n : Int))) = true from
              decide_eq_true (by word)]
            wp_auto
            wp_for_post
            iframe
            iexists m + 1
            rw [show W32 (m : Int) + W32 1 = W32 ((m + 1 : Nat) : Int) by word, hcs, hbv]
            simp only [ite_true]
            rw [show W64 ((((List.range m).countP (fun j => lbefore ls j n) : Nat) : Int)) + W64 1 =
              W64 (((List.range m).countP (fun j => lbefore ls j n) + 1 : Nat) : Int) by
                have := List.countP_le_length (p := fun j => lbefore ls j n) (l := List.range m)
                simp at this; word]
            iframe; ipureintro; omega
          · have hbv : lbefore ls m n = false := by
              unfold lbefore; rw [decide_eq_false hlt, decide_eq_true heq, decide_eq_false hmn]; rfl
            rw [show decide (sint.Z (W32 (m : Int)) < sint.Z (W32 (n : Int))) = false from
              decide_eq_false (by word)]
            wp_auto
            wp_for_post
            iframe
            iexists m + 1
            rw [show W32 (m : Int) + W32 1 = W32 ((m + 1 : Nat) : Int) by word, hcs, hbv]
            simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
            iframe; ipureintro; omega
        · have hbv : lbefore ls m n = false := by
            unfold lbefore; rw [decide_eq_false hlt, decide_eq_false heq]; rfl
          rw [show decide (ls.getD m (W64 0) = ls.getD n (W64 0)) = false from decide_eq_false heq]
          wp_auto
          wp_for_post
          iframe
          iexists m + 1
          rw [show W32 (m : Int) + W32 1 = W32 ((m + 1 : Nat) : Int) by word, hcs, hbv]
          simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          iframe; ipureintro; omega
    · -- `quorum[pos] = i`
      have hm : m = 5 := by
        have : sint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int)))) = 5 := by decide
        rw [this] at Hif; have : ¬ ((m : Int) < 5) := by word
        omega
      subst hm
      have hr : (List.range 5).countP (fun j => lbefore ls j n) = lrank ls n := rfl
      rw [hr]
      have hrl := lrank_lt ls n hn5
      ihave %Hql := ownSlice_len _ _ _ $$ Hqs
      have hqsl : sint.Z qsl.len = 5 := by
        have h1 := Hql.1; rw [quorumN_length] at h1; have := Hql.2; word
      have hrz : sint.Z (W64 ((lrank ls n : Nat) : Int)) = (lrank ls n : Int) := by word
      rw [hrz, hqsl, if_pos (by omega)]
      wp_apply wp_store_slice_index qsl _ _ (W32 (n : Int)) $$ [Hqs] as Hqs
      · iframe; ipureintro; rw [quorumN_length]; omega
      wp_for_post
      iframe
      iexists n + 1
      have hqn : quorumN ls (n + 1) = (quorumN ls n).set (lrank ls n) (W32 (n : Int)) := by
        unfold quorumN; rw [List.range_succ, List.foldl_append]; rfl
      rw [hqn, show W32 (n : Int) + W32 1 = W32 ((n + 1 : Nat) : Int) by word]
      simp only [Int.toNat_natCast]
      iframe; ipureintro; omega
  have hn : n = 5 := by
    have : sint.Z (W32 (sint.Z (W64 ((5 : Nat) : Int)))) = 5 := by decide
    rw [this] at Hif; have : ¬ ((n : Int) < 5) := by word
    omega
  subst hn
  ihave Hcore := Hcore $$ [Hps Hws Has Hls Hsl]
  · iunfold fwPeers
    iexists cs, ws, als, ls
    iframe
    ipureintro; exact Hlen
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
  · unfold fwLockInv; iframe
  wp_apply (wp_UpdatePreferredPeerOrder γ r id L p Rext qsl po (quorumOf ls) ord
    (quorumOf_perm ls) ho) $$ [Hqs Hpf Hpo] as ⟨Hqs, %aux, Hpf, Haux⟩
  · iframe #; unfold quorumOf; iframe
  obtain ⟨hU, hU4⟩ := updOrder_perm (quorumOf ls) ord id hid5 (quorumOf_perm ls) ho
  ipersist Hpf
  iapply fupd_wp
  imod (ownSlice_persist aux (DFrac.own 1) _) $$ Haux with #Haux
  imodintro
  have hUl : (updOrder (quorumOf ls) ord id).length = 5 := by rw [hU.length_eq, R5_length]
  ihave %Haul := ownSlice_len _ _ _ $$ Haux
  have haul : sint.Z aux.len = 5 := by
    have h1 := Haul.1; rw [hUl] at h1; have := Haul.2; word
  -- the latencies, printed
  wp_apply (wp_slice_make2 (V := w64) (W64 ((5 : Nat) : Int) - W64 1)) as %lsl ⟨Hlsl, -⟩
  · ipureintro; decide
  ihave HL : (∃ (k : Nat) (vs : List w64), "i" ∷ i_ptr ↦ W64 (k : Int) ∗ "Hlsl" ∷ lsl ↦* vs ∗
      "%Hk" ∷ ⌜k ≤ 4 ∧ vs.length = 4⌝ : IProp GF) $$ [i Hlsl]
  · iexists 0, _; iframe; ipureintro; constructor
    · omega
    · simp only [List.length_replicate]; decide
  wp_for HL
  wp_if_destruct
  · have hk4 : k < 4 := by
      have : sint.Z (W64 ((5 : Nat) : Int) - W64 1) = 4 := by decide
      rw [this] at Hif; word
    have hkz : sint.Z (W64 (k : Int)) = (k : Int) := by word
    obtain ⟨jj, hjj, hUk⟩ := (mem_R5 _).mp (hU.subset (List.getElem_mem (l := updOrder (quorumOf ls) ord id)
      (n := k) (by omega)))
    have hgU : (updOrder (quorumOf ls) ord id)[k]? = some (W32 (jj : Int)) := by
      rw [List.getElem?_eq_getElem (by omega), hUk]
    rw [hkz, haul, if_pos (by omega)]
    wp_apply wp_load_slice_index aux (k : Int) _ DFrac.discard (W32 (jj : Int)) (by omega)
      $$ [Haux] as -
    · iframe #; ipureintro; simpa using hgU
    wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold fwLockInv at HR
    icases HR with ⟨Hcore, HRext⟩
    ihave Hacc := fwCore_peers_acc (GF := GF) γ id L p ⊤ CoPset.subseteq_top $$ Hph1 Hcore Hlc1
    iapply fupd_wp
    imod Hacc with ⟨Hpeers, Hcore⟩
    imodintro
    iunfold fwPeers at Hpeers
    icases Hpeers with ⟨%cs, %ws, %als, %ls', Hps, Hws, Has, Hls, %Hlen', Hsl⟩
    ihave %Hll' := ownSlice_len _ _ _ $$ Hls
    have hll' : sint.Z p.lat.len = 5 := by
      have h1 := Hll'.1; rw [Hlen'.2.2.2, hL5] at h1; have := Hll'.2; word
    have hjz : sint.Z (W64 (sint.Z (W32 (jj : Int)))) = (jj : Int) := by word
    rw [hjz, hll', if_pos (by omega)]
    have hgl : ls'[jj]? = some (ls'.getD jj (W64 0)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Hlen'.2.2.2, hL5]; omega)]
      rfl
    wp_apply wp_load_slice_index p.lat (jj : Int) ls' (DFrac.own 1) (ls'.getD jj (W64 0)) (by omega)
      $$ [Hls] as Hls
    · iframe; ipureintro; simpa using hgl
    ihave Hcore := Hcore $$ [Hps Hws Has Hls Hsl]
    · iunfold fwPeers
      iexists cs, ws, als, ls'
      iframe
      ipureintro; exact Hlen'
    wp_apply wp_float64_div as %fl -
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcore HRext]
    · unfold fwLockInv; iframe
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨-, -⟩
    wp_auto
    wp_apply wp_rPrintln hPrintln γ r id L p $$ [$Hro]
    ihave %Hvl := ownSlice_len _ _ _ $$ Hlsl
    have hvl : sint.Z lsl.len = 4 := by
      have h1 := Hvl.1; rw [Hk.2] at h1; have := Hvl.2; word
    rw [hkz, hvl, if_pos (by omega)]
    wp_apply wp_store_slice_index lsl (k : Int) vs _ $$ [Hlsl] as Hlsl
    · iframe; ipureintro; omega
    wp_for_post
    iframe
    iexists k + 1, _
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
    iframe
    ipureintro; simp [Hk.2]; omega
  -- the result: `PreferredPeerOrder` read-only from now on
  iapply HΦ
  iexists updOrder (quorumOf ls) ord id
  unfold prefOrder
  iexists aux
  iframe #
  ipureintro
  refine ⟨?_, by rw [hL5]; exact hU4, fun o ho => ?_⟩
  · rw [hL5, ← R5_map_sint]
    exact hU.map _
  · obtain ⟨j, hj, rfl⟩ := (mem_R5 o).mp (hU.subset ho)
    have : j < 5 := hj
    word

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
