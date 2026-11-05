/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseExpiredNotifier__Init.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Init
public import Spec.container.heap.Init_
public import Proof.go_etcd_io.etcd.server.v3.lease.QueueLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section lemmas

/-- **One step of `Init`'s loop** (`mq.m[item.id] = item`): a map holding exactly the items `zs`,
each under its id, with the next item `x` (of an id not among them) inserted, holds `zs ++ [x]`. -/
theorem notif_step (zs : List (Loc × w64)) (x : Loc × w64)
    (hnd : ((zs ++ [x]).map Prod.snd).Nodup) (M : GMap w64 Loc)
    (hM : ∀ (id : w64) (p : Loc), M.lookup id = some p ↔ (p, id) ∈ zs) (id : w64) (p : Loc) :
    (M.insert x.2 x.1).lookup id = some p ↔ (p, id) ∈ zs ++ [x] := by
  have hx : x.2 ∉ zs.map Prod.snd := by
    simp only [List.map_append, List.map_cons, List.map_nil] at hnd
    rw [List.nodup_append] at hnd
    exact fun h => hnd.2.2 _ h _ (List.mem_singleton_self _) rfl
  rw [GMap.lookup_insert_eq_iff, List.mem_append, List.mem_singleton]
  by_cases hxi : x.2 = id
  · subst hxi
    rw [if_pos rfl]
    constructor
    · intro h; cases h; right; rfl
    · rintro (h | h)
      · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hx
      · rw [← h]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hxi), hM]
    constructor
    · intro h; left; exact h
    · rintro (h | h)
      · exact h
      · subst h; exact absurd rfl hxi

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseExpiredNotifier.Init.wp_proof
    (hLen : lease.LeaseQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.LeaseQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.LeaseQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : lease.LeaseQueue.Push.spec (GF := GF) (hG := hG))
    (hInit : heap.Init_.spec (GF := GF) (hG := hG)) :
    lease.LeaseExpiredNotifier.Init.spec (GF := GF) (hG := hG) := by
  intro np
  wp_start as Hn
  ihave #Hheap : isPkgInit (PROP := IProp GF) pkg_id.container.heap $$ []
  · iPkgInit
  ihave #Hiface := queue_heapIface hLen hLess hSwap hPush (nF go!"queue" np) $$ Hpkg
  iunfold notifierAt at Hn
  icases Hn with ⟨%mp, %s, %M, %xs, Hm, HM, Hq, Hqa, %Hinv⟩
  wp_auto
  wp_apply (hInit (Loc × w64) (interface.mk (go.GoType.PointerType LeaseQueue.ty)
      #(nF go!"queue" np)) (queueHeap (nF go!"queue" np)) queueElem xs)
    $$ [$Hheap $Hiface Hq Hqa] as ⟨%ys, Hys, %Hperm⟩
  · iunfold queueHeap; iexists s; iframe
  iunfold queueHeap at Hys
  icases Hys with ⟨%s', Hq, Hqa⟩
  -- the ids of the queue's items are distinct (the map had each under its id, no item twice)
  have hfst : (ys.map Prod.fst).Nodup := (List.Perm.map Prod.fst Hperm).nodup_iff.mpr Hinv.1
  have hxsnd : (xs.map Prod.snd).Nodup := by
    have h0 : (xs.map Prod.fst).Nodup := Hinv.1
    unfold List.Nodup at h0 ⊢
    rw [List.pairwise_map] at h0 ⊢
    refine h0.imp_of_mem ?_
    intro x y hx hy hne hxy
    apply hne
    obtain ⟨p, i⟩ := x
    obtain ⟨q, j⟩ := y
    simp only at hxy ⊢
    subst hxy
    have h1 := (Hinv.2 i p).2 hx
    have h2 := (Hinv.2 i q).2 hy
    rw [h1] at h2; cases h2; rfl
  have hsnd : (ys.map Prod.snd).Nodup := (List.Perm.map Prod.snd Hperm).nodup_iff.mpr hxsnd
  iunfold queueAt at Hqa
  icases Hqa with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s' _ _ $$ Hs
  simp only [List.length_map] at Hlen
  (try wp_auto)
  wp_apply (wp_map_make1 (V := Loc) LeaseID.ty (go.GoType.PointerType LeaseWithTime.ty))
    as %mp' HM'
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (itv : Loc) (M' : GMap w64 Loc),
      "Hi" ∷ i_ptr ↦ n ∗ "Hit" ∷ item_ptr ↦ itv ∗ "HM'" ∷ mp' ↦$ M' ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s'.len⌝ ∗
      "%HMn" ∷ ⌜∀ (id : w64) (p : Loc), M'.lookup id = some p ↔ (p, id) ∈ ys.take (sint.nat n)⌝)
      $$ [i item HM']
  · iexists W64 0, _, ∅
    iframe i item HM'
    ipureintro; constructor
    · constructor <;> word
    · intro id p; rw [show sint.nat (W64 0) = 0 by word]; simp [GMap.lookup_empty]
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ys.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, ys[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s'.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index s' (sint.Z n) (ys.map Prod.fst) (DFrac.own 1) x.1 Hn.1
      $$ [Hs] as Hs
    · iframe; ipureintro
      rw [List.getElem?_map, show (sint.Z n).toNat = sint.nat n by word, Hx]; rfl
    icases (BigSepL.bigSepL_lookup_acc Hx).1 $$ Hits with ⟨Hel, Hits⟩
    iunfold lwtAt at Hel
    icases Hel with ⟨#Hid, ⟨%tt, Htt⟩, Hix⟩
    ihave Hits := Hits $$ [Hid Htt Hix]
    · iunfold lwtAt; iframe Hid Hix; iexists tt; iexact Htt
    rw [list_set_lookup_self ys _ _ Hx]
    wp_auto
    wp_apply (wp_mapInsert LeaseID.ty mp' M' x.2 x.1) $$ HM' as HM'
    wp_for_post
    iframe
    iexists n + W64 1, x.1, _
    iframe
    ipureintro
    constructor
    · constructor <;> word
    · have h1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      have htk : ys.take (sint.nat n + 1) = ys.take (sint.nat n) ++ [x] := by
        rw [List.take_add_one, Hx]; rfl
      rw [h1, htk]
      refine notif_step _ x ?_ M' HMn
      rw [← htk]
      exact hsnd.sublist ((List.take_sublist _ _).map _)
  · have hys : ys.take (sint.nat n) = ys := by
      apply List.take_of_length_le; word
    rw [hys] at HMn
    iapply HΦ
    iunfold notifierAt
    iexists mp', s', M', ys
    iframe
    iunfold queueAt
    iframe
    ipureintro
    exact ⟨hfst, HMn⟩

end proof

end EtcdGrove
end Perennial
