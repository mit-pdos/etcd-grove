/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseExpiredNotifier__RegisterOrUpdate.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__RegisterOrUpdate
public import Spec.container.heap.Push
public import Spec.container.heap.Fix
public import Proof.go_etcd_io.etcd.server.v3.lease.QueueLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseExpiredNotifier.RegisterOrUpdate.wp_proof
    (hLen : lease.LeaseQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.LeaseQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.LeaseQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : lease.LeaseQueue.Push.spec (GF := GF) (hG := hG))
    (hFix : heap.Fix.spec (GF := GF) (hG := hG))
    (hHPush : heap.Push.spec (GF := GF) (hG := hG)) :
    lease.LeaseExpiredNotifier.RegisterOrUpdate.spec (GF := GF) (hG := hG) := by
  intro np item id k
  wp_start as ⟨Hn, Hit⟩
  ihave #Hheap : isPkgInit (PROP := IProp GF) pkg_id.container.heap $$ []
  · iPkgInit
  ihave #Hiface := queue_heapIface hLen hLess hSwap hPush (nF go!"queue" np) $$ Hpkg
  iunfold notifierAt at Hn
  icases Hn with ⟨%mp, %s, %M, %xs, Hm, HM, Hq, Hqa, %Hinv⟩
  ihave Hit' := Hit
  iunfold lwtAt at Hit'
  icases Hit' with ⟨#Hid, Ht, Hix⟩
  iunfold queueAt at Hqa
  icases Hqa with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  simp only [List.length_map] at Hlen
  wp_auto
  wp_apply (wp_map_lookup2 LeaseID.ty (go.GoType.PointerType LeaseWithTime.ty) mp M id) $$ HM
    as HM
  cases hM : M !! id with
  | some old =>
    simp only [Option.getD_some, Option.isSome_some, decide_true]
    have hmem : (old, id) ∈ xs := (Hinv.2 id old).1 hM
    obtain ⟨n, hn, hxn⟩ := List.mem_iff_getElem.mp hmem
    have hxn' : xs[n]? = some (old, id) := by rw [List.getElem?_eq_getElem hn, hxn]
    icases (BigSepL.bigSepL_lookup_acc hxn').1 $$ Hits with ⟨Hold, Hits⟩
    iunfold lwtAt at Hold
    icases Hold with ⟨#Hoid, ⟨%to, Hto⟩, Hoix⟩
    icases Ht with ⟨%t, Ht⟩
    wp_auto
    ihave Hits := Hits $$ [Hoid Hto Hoix]
    · iunfold lwtAt; iframe Hoid Hoix; iexists t; iexact Hto
    rw [list_set_lookup_self xs n _ hxn']
    have hn63 : (n : Int) < 2 ^ 63 := by have := Hlen.1; word
    wp_apply (hFix (Loc × w64) (interface.mk (go.GoType.PointerType LeaseQueue.ty)
        #(nF go!"queue" np)) (queueHeap (nF go!"queue" np)) queueElem xs (W64 (n : Int))
        (by word) (by word)) $$ [$Hheap $Hiface Hq Hs Hcap Hits] as ⟨%ys, Hys, %Hperm⟩
    · iunfold queueHeap; iexists s; iframe; iunfold queueAt; iframe
    iapply HΦ
    iunfold queueHeap at Hys
    icases Hys with ⟨%s', Hq', Hqa'⟩
    iunfold notifierAt
    iexists mp, s', M, ys
    iframe
    ipureintro
    constructor
    · exact (List.Perm.map Prod.fst Hperm).nodup_iff.mpr Hinv.1
    · intro id' p'; rw [Hinv.2 id' p']; exact Hperm.mem_iff.symm
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    icases queue_item_fresh xs item k $$ [$Hits $Hix] with ⟨Hits, Hix, %Hfresh⟩
    wp_auto
    wp_apply (hHPush (Loc × w64) (interface.mk (go.GoType.PointerType LeaseQueue.ty)
        #(nF go!"queue" np)) (queueHeap (nF go!"queue" np)) queueElem xs
        (interface.mkOk (go.GoType.PointerType LeaseWithTime.ty) #item) (item, id))
      $$ [$Hheap $Hiface Hq Hs Hcap Hits Ht Hix] as ⟨%ys, Hys, %Hperm⟩
    · isplitl [Hq Hs Hcap Hits]
      · iunfold queueHeap; iexists s; iframe; iunfold queueAt; iframe
      iunfold queueElem
      isplitr
      · ipureintro; rfl
      iexists k; iunfold lwtAt; iframe; iframe #
    (try wp_auto)
    wp_apply (wp_mapInsert LeaseID.ty mp M id item) $$ HM as HM
    iapply HΦ
    iunfold queueHeap at Hys
    icases Hys with ⟨%s', Hq', Hqa'⟩
    iunfold notifierAt
    iexists mp, s', _, ys
    iframe
    ipureintro
    constructor
    · refine (List.Perm.map Prod.fst Hperm).nodup_iff.mpr ?_
      simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.mpr ⟨Hinv.1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
        fun a ha b hb => by simp at hb; subst hb; intro h; exact Hfresh (h ▸ ha)⟩
    · intro id' p'
      rw [Hperm.mem_iff, GMap.lookup_insert_Some, List.mem_append, ← Hinv.2 id' p']
      simp only [List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨_, h⟩)
        · right; exact ⟨h2.symm, h1.symm⟩
        · left; exact h
      · rintro (h | ⟨h1, h2⟩)
        · right
          refine ⟨?_, h⟩
          rintro rfl; rw [hM] at h; cases h
        · left; exact ⟨h2.symm, h1.symm⟩

end proof

end EtcdGrove
end Perennial
