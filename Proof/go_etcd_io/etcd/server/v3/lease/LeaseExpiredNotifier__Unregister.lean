/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseExpiredNotifier__Unregister.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Unregister
public import Proof.go_etcd_io.etcd.server.v3.lease.QueuePop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseExpiredNotifier.Unregister.wp_proof
    (hLen : lease.LeaseQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.LeaseQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.LeaseQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : lease.LeaseQueue.Push.spec (GF := GF) (hG := hG))
    (hPop : lease.LeaseQueue.Pop.spec (GF := GF) (hG := hG))
    (hHPop : heap.Pop.spec (GF := GF) (hG := hG)) :
    lease.LeaseExpiredNotifier.Unregister.spec (GF := GF) (hG := hG) := by
  intro np M hM
  wp_start as Hn
  ihave #Hheap : isPkgInit (PROP := IProp GF) pkg_id.container.heap $$ []
  · iPkgInit
  ihave #Hiface := queue_heapIface hLen hLess hSwap hPush (nF go!"queue" np) $$ Hpkg
  ihave #HifaceP := queue_heapPopIface hPop (nF go!"queue" np) $$ Hpkg
  iunfold notifierAtM at Hn
  icases Hn with ⟨%mp, %s, %xs, Hm, HM, Hq, Hqa, %Hinv⟩
  have hxs : xs ≠ [] := by
    intro hx
    apply hM
    apply (GMap.lookup_empty_iff M).1
    intro k
    cases hk : M !! k with
    | none => rfl
    | some p => have := (Hinv.2 k p).1 hk; rw [hx] at this; cases this
  wp_auto
  wp_apply (hHPop (Loc × w64) (interface.mk (go.GoType.PointerType LeaseQueue.ty)
      #(nF go!"queue" np)) (queueHeap (nF go!"queue" np)) queueElem xs hxs)
    $$ [$Hheap $Hiface $HifaceP Hq Hqa] as %x ⟨%ys, %a, Hys, Hx, %Hperm⟩
  · iunfold queueHeap; iexists s; iframe
  iunfold queueElem at Hx
  icases Hx with ⟨%Hx, %k, Hit⟩
  subst Hx
  iunfold lwtAt at Hit
  icases Hit with ⟨#Hid, Ht, Hix⟩
  wp_auto
  wp_apply (wp_mapDelete mp M a.2 LeaseID.ty (go.GoType.PointerType LeaseWithTime.ty)) $$ HM as HM
  (try wp_auto)
  iapply HΦ
  iunfold queueHeap at Hys
  icases Hys with ⟨%s', Hq', Hqa'⟩
  have hmem : (a.1, a.2) ∈ xs := Hperm.mem_iff.mp (by simp)
  have hnd : ((ys ++ [a]).map Prod.fst).Nodup := (List.Perm.map Prod.fst Hperm).nodup_iff.mpr Hinv.1
  ihave Hit : lwtAt (GF := GF) a.1 a.2 k 1 $$ [Ht Hix]
  · iunfold lwtAt; iframe Hid Ht Hix
  iexists a.2, k
  iframe Hit
  isplitr
  · ipureintro; exact (Hinv.2 a.2 a.1).2 hmem
  iunfold notifierAtM
  iexists mp, s', ys
  iframe
  ipureintro
  constructor
  · exact (List.nodup_append.mp (by simpa using hnd)).1
  · intro id' p'
    have hnd' : (a.1 :: ys.map Prod.fst).Nodup := by
      have := (List.perm_append_singleton a.1 (ys.map Prod.fst))
      exact (this.nodup_iff).mp (by simpa using hnd)
    rw [GMap.lookup_delete_Some, Hinv.2 id' p', ← Hperm.mem_iff, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨hne, h | h⟩
      · exact h
      · cases h; exact absurd rfl hne
    · intro h
      refine ⟨?_, Or.inl h⟩
      rintro rfl
      -- `(p', a.2)` and `a` are two items of one id: one item per id (`Hinv`)
      have h1 := (Hinv.2 a.2 p').2 (Hperm.mem_iff.mp (by simp [h]))
      have h2 := (Hinv.2 a.2 a.1).2 hmem
      rw [h1] at h2
      cases h2
      exact (List.nodup_cons.mp hnd').1 (List.mem_map.mpr ⟨_, h, rfl⟩)

end proof

end EtcdGrove
end Perennial
