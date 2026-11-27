/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStoreIface.lean (241f27e).
-/
/-
The interface contracts (`iface/Stores.lean`) for `*InmemStore` (as the stable store) and
`*InmemSnapshotStore` (as the snapshot store), from the methods' specs (taken as hypotheses, so
that a caller's `wp_proof` takes the specs and gen-link instantiates them).

Two contract statements cannot be met as written (see the report); this file states the revised
clauses and proves them:
* `isStableStore`: `isStableStore` with `Get`'s found case not assuming non-empty contents
  (`Set` of a non-nil empty slice is then found by `Get`, as `[]`: the code tests `val == nil`).
  The other three clauses are exactly `isStableStore`'s.
* `isSnapshotStore`: `isSnapshotStore` whose `List` takes the calling thread's quarter token `rtok tid` and
  gives it back (`List` takes a read lock: its reader token has to be paid for).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__GetUint64
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__SetUint64
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__Get
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__Set
public import Dsverify.Spec.github_com.hashicorp.raft.InmemSnapshotStore__List

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

section iface
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- **`*InmemStore` is a stable store**, its contents the view `kvView γs`. -/
theorem inmem_isStableStore
    (wp_GetUint64 : github_com.hashicorp.raft.InmemStore.GetUint64.spec (GF := GF) (hG := hG))
    (wp_SetUint64 : github_com.hashicorp.raft.InmemStore.SetUint64.spec (GF := GF) (hG := hG))
    (wp_Get : github_com.hashicorp.raft.InmemStore.Get.spec (GF := GF) (hG := hG))
    (wp_Set : github_com.hashicorp.raft.InmemStore.Set.spec (GF := GF) (hG := hG))
    (γs : InmemNames) (i : Loc) :
    isInmemStore (GF := GF) γs i ⊢
      isStableStore (interface.mk (go.GoType.PointerType InmemStore.ty) #i) (kvView γs) := by
  iintro #His
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ [His]
  · unfold isInmemStore; iNamed His; iexact Hinit
  unfold isStableStore
  isplitr
  · imodintro
    iintro %st %key %kb %tid %Φ Hown #Hkey Htok HΦ
    iapply (wp_GetUint64 γs i st key kb tid) $$ [Hown Htok] HΦ
    iframe; iframe #
  isplitr
  · imodintro
    iintro %st %key %kb %v %Φ Hown #Hkey HΦ
    iapply (wp_SetUint64 γs i st key kb v) $$ [Hown] HΦ
    iframe; iframe #
  isplitr
  · imodintro
    iintro %st %key %kb %tid %Φ Hown #Hkey Htok HΦ
    iapply (wp_Get γs i st key kb tid) $$ [Hown Htok] HΦ
    iframe; iframe #
  · imodintro
    iintro %st %key %vs %kb %vb %Φ Hown #Hkey #Hvs HΦ
    iapply (wp_Set γs i st key vs kb vb) $$ [Hown] HΦ
    iframe; iframe #

/-- **`*InmemSnapshotStore` is a snapshot store** (no snapshot). -/
theorem inmem_isSnapshotStore
    (wp_List : github_com.hashicorp.raft.InmemSnapshotStore.List.spec (GF := GF) (hG := hG))
    (m : Loc) :
    isInmemSnapshotStore (GF := GF) m ⊢
      isSnapshotStore (interface.mk (go.GoType.PointerType InmemSnapshotStore.ty) #m) := by
  iintro #His
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ [His]
  · unfold isInmemSnapshotStore; iNamed His; iexact Hinit
  unfold isSnapshotStore
  imodintro
  iintro %tid %Φ Htok HΦ
  iapply (wp_List m tid) $$ [Htok] HΦ
  iframe; iframe #

end iface

end github_com.hashicorp.raft

end Perennial
