/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/hr3/run.lean (241f27e),
`inmem_isLogStore`.
-/
/-
`*InmemStore` as raft's log store (`isLogStore`, `iface/Stores.lean`), its contents `inmemLogs γs`, from
the methods' specs (hypotheses): the store's specs are the contract's clauses.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__LastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__FirstIndex
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__GetLog
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__StoreLogs
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__StoreLog
public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__DeleteRange

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

/-- **`*InmemStore` is a log store**, its contents `inmemLogs γs`. -/
theorem inmem_isLogStore
    (wp_LastIndex : github_com.hashicorp.raft.InmemStore.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : github_com.hashicorp.raft.InmemStore.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_GetLog : github_com.hashicorp.raft.InmemStore.GetLog.spec (GF := GF) (hG := hG))
    (wp_StoreLogs : github_com.hashicorp.raft.InmemStore.StoreLogs.spec (GF := GF) (hG := hG))
    (wp_StoreLog : github_com.hashicorp.raft.InmemStore.StoreLog.spec (GF := GF) (hG := hG))
    (wp_DeleteRange : github_com.hashicorp.raft.InmemStore.DeleteRange.spec (GF := GF) (hG := hG))
    (γs : InmemNames) (i : Loc) :
    isInmemStore (GF := GF) γs i ⊢
      isLogStore (interface.mk (go.GoType.PointerType InmemStore.ty) #i) (inmemLogs γs) := by
  iintro #His
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ [His]
  · unfold isInmemStore; iNamed His; iexact Hinit
  unfold isLogStore
  isplitr
  · imodintro
    iintro %tid %Φ Htok HAU
    iapply (wp_LastIndex γs i tid) $$ [Htok] HAU
    iframe; iframe #
  isplitr
  · imodintro
    iintro %tid %Φ Htok HΦ
    iapply (wp_FirstIndex γs i tid) $$ [Htok] HΦ
    iframe; iframe #
  isplitr
  · imodintro
    iintro %idx %ptr %lv0 %tid %Φ Hptr Htok HAU
    iapply (wp_GetLog γs i idx ptr lv0 tid) $$ [Hptr Htok] HAU
    iframe; iframe #
  isplitr
  · -- no window: `W` goes to the atomic update at once
    imodintro
    iintro %sl %dq %ptrs %first %es %W %Φ %Hlen Hsl Hptrs HW HAU
    iapply (wp_StoreLogs γs i sl dq ptrs first es) $$ [Hsl Hptrs] [HW HAU]
    · iframe; iframe #; ipureintro; exact ⟨Hlen.1, by omega⟩
    · iapply HAU $$ HW
  isplitr
  · imodintro
    iintro %p %first %e %W %Φ %Hf #Hp HW HAU
    iapply (wp_StoreLog γs i p first e) $$ [] [HW HAU]
    · iframe #; ipureintro; exact Hf
    · iapply HAU $$ HW
  isplitr
  · imodintro
    iintro %mn %mx %W %Φ %Hmx HW HAU
    iapply (wp_DeleteRange γs i mn mx) $$ [] [HW HAU]
    · iframe #; ipureintro; exact Hmx
    · iapply HAU $$ HW
  · -- `*InmemStore` is not a `CommitTrackingLogStore`
    ileft
    ipureintro
    go_type_set

end iface

end github_com.hashicorp.raft

end Perennial
