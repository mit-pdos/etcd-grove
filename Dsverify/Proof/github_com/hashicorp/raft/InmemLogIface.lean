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
    (γs : InmemNames) (i : Loc) (Wl : LogOp → IProp GF) :
    isInmemStore (GF := GF) γs i ⊢
      isLogStore (interface.mk (go.GoType.PointerType InmemStore.ty) #i) (inmemLogs γs) Wl := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end iface

end github_com.hashicorp.raft

end Perennial
