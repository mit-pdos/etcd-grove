/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__tick.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__tick
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.tick.wp_proof : raftNode.tick.spec (GF := GF) (hG := hG) := by
  intro E γ r
  wp_start as ⟨#Hr, HT⟩
  iunfold isRaftNode at Hr
  iNamed Hr
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, #HReady, #HAdv, #HTick, #HStop⟩
  subst Hnieq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard mu (rnTickInv r) $$ [$Hsync $Hmug] as ⟨Hl, HP⟩
  wp_apply HTick $$ [$HT]
  wp_apply time.wp_Now as %t -
  iunfold rnTickInv at HP
  icases HP with ⟨%t0, Hts⟩
  wp_auto
  wp_apply sync.RWMutex.wp_Unlock_guard mu (rnTickInv r) $$ [$Hsync $Hl Hts]
  · iunfold rnTickInv
    iexists t
    iexact Hts
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
