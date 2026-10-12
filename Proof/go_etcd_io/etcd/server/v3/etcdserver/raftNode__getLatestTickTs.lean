/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__getLatestTickTs.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__getLatestTickTs

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

theorem raftNode.getLatestTickTs.wp_proof :
    raftNode.getLatestTickTs.spec (GF := GF) (hG := hG) := by
  intro E γ r mu
  wp_start as ⟨#Hr, #Hmu', Hown⟩
  iunfold isRaftNode at Hr
  iNamed Hr
  icombine Hmu Hmu' gives %Heq
  subst Heq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_RLock mu (rnTickInv r) $$ [$Hsync $Hown] as ⟨Hl, HP⟩
  iunfold rnTickInv at HP
  icases HP with ⟨%t, Hts⟩
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock mu (rnTickInv r) $$ [$Hsync $Hl Hts] as Hown
  · iunfold rnTickInv
    iexists t
    iexact Hts
  iapply HΦ
  iexact Hown

end proof

end EtcdGrove
end Perennial
