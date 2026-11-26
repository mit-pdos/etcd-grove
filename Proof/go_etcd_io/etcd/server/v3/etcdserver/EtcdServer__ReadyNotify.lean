/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ReadyNotify.lean`. Lean-first (no Rocq
counterpart); etcd-dist N5 (`notes/etcd-dist-plan.md` §19): `return s.readych`, from the receiver's share
(`srvReadyRecv`: the field, read-only, and the broadcast idiom's persistent part of the channel).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReadyNotify

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.ReadyNotify.wp_proof : EtcdServer.ReadyNotify.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as Hr
  iunfold srvReadyRecv at Hr
  icases Hr with ⟨%rdc, %γ, #Hf, #Hc⟩
  wp_auto
  iapply HΦ
  iexists γ
  iexact Hc

end proof

end EtcdGrove
end Perennial
