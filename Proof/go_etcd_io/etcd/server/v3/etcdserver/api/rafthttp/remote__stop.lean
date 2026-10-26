/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/remote__stop.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.remote.stop.wp_proof
    (hPipeStop : rafthttp.pipeline.stop.spec (GF := GF) (hG := hG)) :
    rafthttp.remote.stop.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid R g
  wp_start as ⟨-, Hst⟩
  iunfold remoteStop at Hst
  icases Hst with ⟨%pl, #Hpl, Hpls⟩
  wp_auto
  wp_apply hPipeStop Rh pl pid R $$ [Hpls] as ⟨HR1, HR2, HR3, HR4⟩
  · iframe #; iframe
  (try wp_auto)
  iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
