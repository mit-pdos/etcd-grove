/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ForceSnapshot.lean`. Lean-first
(no Rocq counterpart); D14i (2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ForceSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.ForceSnapshot.wp_proof : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as Hfs
  iunfold srvFS at Hfs
  icases Hfs with ⟨%f, Hf⟩
  wp_auto
  iapply HΦ
  iunfold srvFS
  iexists _
  iexact Hf

end proof

end EtcdGrove
end Perennial
