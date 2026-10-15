/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__isLeader.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Lead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.isLeader.wp_proof (hM : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hL : EtcdServer.Lead.spec (GF := GF) (hG := hG)) :
    EtcdServer.isLeader.spec (GF := GF) (hG := hG) := by
  intro s id
  wp_start as ⟨#Hid, #Hl⟩
  (try wp_auto)
  wp_apply hM s id
  · iexact Hid
  wp_apply hL s as %v -
  · iexact Hl
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
