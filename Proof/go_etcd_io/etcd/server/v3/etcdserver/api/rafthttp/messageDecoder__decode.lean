/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/messageDecoder__decode.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder__decode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder__decodeLimit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.messageDecoder.decode.wp_proof
    (hLimit : rafthttp.messageDecoder.decodeLimit.spec (GF := GF) (hG := hG)) :
    rafthttp.messageDecoder.decode.spec (GF := GF) (hG := hG) := by
  intro dec r Rd B rs
  wp_start as ⟨#Hr, #Hrf, HRd, #HV⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HRBL, -⟩
  wp_auto
  wp_apply hLimit dec r Rd B rs (W64 536870912) (by decide) $$ [HRd]
    as %ml %err ⟨#Herr, %rs', HRd, Hok⟩
  · iframe; iframe #
  iapply HΦ
  iframe Herr
  iexists rs'
  iframe HRd
  iintro %Hnil
  ihave ⟨%bs, %st, %Hb, #HB, Hm⟩ := Hok $$ %Hnil
  iexists bs, st
  iframe Hm HB
  ipureintro
  exact ⟨Hb.1, by have := Hb.2.1; simpa using this, Hb.2.2⟩

end proof

end EtcdGrove
end Perennial
