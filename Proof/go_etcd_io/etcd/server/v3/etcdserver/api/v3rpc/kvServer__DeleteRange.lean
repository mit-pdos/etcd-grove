/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkDeleteRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.kvServer.DeleteRange.wp_proof
    (hChk : v3rpc.checkDeleteRequest.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG)) :
    v3rpc.kvServer.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid n ctx r o
  wp_start as ⟨#Hsrv, Hcall, #Hr, %Hpre⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.kvServerIs at Hsrv'
  icases Hsrv' with ⟨%Hpn, #Hhdr, #Hkv, #Hn, #HKV⟩
  iunfold v3rpc.raftKV at HKV
  icases HKV with ⟨-, -, #HPut, -, -⟩
  iunfold v3rpc.kvDeleteOk at HPut
  wp_auto
  wp_apply hChk $$ [] as %err #Herr
  · iframe #
  cases hc : v3rpc.deleteCheck o with
  | some e =>
    simp only [v3rpc.checkRes]
    iunfold txn.errVarIs at Herr
    icases Herr with ⟨%ee, #Hee, %Herr⟩
    subst Herr
    wp_auto
    iapply HΦ
    iframe Hcall
    iunfold v3rpc.checkOut
    iunfold txn.errVarIs
    iframe #
    ipureintro; exact ⟨rfl, rfl⟩
  | none =>
    try simp only [v3rpc.checkRes]
    icases Herr with %Herr
    subst Herr
    wp_auto
    wp_apply HPut $$ [Hcall] as %resp %err' Hans
    · iframe; iframe #; ipureintro; exact ⟨hc, Hpre⟩
    iunfold v3rpc.kvAnswer at Hans
    icases Hans with (⟨%Hok, %h, %rv, #Hhf, Hw, Hrev, HA⟩ | ⟨#Hse, HA⟩)
    · obtain ⟨He, Hrn⟩ := Hok
      subst He
      wp_auto
      wp_apply hFill $$ [Hw Hrev] as ⟨Hf, %rv', Hrev'⟩
      · iframe; iframe #
      wp_auto
      iapply HΦ
      iunfold v3rpc.kvOut
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn⟩
      iexists h, rv, rv'
      iframe
      iframe #
    · ihave #Hse' := Hse
      iunfold v3rpc.srvErrIs at Hse'
      icases Hse' with ⟨%Hen, -⟩
      cases err' with
      | nil => exact absurd rfl Hen
      | ok ei =>
        wp_auto
        wp_apply hTog $$ [] as %e %He
        · iframe #
        iapply HΦ
        iunfold v3rpc.kvOut
        iright
        isplitr
        · ipureintro; exact ⟨rfl, He⟩
        iexists _
        iexact HA

end proof

end EtcdGrove
end Perennial
