/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fillWithoutRevision

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

theorem v3rpc.header.fill.wp_proof
    (hFWR : v3rpc.header.fillWithoutRevision.spec (GF := GF) (hG := hG)) :
    v3rpc.header.fill.spec (GF := GF) (hG := hG) := by
  intro hp s A cid mid rh r
  wp_start as ⟨#Hhdr, Hw, Hr⟩
  ihave #Hhdr' := Hhdr
  iunfold v3rpc.hdrIs at Hhdr'
  icases Hhdr' with ⟨%revf, -, -, -, #Hrev, #HrevS, -⟩
  wp_auto
  wp_apply hFWR $$ [Hw] as Hf
  · iframe; iframe #
  iunfold v3rpc.hdrRevIn at Hr
  icases Hr with (⟨%Hr0, #Hr⟩ | ⟨Hr, HR⟩)
  · wp_auto
    wp_if_destruct
    · exact absurd rfl Hr0
    · iapply HΦ
      iframe Hf
      iexists r
      iunfold v3rpc.hdrRevOut
      ileft
      iframe Hr
      ipureintro; exact ⟨Hr0, rfl⟩
  · wp_auto
    wp_if_destruct
    · wp_apply HrevS $$ HR as %rv HR
      iapply HΦ
      iframe Hf
      iexists rv
      iunfold v3rpc.hdrRevOut
      iright
      iframe
      ipureintro; intro h; exact absurd rfl h
    · iapply HΦ
      iframe Hf
      iexists r
      iunfold v3rpc.hdrRevOut
      iright
      iframe
      ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial
