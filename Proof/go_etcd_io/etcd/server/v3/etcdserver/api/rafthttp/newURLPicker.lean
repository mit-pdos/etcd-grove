/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/newURLPicker.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newURLPicker

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.newURLPicker.wp_proof :
    rafthttp.newURLPicker.spec (GF := GF) (hG := hG) := by
  intro urls us P Hne HP
  wp_start as #Hus
  wp_auto
  wp_alloc pk as Hpk
  iStructNamed Hpk
  imod sync.init_Mutex (pickerInv pk P) ⊤
    (pk.[rafthttp.urlPicker, go!"mu"]) $$ mu [urls picked] with #Hmu
  · inext
    iunfold pickerInv
    iexists urls, us, _
    iframe; iframe #
    ipureintro
    refine ⟨by decide, ?_, HP⟩
    have : 0 < us.length := List.length_pos_iff.2 Hne
    simp; omega
  (try wp_auto)
  iapply HΦ
  iunfold pickerOk
  iexact Hmu

end proof

end EtcdGrove
end Perennial
