/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressAll
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressIfSync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchableStore.progressAll.wp_proof
    (hPIS : mvcc.watchableStore.progressIfSync.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.progressAll.spec (GF := GF) (hG := hG) := by
  intro s st γ m dq M γc
  wp_start as ⟨#Hws, Hm, #HM, #Hpf, HR⟩
  wp_auto
  wp_apply (hPIS s st γ m dq M _ γc) $$ [$Hws $Hm $HR] as %b ⟨Hm, HR⟩
  · iintro !> %id %w %hw
    icases HM $$ %id %w %hw with ⟨#HIW, #HOC⟩
    iframe HIW
    simp only [mvcc.storeWatchParams] at *
    icases HOC with ⟨%γw, #Hm, %Hwc⟩
    icases HIW with ⟨%γw', %r, %fcs, -, #Hf, -⟩
    iexists γw, r, fcs
    iframe Hm Hf
    isplitr
    · ipureintro; exact Hwc
    iright
    rw [Hwc]
    iexact Hpf
  (try wp_auto)
  iapply HΦ
  iframe Hm HR

end proof

end EtcdGrove
end Perennial
