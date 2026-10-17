/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/sharedBoltTx__finishWait.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__finishWait
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.sharedBoltTx.finishWait.wp_proof :
    backend.sharedBoltTx.finishWait.spec (GF := GF) (hG := hG) := by
  intro γ st dq rtx wg γw γo γt k q
  wp_start as ⟨Hwg, #Hwgi, Hsh⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_rdDone γ rtx wg γw γo γt k q $$ [$Hsync $Hwgi $Hsh] as Htok
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
