/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__reset.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__reset
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__reset
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__reset

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

theorem backend.readTx.reset.wp_proof
    (hreset : backend.txReadBuffer.reset.spec (GF := GF) (hG := hG))
    (hst : backend.sharedBoltTx.reset.spec (GF := GF) (hG := hG)) :
    backend.readTx.reset.spec (GF := GF) (hG := hG) := by
  intro γ rt st R cm tx wg lg
  wp_start as ⟨Hrb, #Hst, Hcm, Htx, Hwg, Hr⟩
  wp_auto
  wp_apply hreset $$ [$Hrb] as Hrb
  wp_apply hst γ st cm tx wg lg $$ [$Hcm $Htx $Hwg $Hr] as %cm' %wg' ⟨Hcm, Hcm0, Htx, Hwg, Hwg0⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
