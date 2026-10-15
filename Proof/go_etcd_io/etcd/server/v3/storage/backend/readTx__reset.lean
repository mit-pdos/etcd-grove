/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__reset.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__reset
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__reset

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
    (hreset : backend.txReadBuffer.reset.spec (GF := GF) (hG := hG)) :
    backend.readTx.reset.spec (GF := GF) (hG := hG) := by
  intro rt R cm tx wg
  wp_start as ⟨Hrb, Hcm, Htx, Hwg⟩
  wp_auto
  wp_apply hreset $$ [$Hrb] as Hrb
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %m Hm
  iapply HΦ
  iframe


end proof

end EtcdGrove
end Perennial
