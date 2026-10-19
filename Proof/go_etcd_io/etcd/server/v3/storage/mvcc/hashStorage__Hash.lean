/-
Proof of `Spec/.../mvcc/hashStorage__Hash.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Hash
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__hash

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

theorem mvcc.hashStorage.Hash.wp_proof (hHash : mvcc.store.hash.spec (GF := GF) (hG := hG)) :
    mvcc.hashStorage.Hash.spec (GF := GF) (hG := hG) := by
  intro hs s γ log₀
  wp_start as ⟨#Hst, #Hs, #Hho, Hrd, Hwt, #Hc0⟩
  (try wp_auto)
  wp_apply hHash s γ log₀ $$ [$Hrd $Hwt] as %h %rev %err ⟨Hrd, Hpost⟩
  · iframe #
  (try wp_auto)
  iapply HΦ
  iframe Hrd Hpost

end proof

end EtcdGrove
end Perennial
