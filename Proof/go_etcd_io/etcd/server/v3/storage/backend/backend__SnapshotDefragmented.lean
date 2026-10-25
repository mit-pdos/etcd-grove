/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__SnapshotDefragmented.lean`
(`etcd#21776`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SnapshotDefragmented
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__snapshotDefragmented

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

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

theorem backend.backend.SnapshotDefragmented.wp_proof
    (hSnapDefrag : backend.backend.snapshotDefragmented.spec (GF := GF) (hG := hG)) :
    backend.backend.SnapshotDefragmented.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b qo R Q
  wp_start as ⟨#Hb, Ho, Hwb, HR, #HQ⟩
  wp_auto
  wp_apply (hSnapDefrag γ P W Pk b (W64 16777216) qo R Q (by decide))
    $$ [Ho Hwb HR] as %s %err ⟨Ho, HR, Hres⟩
  · iframe #; iframe Ho Hwb HR
  iapply HΦ
  iframe Ho HR Hres

end proof

end EtcdGrove
end Perennial
