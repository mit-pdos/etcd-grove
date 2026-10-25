/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/defragmentedSnapshot__Size.lean`
(`etcd#21776`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.defragmentedSnapshot__Size
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Size

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

theorem backend.defragmentedSnapshot.Size.wp_proof
    (hSize : backend.snapshot.Size.spec (GF := GF) (hG := hG)) :
    backend.defragmentedSnapshot.Size.spec (GF := GF) (hG := hG) := by
  intro ds D γ q
  wp_start as Hds
  iunfold defragSnapOpenQ at Hds
  icases Hds with ⟨Hs, Hg, %cl, #Hcl, #Hwp⟩
  wp_apply (hSize (dsSnapOf ds) D γ.1 q) $$ [Hs] as %n Hs
  · iframe #; iframe Hs
  iapply HΦ
  iunfold defragSnapOpenQ
  iframe Hs Hg Hcl Hwp

end proof

end EtcdGrove
end Perennial
