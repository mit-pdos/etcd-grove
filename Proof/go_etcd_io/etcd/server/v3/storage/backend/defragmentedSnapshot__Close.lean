/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/defragmentedSnapshot__Close.lean`
(`etcd#21776`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.defragmentedSnapshot__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Close

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

theorem backend.defragmentedSnapshot.Close.wp_proof
    (hClose : backend.snapshot.Close.spec (GF := GF) (hG := hG)) :
    backend.defragmentedSnapshot.Close.spec (GF := GF) (hG := hG) := by
  intro ds D γ
  wp_start as Hds
  iunfold defragSnapOpenQ at Hds
  icases Hds with ⟨Hs, Hg, %cl, #Hcl, #Hwp⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply (hClose (dsSnapOf ds) D γ.1) $$ [Hs]
  · iframe #; iframe Hs
  wp_bind (App (Val #cl) (Val #()))
  iapply Hwp $$ [Hg]
  · iexact Hg
  inext
  iintro -
  (try wp_auto)
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
