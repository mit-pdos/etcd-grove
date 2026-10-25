/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/defragmentedSnapshot__WriteTo.lean`
(`etcd#21776`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.defragmentedSnapshot__WriteTo
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__WriteTo

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

theorem backend.defragmentedSnapshot.WriteTo.wp_proof
    (hWT : backend.snapshot.WriteTo.spec (GF := GF) (hG := hG)) :
    backend.defragmentedSnapshot.WriteTo.spec (GF := GF) (hG := hG) := by
  intro ds D γ q w Wr c bs₀
  wp_start as ⟨Hds, #Hwok, Hw⟩
  iunfold defragSnapOpenQ at Hds
  icases Hds with ⟨Hs, Hg, %cl, #Hcl, #Hwp⟩
  wp_apply (hWT (dsSnapOf ds) D γ.1 q w Wr c bs₀) $$ [Hs Hw] as %n %err ⟨%bs, Hs, Hw, %Himg⟩
  · iframe #; iframe Hs Hw
  iapply HΦ
  iexists bs
  iunfold defragSnapOpenQ
  iframe Hs Hg Hcl Hwp Hw
  ipureintro
  exact Himg

end proof

end EtcdGrove
end Perennial
