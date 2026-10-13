/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/hooks__OnPreCommitUnsafe.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.hooks__OnPreCommitUnsafe

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

theorem backend.hooks.OnPreCommitUnsafe.wp_proof :
    backend.hooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG) := by
  intro γ P Pk b t h st
  wp_start as ⟨#Hf, Hl, HWR⟩
  wp_auto
  unfold hookFnSpec
  wp_apply Hf $$ %st [$Hl $HWR] as ⟨%st', Hl, HWR, %Hs⟩
  iapply HΦ
  iexists st'
  iframe
  ipureintro
  exact Hs

end proof

end EtcdGrove
end Perennial
