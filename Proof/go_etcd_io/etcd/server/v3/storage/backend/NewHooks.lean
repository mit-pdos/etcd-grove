/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/NewHooks.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.NewHooks
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

theorem backend.NewHooks.wp_proof
    (hOn : backend.hooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG)) :
    backend.NewHooks.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t f
  wp_start as #Hf
  wp_auto
  iapply HΦ
  unfold hooksSpec
  iright
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %st !> %Φ' Hpre HΦ'
  iapply (hOn γ P WR b t ⟨f⟩ st) $$ [Hpre] HΦ'
  icases Hpre with ⟨Hl, HWR⟩
  iframe
  iframe Hf
  iPkgInit

end proof

end EtcdGrove
end Perennial
