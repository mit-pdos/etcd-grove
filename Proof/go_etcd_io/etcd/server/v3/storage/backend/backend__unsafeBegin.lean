/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__unsafeBegin.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__unsafeBegin
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__unsafeBegin
public import Spec.go_etcd_io.bbolt.DB__Begin_kv
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.backend.unsafeBegin.wp_proof
    (hBegin : bbolt.DB.Begin_kv.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    backend.backend.unsafeBegin.spec (GF := GF) (hG := hG) := by
  intro γ P WR b db q D w
  wp_start as ⟨#Hb, Hdb, Hown, Hwr⟩
  icases isBackend_b γ P WR b $$ Hb with
    ⟨%t, %rt, %db0, %lg, #-, #-, #Hlg, %Hlgn, #-⟩
  wp_auto
  wp_apply (hBegin db γ.db D w) $$ [$Hown $Hwr] as %tx %err ⟨Hown, #Hisdb, Hr⟩
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, #Htxdb, Htx⟩)
  · rcases err with ei | _
    · wp_auto
      wp_apply hError as %f -
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      try iintro %_ ⟨_, -⟩
      try wp_auto
      wp_apply hFatal lg $$ [] as %v Hf
      · ipureintro; exact Hlgn
      iexfalso
      iexact Hf
    · exact absurd rfl Herr
  · subst Herr
    wp_auto
    iapply HΦ
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
