/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/simpleTokenTTLKeeper__resetSimpleToken.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__resetSimpleToken

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.simpleTokenTTLKeeper.resetSimpleToken.wp_proof :
    auth.simpleTokenTTLKeeper.resetSimpleToken.spec (GF := GF) (hG := hG) := fun k d tk => by
  wp_start as ⟨Hk, #Hd⟩
  iunfold keeperMap at Hk
  icases Hk with ⟨%m, %M, Hf, Hm⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hm] as Hm
  wp_if_destruct
  · wp_apply time.wp_Now as %now -
    wp_apply time.Time.wp_Add as %t' -
    wp_apply wp_mapInsert $$ [$Hm] as Hm
    iapply HΦ
    iunfold keeperMap
    iexists _, _
    iframe
  · iapply HΦ
    iunfold keeperMap
    iexists _, _
    iframe

end proof

end EtcdGrove
end Perennial
