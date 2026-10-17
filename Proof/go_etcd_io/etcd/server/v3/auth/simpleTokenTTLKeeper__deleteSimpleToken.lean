/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/simpleTokenTTLKeeper__deleteSimpleToken.lean`.
Lean-first (no Rocq counterpart; PR etcd#22338).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__deleteSimpleToken

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

theorem auth.simpleTokenTTLKeeper.deleteSimpleToken.wp_proof :
    auth.simpleTokenTTLKeeper.deleteSimpleToken.spec (GF := GF) (hG := hG) := by
  intro tm tokens ttl lg m G x token
  wp_start as ⟨#Hro, Hm, #Hgm, HG⟩
  iunfold keeperRO at Hro
  icases Hro with ⟨#Htok, #Httl, #Hlg⟩
  iunfold gaugeModel at Hgm
  icases Hgm with ⟨%g, #Hgv, #Hset⟩
  wp_alloc tmv as Htmv
  wp_pures
  wp_alloc tokv as Htokv
  wp_pures
  wp_load
  wp_pures
  wp_load
  wp_pures
  wp_load
  wp_pures
  wp_apply (wp_mapDelete tokens m token go.string time.Time.ty) $$ Hm as Hm
  wp_pures
  wp_apply wp_map_len $$ Hm as Hm
  wp_pures
  wp_bind (App (Val #(methods g.ty go!"Set" g.v))
    (Val #(int64ToFloat64 (W64 (GMap.size (GMap.delete token m))))))
  iapply Hset $$ %x %(tokenCount (GMap.delete token m)) [HG]
  · iexact HG
  inext
  iintro HG
  wp_pures
  iapply HΦ
  iframe Hm
  iexact HG

end proof

end EtcdGrove
end Perennial
