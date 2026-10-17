/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/simpleTokenTTLKeeper__addSimpleToken.lean`.
Lean-first (no Rocq counterpart; PR etcd#22338).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__addSimpleToken
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn

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

theorem auth.simpleTokenTTLKeeper.addSimpleToken.wp_proof
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    auth.simpleTokenTTLKeeper.addSimpleToken.spec (GF := GF) (hG := hG) := by
  intro tm tokens ttl lg m G x token
  wp_start as ⟨#Hro, Hm, #Hgm, HG⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
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
  wp_apply time.wp_Now as %now -
  wp_pures
  wp_apply time.Time.wp_Add as %e -
  wp_pures
  wp_apply (wp_mapInsert go.string tokens m token e) $$ Hm as Hm
  wp_pures
  wp_apply wp_map_len_lt $$ Hm as ⟨Hm, %Hsz⟩
  wp_pures
  wp_bind (App (Val #(methods g.ty go!"Set" g.v))
    (Val #(int64ToFloat64 (W64 (GMap.size (<[token := e]> m))))))
  iapply Hset $$ %x %(tokenCount (<[token := e]> m)) [HG]
  · iexact HG
  inext
  iintro HG
  wp_pures
  wp_load
  wp_pures
  have hpos : 0 < GMap.size (<[token := e]> m) :=
    GMap.map_size_nonzero _ token (by simp [GMap.lookup_insert_eq])
  have hz : sint.Z (W64 0) < sint.Z (W64 (GMap.size (<[token := e]> m))) := by word
  rw [decide_eq_true hz]
  wp_pures
  wp_load
  wp_pures
  by_cases hw : BitVec.srem (W64 (GMap.size (<[token := e]> m))) (W64 10000) = W64 0
  · rw [decide_eq_true hw]
    wp_pures
    by_cases hlg : lg = null
    · subst hlg
      wp_load
      wp_pures
      wp_load
      wp_pures
      iapply HΦ
      iexists e
      iframe Hm
      iexact HG
    · wp_load
      wp_pures
      wp_load
      wp_pures
      rw [decide_eq_false hlg]
      wp_pures
      wp_load
      wp_pures
      wp_apply h_Int _ _ as %f1 -
      wp_pures
      wp_apply h_Duration _ _ as %f2 -
      wp_pures
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      wp_pures
      wp_load
      wp_pures
      wp_load
      wp_pures
      wp_apply h_Warn lg _ _ $$ []
      · ipureintro; exact hlg
      wp_pures
      iapply HΦ
      iexists e
      iframe Hm
      iexact HG
  · rw [decide_eq_false hw]
    wp_pures
    iapply HΦ
    iexists e
    iframe Hm
    iexact HG

end proof

end EtcdGrove
end Perennial
