/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/tokenJWT__info.lean` (PR etcd#21909). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenJWT__info
public import Spec.github_com.golang_jwt.jwt.v5.Parse
public import Spec.go_etcd_io.etcd.server.v3.auth.tokenJWT__keyFunc
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth jwt go_uber_org

-- A failing branch of `info`: `t.lg.Warn(...)`, then `return nil, false`.
set_option hygiene false in
local macro "jwt_fail" : tactic => `(tactic| (
  wp_apply wp_Warn
  · ipureintro; exact Hlgn
  (try wp_auto)
  iapply HΦ
  isplit
  · iunfold authInfoRO; ileft; ipureintro; rfl
  · iunfold jwtInfoOk; ileft; ipureintro; exact ⟨rfl, rfl⟩))

-- A succeeding branch of `info`: the `AuthInfo` `a` allocated (`Ha`), made read-only.
set_option hygiene false in
local macro "jwt_ok" Ha:ident : tactic => `(tactic| (
  ipersist $Ha:ident
  ihave %Hna := typedPointsto_not_null _ _ _ $$ $Ha:ident
  iStructNamed $Ha:ident
  wp_auto
  iapply HΦ
  isplit
  · iunfold authInfoRO; iright; iexists _, _; iframe Username Revision
    ipureintro; exact Hna
  iunfold jwtInfoOk; iright; isplitr
  · ipureintro; exact ⟨rfl, Hna⟩))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.tokenJWT.info.wp_proof
    (wp_Parse : jwt.Parse.spec (GF := GF) (hG := hG))
    (wp_keyFunc : auth.tokenJWT.keyFunc.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    auth.tokenJWT.info.spec (GF := GF) (hG := hG) := by
  intro t vo ctx token rev
  wp_start as #Ht
  ihave #Ht0 := Ht
  iunfold jwtProviderRO at Ht
  icases Ht with ⟨%Htn, ⟨%lg, #Hlg, %Hlgn⟩, -, -, #Hvo⟩
  ihave #Hjwt : isPkgInit (PROP := IProp GF) pkg_id.github_com.golang_jwt.jwt.v5 $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Parse as %p %err Hp
  · imodintro
    iintro %tok !> %Φ' - HΦ'
    wp_apply wp_keyFunc t vo tok $$ [$Hpkg $Ht0] as %k %e -
    iapply HΦ'; itrivial
  icases Hp with (%Herr | ⟨%Herr, Hp⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
    wp_auto
    wp_apply wp_Error $$ [$Hzap] as %fe -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fe]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    jwt_fail
  · subst Herr
    iunfold jwtTokenRO at Hp
    icases Hp with ⟨%Hpn, %cl, %valid, #Hcl, #Hvalid, #Hclok⟩
    wp_auto
    cases cl with
    | nil =>
      wp_auto
      cases valid <;> (wp_auto; jwt_fail)
    | ok ii =>
      by_cases Hty : ii.ty = github_com.golang_jwt.jwt.v5.MapClaims.ty
      · iunfold jwtClaimsOk at Hclok
        icases Hclok $$ %ii [] with ⟨%m, %mm, %Hv, #Hm, %Hmm⟩
        · ipureintro; exact ⟨rfl, Hty⟩
        simp only [Hty, ↓reduceIte, Hv, _root_.decide_true]
        wp_auto
        cases valid
        · wp_auto; jwt_fail
        have Hj : ∀ k : GoString, jsonAnyOk ((mm !! k).getD GoInterface.nil) := by
          intro k
          cases Hk : mm !! k with
          | none => left; rfl
          | some v => exact Hmm k v Hk
        wp_auto
        wp_apply wp_map_lookup1 $$ Hm as -
        rcases Hj [117#8, 115#8, 101#8, 114#8, 110#8, 97#8, 109#8, 101#8] with
          Hu | ⟨us, Hu⟩ | ⟨uf, Hu⟩ | ⟨ui, Hu, Hus, -⟩ <;> rw [Hu]
        · wp_auto; jwt_fail
        · wp_auto
          wp_apply wp_map_lookup1 $$ Hm as -
          rcases Hj [114#8, 101#8, 118#8, 105#8, 115#8, 105#8, 111#8, 110#8] with
            Hr | ⟨rs, Hr⟩ | ⟨rf, Hr⟩ | ⟨ri, Hr, -, Hrf⟩ <;> rw [Hr]
          · wp_auto; jwt_fail
          · simp only []
            wp_auto
            jwt_fail
          · simp only []
            wp_auto
            cases vo
            · wp_pures
              wp_bind (Pair _ _)
              wp_load
              (try wp_pures)
              wp_load
              wp_apply wp_convert_float64_uint64 as %r -
              (try wp_pures)
              wp_alloc a as Ha
              jwt_ok Ha
              ileft; ipureintro; rfl
            · wp_auto
              wp_bind (Pair _ _)
              wp_alloc a as Ha
              jwt_ok Ha
              iright; iexact Revision
          · simp only [Hrf, ↓reduceIte, decide_false]
            wp_auto
            jwt_fail
        · simp only []
          wp_auto
          jwt_fail
        · simp only [Hus, ↓reduceIte, decide_false]
          wp_auto
          jwt_fail
      · simp only [Hty, ↓reduceIte, decide_false]
        wp_auto
        cases valid <;> (wp_auto; jwt_fail)

/-- **The JWT provider meets the store's contract** (`tokenProviderOk`, `InvAuth.lean`, which
`authStore.authInfoFromToken` calls `info` through): the store's proofs, unchanged, hold of a
store whose provider is a `*tokenJWT`, verify-only or not. -/
theorem auth.tokenJWT.tokenProviderOk_of
    (h_info : auth.tokenJWT.info.spec (GF := GF) (hG := hG)) (t : Loc) (vo : Bool) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ jwtProviderRO t vo ⊢
      tokenProviderOk (interface.mkOk (go.GoType.PointerType tokenJWT.ty) #t) := by
  iintro ⟨#Hpkg, #Ht⟩
  iunfold tokenProviderOk
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %ctx %token %rev !> %Φ - HΦ
  wp_apply h_info t vo ctx token rev $$ [$Hpkg $Ht] as %a %ok ⟨Ha, -⟩
  iapply HΦ $$ Ha

end proof

end EtcdGrove
end Perennial
