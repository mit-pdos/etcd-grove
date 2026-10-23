/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__isRangeOpPermitted.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isRangeOpPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyPoint
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyInterval
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Error

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

theorem auth.authStore.isRangeOpPermitted.wp_proof
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_checkKeyInterval : auth.checkKeyInterval.spec (GF := GF) (hG := hG))
    (h_checkKeyPoint : auth.checkKeyPoint.spec (GF := GF) (hG := hG)) :
    auth.authStore.isRangeOpPermitted.spec (GF := GF) (hG := hG) := by
  intro st R M user key re k e dk de pt
  wp_start as ⟨#Hinv, Hrd, Hk, He, %Hpt, %Hlen⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  iunfold cacheRd at Hrd
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold cacheP at HP
  icases HP with ⟨%mp, %M, Hmp, HM, #Hall⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 go.string _ mp M user $$ HM as HM
  cases HMu : M !! user with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply h_String _ _ as %f -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM] as Hrd
    · inext; iunfold cacheP; iexists mp, M; iframe Hmp HM Hall
    iapply HΦ
    iunfold cacheRd
    iframe Hrd Hk He
  | some p =>
    ihave #Hp := BigSepM.bigSepM_lookup (Φ := fun (_ : GoString) (p : Loc) => permsOk (GF := GF) p)
      HMu $$ Hall
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
    wp_auto
    wp_if_destruct
    · wp_apply h_checkKeyPoint $$ [$Hp $Hk] as %b Hk
      · ipureintro; exact ⟨Hpt, Hlen⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM] as Hrd
      · inext; iunfold cacheP; iexists mp, M; iframe Hmp HM Hall
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He
    · wp_apply h_checkKeyInterval $$ [$Hp $Hk $He] as %b ⟨Hk, He⟩
      · ipureintro; exact Hpt
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM] as Hrd
      · inext; iunfold cacheP; iexists mp, M; iframe Hmp HM Hall
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He

end proof

end EtcdGrove
end Perennial
