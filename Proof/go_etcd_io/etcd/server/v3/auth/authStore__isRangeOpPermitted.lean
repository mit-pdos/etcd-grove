/-
`(*authStore).isRangeOpPermitted`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`, `PermTree.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isRangeOpPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyInterval
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyPoint
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Error
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  ihave %Hle := ownSlice_len _ _ _ $$ He
  have he0 := adt.slice_len_eq_zero Hle
  iunfold cacheRd at Hrd
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold cacheP at HP
  icases HP with ⟨%mp, %Mp, Hmp, HM, #Hall, HgM⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 go.string _ mp Mp user $$ HM as HM
  cases HMu : Mp !! user with
  | none =>
    ihave #Hv := cacheOk_absent M Mp user k e pt HMu $$ Hall
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
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM HgM] as Hrd
    · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hall HgM
    iapply HΦ
    iunfold cacheRd
    iframe Hrd Hk He
    iexact Hv
  | some p =>
    ihave #Hent := cacheOk_lookup M Mp user p HMu $$ Hall
    icases Hent with ⟨%Lr, %Lw, #Hp, #Hent⟩
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
    wp_auto
    wp_if_destruct
    · -- a point: `rangeEnd` empty
      rw [he0] at Hif
      wp_apply (h_checkKeyPoint lg p Lr Lw key k dk pt) $$ [$Hp $Hk] as %b ⟨Hk, %Hb⟩
      · ipureintro; exact ⟨Hpt, Hlen⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM HgM] as Hrd
      · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hall HgM
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He
      iapply (cacheVerdict_entry M user k e pt b Lr Lw Hpt) $$ Hent
      intro _ _
      rw [if_pos Hif]
      exact Hb
    · rw [he0] at Hif
      wp_apply (h_checkKeyInterval lg p Lr Lw key re k e dk de pt) $$ [$Hp $Hk $He]
        as %b ⟨Hk, He, %Hb⟩
      · ipureintro; exact Hpt
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HM HgM] as Hrd
      · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hall HgM
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He
      iapply (cacheVerdict_entry M user k e pt b Lr Lw Hpt) $$ Hent
      intro hk hr
      rw [if_neg Hif]
      rcases hr with h | h
      · exact absurd h Hif
      · exact Hb hk h

end proof

end EtcdGrove
end Perennial
