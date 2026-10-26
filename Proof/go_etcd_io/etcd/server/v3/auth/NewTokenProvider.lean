/-
`NewTokenProvider`'s proof (the auth plan's E2g, 2026-10-25; until then an axiom at the trust
boundary, unit N1): the options decomposed (`decomposeOpts`), then the token type's switch: the
simple provider (`newTokenProviderSimple`, with its facts for the options `"simple"`), the JWT
provider (`newTokenProviderJWT`, the trust boundary), the no-op provider for `""`, or the error
`ErrInvalidAuthOpts` (the package's fact: not nil).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.NewTokenProvider
public import Spec.go_etcd_io.etcd.server.v3.auth.decomposeOpts
public import Spec.go_etcd_io.etcd.server.v3.auth.newTokenProviderSimple
public import Spec.go_etcd_io.etcd.server.v3.auth.newTokenProviderJWT
public import Spec.go_etcd_io.etcd.server.v3.auth.newTokenProviderNop
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem auth.NewTokenProvider.wp_proof
    (h_decomposeOpts : auth.decomposeOpts.spec (GF := GF) (hG := hG))
    (h_Simple : auth.newTokenProviderSimple.spec (GF := GF) (hG := hG))
    (h_JWT : auth.newTokenProviderJWT.spec (GF := GF) (hG := hG))
    (h_Nop : auth.newTokenProviderNop.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Error.spec (GF := GF) (hG := hG)) :
    auth.NewTokenProvider.spec (GF := GF) (hG := hG) := by
  intro lg opts iw ttl
  wp_start as %Hlg
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HIO⟩
  iunfold authErrVar at HIO
  icases HIO with ⟨%eIO, #HeIO, -⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply h_decomposeOpts lg opts $$ [] as %tt %m %err Hd
  · iframe #; ipureintro; exact Hlg
  have Hsimple1 : _root_.Perennial.strings.split go!"simple" go!"," = [go!"simple"] := by
    simp [_root_.Perennial.strings.split, _root_.Perennial.strings.splitAux]
  -- not the options `"simple"` (when the token type is not `"simple"`)
  have Hns : tt = (_root_.Perennial.strings.split opts go!",").head! → tt ≠ go!"simple" →
      opts ≠ go!"simple" := by
    intro h hne hopt; subst hopt; rw [Hsimple1] at h; exact hne h
  icases Hd with (⟨%Herr, %Htt, %mm, Hm⟩ | %Herr)
  · subst Herr
    (try wp_auto)
    wp_if_destruct
    · -- the simple provider
      wp_if_destruct
      · exfalso; first | exact Hlg rfl | (apply Hlg; assumption)
      wp_apply h_Warn $$ []
      · iframe #; ipureintro; exact Hlg
      (try wp_auto)
      wp_apply h_Simple lg iw ttl $$ [] as %p ⟨#Hw, Hp⟩
      (try wp_auto)
      iapply HΦ
      isplitl []
      · ipureintro; intro _; simp
      icases Hp with (%Hneg | ⟨%γt, %γf, #Hok, Had, Hf⟩)
      · ileft; ipureintro; right; exact Hneg
      · iright
        iexists p, γt, γf
        iframe Hw Hok Had Hf
        ipureintro; exact ⟨rfl, rfl⟩
    · have Hno := Hns Htt Hif
      wp_if_destruct
      · -- the JWT provider
        wp_apply h_JWT lg m mm $$ [$Hm] as %p %err -
        (try wp_auto)
        iapply HΦ
        isplitl []
        · ipureintro; intro _; simp
        ileft; ipureintro; left; exact Hno
      · wp_if_destruct
        · -- the no-op provider
          wp_apply h_Nop $$ [] as %p %err %Herr
          (try wp_auto)
          iapply HΦ
          isplitl []
          · ipureintro; intro _; simp
          ileft; ipureintro; left; exact Hno
        · -- an unknown token type: the error
          wp_if_destruct
          · exfalso; first | exact Hlg rfl | (apply Hlg; assumption)
          wp_apply h_String _ _ as %f1 -
          (try wp_auto)
          wp_apply h_Error _ as %f2 -
          (try wp_auto)
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply h_Warn
          · ipureintro; exact Hlg
          (try wp_auto)
          iapply HΦ
          isplitl []
          · ipureintro; intro h; simp at h
          ileft; ipureintro; left; exact Hno
  · cases err with
    | nil => exact absurd rfl Herr.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      isplitl []
      · ipureintro; intro h; simp at h
      ileft; ipureintro; left
      intro hopt; subst hopt; rw [Hsimple1] at Herr; simp at Herr

end proof

end EtcdGrove
end Perennial
