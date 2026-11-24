/-
Proof of `config.ServerConfig.VerifyBootstrap.spec` (claim #34, stage 2, 2026-11-25): over
`hasLocalMember`, the pending `advertiseMatchesCluster` (names only, a hypothesis), `CheckDuplicateURL`,
`types.URLsMap.String` (also as `fmt`'s `%s` of the map, `fmt.stringMethodSpec`) and `ShouldDiscover`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__VerifyBootstrap
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__hasLocalMember
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__advertiseMatchesCluster
public import Spec.go_etcd_io.etcd.server.v3.config.CheckDuplicateURL
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ShouldDiscover
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLsMap__String
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.ServerConfig.VerifyBootstrap.wp_proof
    (hLocal : config.ServerConfig.hasLocalMember.spec (GF := GF) (hG := hG))
    (hAdv : config.ServerConfig.advertiseMatchesCluster.spec (GF := GF) (hG := hG))
    (hDup : config.CheckDuplicateURL.spec (GF := GF) (hG := hG))
    (hStr : types.URLsMap.String.spec (GF := GF) (hG := hG))
    (hDisc : config.ServerConfig.ShouldDiscover.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    config.ServerConfig.VerifyBootstrap.spec (GF := GF) (hG := hG) := by
  intro p cfg m urls peer Hsum
  wp_start as ⟨#Hname, #Hmapf, #Hpeerf, #Hlgf, #Hdcf, #Hm, #Hurls, #Hpeer, #Hzlg⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Htypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  -- `URLsMap.String` of the initial cluster, as `fmt` calls it (`%s`)
  have hE := go.method_set_is (t := go_etcd_io.etcd.client.pkg.v3.types.URLsMap.ty) go!"Error"
  have hF := go.method_set_is (t := go_etcd_io.etcd.client.pkg.v3.types.URLsMap.ty) go!"Format"
  have hS := go.method_set_is (t := go_etcd_io.etcd.client.pkg.v3.types.URLsMap.ty) go!"String"
  have hC := go.method_set_is (t := go_etcd_io.etcd.client.pkg.v3.types.URLsMap.ty) go!"CanInterface"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hE hF hS hC
  wp_auto
  wp_apply hLocal p cfg m $$ [] as %err1 %Herr1
  · iframe #
  wp_auto
  wp_if_destruct
  · wp_auto
    iapply HΦ
    ipureintro; left; assumption
  rcases Herr1 with Hne | ⟨-, Hin⟩
  · exact absurd Hif Hne
  wp_auto
  wp_apply hAdv p cfg m urls peer $$ [] as %err2 -
  · iframe #
  wp_auto
  wp_if_destruct
  · wp_auto
    iapply HΦ
    ipureintro; left; assumption
  wp_auto
  wp_apply hDup cfg.InitialPeerURLsMap' m urls $$ [] as %dup -
  · iframe #
  wp_if_destruct
  · -- a repeated URL: an error naming the initial cluster
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
    · iframe #; iframe Hasl
      iapply (_root_.Perennial.fmt.argsOk_intro (ds := [⟨W8 115, false⟩]) (by rfl))
      unfold _root_.Perennial.fmt.argsOkAt _root_.Perennial.fmt.argsOkAt
      isplitl
      · unfold _root_.Perennial.fmt.argOkAt
        iright; iright; ileft
        isplitr
        · ipureintro; refine ⟨by decide, rfl, fun h => by cases h⟩
        unfold _root_.Perennial.fmt.argOk
        iright; iright
        isplitr
        · unfold _root_.Perennial.fmt.stringMethodSpec
          imodintro
          iintro %Φ' HΦ'
          wp_apply hStr cfg.InitialPeerURLsMap' m urls Hsum $$ [] as %s' -
          · iframe #
          iapply HΦ'
        · ipureintro; exact ⟨hF, hE, hS, hC⟩
      · itrivial
    (try wp_auto)
    iapply HΦ
    ipureintro; left; simp
  wp_auto
  wp_apply hStr cfg.InitialPeerURLsMap' m urls Hsum $$ [] as %s -
  · iframe #
  wp_if_destruct
  · wp_apply hDisc p cfg $$ [] as %b -
    · iframe #
    wp_if_destruct
    · wp_auto
      wp_apply hErrorf _ _ _ _ $$ [] as %e -
      · iframe #
        isplitl
        · iapply ownSlice_nil
        fmt_args_ok
      (try wp_auto)
      iapply HΦ
      ipureintro; left; simp
    all_goals (wp_auto; iapply HΦ; ipureintro; right; exact ⟨rfl, Hin⟩)
  all_goals (wp_auto; iapply HΦ; ipureintro; right; exact ⟨rfl, Hin⟩)

end proof

end EtcdGrove
end Perennial
