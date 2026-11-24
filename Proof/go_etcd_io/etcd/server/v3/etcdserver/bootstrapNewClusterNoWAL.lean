/-
Proof of `bootstrapNewClusterNoWAL.spec` (claim #34, stage 2, 2026-11-25; `bootstrap.go:379-414` at the
etcd pin): `VerifyBootstrap` (the configuration's name an entry), `NewClusterFromURLsMap` (the members
`memOfList` of the entries, the id `clusterIdOf` of the sorted ids: `bootGo.memMap` and `bootGo.cid`,
`BootBuild.lean`), `MemberByName(cfg.Name)` (this member's id, `bootGo.id`), `isMemberBootstrapped`
(an error if it answers `true`), `ShouldDiscover()` (false: `bootCfgFresh`), the record.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapNewClusterNoWAL
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isMemberBootstrapped
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__VerifyBootstrap
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ShouldDiscover
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BootstrapTimeoutEffective
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.WithMaxLearners
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewClusterFromURLsMap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__MemberByName
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.fmt.Errorf
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootBuild

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A member id, as an `fmt` argument: its `String()` returns (`fmt.argOk`). -/
theorem bootNC.id_stringMethodSpec (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (id : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ⊢
      fmt.stringMethodSpec ⟨go_etcd_io.etcd.client.pkg.v3.types.ID.ty, #id⟩ go!"String" := by
  iintro #Hp
  rw [fmt.stringMethodSpec_unfold]
  iintro !> %Φ HΦ
  iapply hIDString id $$ []
  · iexact Hp
  inext
  iintro %s -
  iapply HΦ

theorem bootstrapNewClusterNoWAL.wp_proof
    (hVB : config.ServerConfig.VerifyBootstrap.spec (GF := GF) (hG := hG))
    (hWML : membership.WithMaxLearners.spec (GF := GF) (hG := hG))
    (hNCU : membership.NewClusterFromURLsMap.spec (GF := GF) (hG := hG))
    (hMBN : membership.RaftCluster.MemberByName.spec (GF := GF) (hG := hG))
    (hBTE : config.ServerConfig.BootstrapTimeoutEffective.spec (GF := GF) (hG := hG))
    (hIMB : isMemberBootstrapped.spec (GF := GF) (hG := hG))
    (hSD : config.ServerConfig.ShouldDiscover.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    bootstrapNewClusterNoWAL.spec (GF := GF) (hG := hG) := by
  intro cfg U H prt Hfresh HU Hfips HiOk
  obtain ⟨hnc, hend, hutf, hfits⟩ := Hfresh
  have HiOk' := HiOk
  obtain ⟨hnd, hnz, hsz, hsum⟩ := HiOk
  -- the entries' members, as the membership package names them
  let tok := cfg.InitialClusterToken'
  let fm : GoString → apply.MemberM := fun k => membership.memberOfURLs k (U.initURLs k) tok
  have hfm : ∀ k, bootGo.memberOf U tok k = fm k := fun k => bootGo.memberOf_eq U tok k
  -- (no `simp` here: it would unfold the ids' SHA-1)
  have heqm : U.initMap.domList.map (fun k => (fm k).id) =
      U.initMap.domList.map (fun k => (bootGo.memberOf U tok k).id) :=
    List.map_congr_left (fun k _ => by rw [hfm])
  have hnd' : (U.initMap.domList.map (fun k => (fm k).id)).Nodup := by
    rw [heqm]; exact hnd
  have hnz' : W64 0 ∉ U.initMap.domList.map (fun k => (fm k).id) := by
    rw [heqm]; exact hnz
  have hndE : ((U.initMap.domList.map fm).map (·.id)).Nodup := by
    rw [List.map_map]; exact hnd'
  have hlen : ∀ k, (U.initMap.lookup k).isSome → (U.initURLs k).length ≤ 2 ^ 62 := by
    intro k hk
    have hkd : k ∈ U.initMap.domList := (GMap.mem_dom_list _ _).2 hk
    have hle : ∀ l : List GoString, k ∈ l → (U.initURLs k).length ≤
        (l.map (fun k => (U.initURLs k).length)).sum := by
      intro l hl
      induction l with
      | nil => cases hl
      | cons a l ih =>
        rw [List.map_cons, List.sum_cons]
        rcases List.mem_cons.1 hl with rfl | h
        · omega
        · have := ih h; omega
    have := hle _ hkd
    omega
  wp_start as ⟨#Hzlg, #Hro, Hrt⟩
  iunfold bootCfgRO at Hro
  icases Hro with ⟨#Hpeer, #Hcli, #Hmap, #Hurls⟩
  ihave #Hcfgpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hfpkg : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedSuffix Hcf "F"
  -- `cfg.VerifyBootstrap()`
  wp_apply (hVB cfg_ptr cfg U.initMap U.initURLs U.peer hsum) $$ [] as %verr %Hverr
  · iframe #
  rcases Hverr with Hne | Hok
  · obtain ⟨ve, rfl⟩ : ∃ ve, verr = GoInterface.ok ve := by
      cases verr with
      | nil => exact absurd rfl Hne
      | ok ve => exact ⟨ve, rfl⟩
    try wp_auto
    iapply HΦ
    ileft; ipureintro; exact Hne
  obtain ⟨rfl, hname⟩ := Hok
  try wp_auto
  -- `NewClusterFromURLsMap(cfg.Logger, token, cfg.InitialPeerURLsMap, WithMaxLearners(..))`
  wp_apply hWML cfg.MaxLearners' $$ [] as %f #Hf
  try (· iframe #)
  wp_apply wp_slice_literal (V := GoFunc)
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  imod ownSlice_persist $$ Hosl with #Hosl
  wp_apply (hNCU cfg.Logger' tok cfg.InitialPeerURLsMap' U.initMap U.initURLs _ f
      cfg.MaxLearners' Hfips HU hnd' hnz' hsz hlen) $$ [] as %c ⟨%Hcnn, %ms, %ids, %Hids, Hcl⟩
  · iframe #
  try wp_auto
  have hmem : membership.memOfList (U.initMap.domList.map fm) = bootGo.memMap U tok :=
    (bootGo.memMap_eq U tok HiOk').symm
  -- this member's entry
  have hdomname : cfg.Name' ∈ U.initMap.domList := (GMap.mem_dom_list _ _).2 hname
  have hlk : membership.memOfList (U.initMap.domList.map fm) !! (fm cfg.Name').id =
      some (fm cfg.Name') :=
    (membership.memOfList_lookup_some _ hndE _ _).2 ⟨List.mem_map_of_mem hdomname, rfl⟩
  have huniq : membership.memNamesUniq (membership.memOfList (U.initMap.domList.map fm)) :=
    membership.memNamesUniq_memOfList _ fm (fun _ => rfl) hndE
  iunfold membership.clusterOwned at Hcl
  icases Hcl with ⟨%lgc, %rp, %dp, Hclg, #Hlgc, Hlid, Hcid, Hbe, Hmu, Hver, Hmem, Hrf, Hrm, Hdg,
    Hdgv, Hml, Hvc⟩
  -- `cl.MemberByName(cfg.Name)`
  wp_apply (hMBN c 1 ms _ cfg.Name' (fm cfg.Name').id (fm cfg.Name') huniq hlk rfl) $$ [Hmu Hmem]
    as %mc ⟨Hmu, Hmem, Hmc⟩
  · iframe #; iframe
  try wp_auto
  -- `isMemberBootstrapped(cfg.Logger, cl, cfg.Name, prt, cfg.BootstrapTimeoutEffective())`
  wp_apply (hBTE cfg_ptr cfg) $$ [] as %tmo -
  · iframe #
  wp_apply (hIMB cfg.Logger' c cfg.Name' H prt tmo 1 ms _ huniq
      ⟨(fm cfg.Name').id, fm cfg.Name', hlk, rfl⟩) $$ [Hmu Hmem Hrt] as %bt ⟨Hmu, Hmem⟩
  · iframe #; iframe
  iunfold membership.memberIs at Hmc
  icases Hmc with ⟨%Hmcnn, %pu, %cu, %il, %nm, %pus, %cus, Hmid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  cases bt
  rotate_left
  · -- already bootstrapped: an error
    try wp_auto
    wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
    · iframe #; iframe Hasl
      fmt_args_intro; simp only [fmt.argOkAt, fmt.argOk]
      isplitr
      · fmt_arg_method; iright; iright; isplitr
        · iapply bootNC.id_stringMethodSpec hIDString $$ Htpkg
        · ipureintro; fmt_method_facts
      itrivial
    try wp_auto
    iapply HΦ
    ileft; ipureintro; simp
  try wp_auto
  -- `cfg.ShouldDiscover()`: no discovery endpoints
  wp_apply (hSD cfg_ptr cfg) $$ [] as %sd %Hsd
  · iframe #
  have hsd : sd = false := by
    cases sd
    · rfl
    · exact absurd hend (Hsd rfl)
  subst hsd
  try wp_auto
  irename «$r0» => Hbc
  generalize «$r0_ptr» = bcl at *
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists _
  iframe Hbc
  have hids_eq := bootGo.ps_eq U tok HiOk' ids Hids
  isplitr
  · ipureintro
    refine ⟨?_, rfl, ?_⟩
    · show (fm cfg.Name').id = bootGo.id cfg U
      unfold bootGo.id; rw [hfm]
    · refine ⟨hname, ?_, ?_, ?_⟩
      · rw [hids_eq]; exact Hids.1
      · intro h
        have h2 : W64 0 ∈ (bootGo.members U tok).map (·.id) := h
        rw [((bootGo.members_perm U tok).map _).mem_iff] at h2
        unfold bootGo.entries at h2
        rw [List.map_map] at h2
        exact hnz' h2
      · show (bootGo.memberOf U tok cfg.Name').id ∈ bootGo.ps U tok
        rw [hids_eq, Hids.2.1, hfm]
        exact (membership.memOfList_isSome _ hndE _).2
          (List.mem_map.2 ⟨fm cfg.Name', List.mem_map_of_mem hdomname, rfl⟩)
  iunfold clusterBuilt
  rw [← hmem, bootGo.cid_eq U tok HiOk' ids Hids]
  iexists ms, lgc, rp, dp
  iframe

end proof

end EtcdGrove
end Perennial
