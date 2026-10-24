/-
**`Transport.AddPeer` and `AddRemote`, over the transport's lock** (rafthttp stage 6c; their axioms'
statements are restated over these in 6d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startRemote
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.addPeerToProber
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.NewURLs
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.LeaderStats__Follower
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Strings

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- The parsed URLs of a member's URL strings are its: plain, owned by it. -/
theorem peerURL_of_parsed (Rh : RaftHttp GF) (pid : w64) (ss : List GoString)
    (Hown : ∀ h, go!"http://" ++ h ∈ ss → Rh.owner h = pid) (u : net.url.URL)
    (Hu : ∃ s ∈ ss, types.parsedPeerURL s u) : peerURL Rh pid u := by
  obtain ⟨s, hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩ := Hu
  subst h12
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11⟩, Hown _ hs⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.AddPeer(id, us)`** on a live transport (its half of `γr`, not stopped) with the write
lock's guard, of `id`'s URL strings (non-empty, plain, owned by `id`), and eight `R`s: it returns,
the peer of `id` started and added (with its stop right) unless there was one. -/
theorem rafthttp.Transport.AddPeer_core
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hFollower : v2stats.LeaderStats.Follower.spec (GF := GF) (hG := hG))
    (hStartPeer : rafthttp.startPeer.spec (GF := GF) (hG := hG))
    (hProber : rafthttp.addPeerToProber.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (rs : List w64) (id : w64) (us : GoSlice) (dq : DFrac) (ss : List GoString)
    (Hne : ss ≠ []) (Hpl : ∀ s ∈ ss, types.plainPeerURL s)
    (Hown : ∀ h, go!"http://" ++ h ∈ ss → Rh.owner h = id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trStopInv Rh R γs ∗
        sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr) ∗
        ghostVar γr (1 : Qp).half (rs, false) ∗ us ↦*{dq} ss ∗
        [∗list] _x ∈ List.replicate 8 (), R }}
      (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddPeer")) (Val #id))
        (Val #us))
    {{ RET #(); ghostVar γr (1 : Qp).half (rs, false) ∗ us ↦*{dq} ss }} := by
  wp_start as ⟨#Htr, #Hst, #Hgd, Hlive, Hus, HRs⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss0, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr,
    #Hlg, %Hlgnn, #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok,
    #Hdrf, #Hls, %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HP⟩
  · iframe #
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hlive Hgr
  cases Hag
  obtain ⟨Hrs1, Hnn⟩ := Hrs
  obtain ⟨Hpmnn, Hrmnn⟩ := Hnn rfl
  (try wp_auto)
  rw [_root_.decide_eq_false (show ¬ pm = map.nil from Hpmnn)]
  (try wp_auto)
  wp_apply wp_lookup2_mapOrNil _ pm _ PM id $$ [Hpm] as Hpm
  · iframe Hpm
  (try wp_auto)
  cases hp : PM !! id with
  | some pi =>
    -- a known peer: nothing
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr]
    · iframe #; iframe Hwl
      inext
      iunfold trLockP; iexists pm, rm, PM, RM, rs, false; iframe; iframe #
      ipureintro; exact ⟨Hrs1, fun _ => ⟨Hpmnn, Hrmnn⟩⟩
    (try wp_auto)
    iapply HΦ; iframe
  | none =>
  simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
  (try wp_auto)
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_apply hNewURLs us dq ss Hne Hpl $$ [Hus] as %urls %uvs ⟨Hus, Hurls, %Huvs⟩
  · iframe
  ipersist Hurls
  (try wp_auto)
  ihave #Hv2 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats $$ []
  · iPkgInit
  wp_apply hIDStringPtr _ _ _ $$ [id] as %ids ⟨id, -⟩
  · iexact id
  wp_apply hFollower ls ids $$ [] as %fs %Hfs
  · iframe #; ipureintro; exact Hlsnn
  (try wp_auto)
  have Hune : uvs ≠ [] := by
    intro h; rw [h] at Huvs; exact Hne (List.length_eq_zero_iff.1 Huvs.1.symm)
  wp_apply hStartPeer Rh t lid γd R urls uvs id fs Hune
      (fun u hu => peerURL_of_parsed Rh id ss Hown u (Huvs.2 u hu)) Hfs $$ [HRs]
    as %pp ⟨#Hpok, Hpstop⟩
  · iframe; iframe #
  (try wp_auto)
  iunfold mapOrNil at Hpm
  icases Hpm with (⟨%Hpn, -⟩ | Hpm)
  · exact absurd Hpn Hpmnn
  wp_apply wp_mapInsert $$ [Hpm] as Hpm
  · iframe Hpm
  imod trStop_add_peer Rh R γs pm rm PM RM id pp hp $$ Hst Hg Hpstop with Hg
  (try wp_auto)
  -- the probers, the log
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%vrtt, #Hrtt⟩⟩
  repeat' (first
    | (wp_apply hIDStringPtr _ _ _ $$ [id] as %_ ⟨id, -⟩; iexact id)
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hProber $$ [Hus] as Hus; iframe Hus)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZStrings _ us dq ss $$ [Hus] as %_ Hus; iframe Hus)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
    | wp_auto)
  -- the deferred unlock: the peer in the map, its facts
  iunfold peersOk at Hpo
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP
    iexists pm, rm, _, RM, rs, false
    iframe Hp Hr Hrm Hg Hgr
    isplitl [Hpm]
    · iunfold mapOrNil; iright; iexact Hpm
    isplitr
    · ipureintro; exact ⟨Hrs1, fun _ => ⟨Hpmnn, Hrmnn⟩⟩
    isplitr
    · imodintro
      iunfold peersOk
      iapply (BigSepM.bigSepM_insert hp).2
      iframe Hpo
      iexists pp; iframe Hpok; ipureintro; rfl
    iframe #
  (try wp_auto)
  iapply HΦ; iframe

set_option hygiene false in
/-- `AddRemote`'s early returns: the write lock given back (`id` now among the remotes' ids). -/
local macro "ar_return" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP; iexists pm, rm, PM, RM, rs ++ [id], false; iframe; iframe #
    ipureintro
    exact ⟨fun k hk => List.mem_append_left _ (Hrs1 k hk), fun _ => ⟨Hpmnn, Hrmnn⟩⟩
  (try wp_auto)
  iapply HΦ; iframe))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.AddRemote(id, us)`** on a live transport (its half of `γr`) with the write lock's guard, of
`id`'s URL strings (non-empty, plain, owned by `id`), and four `R`s: it returns, `id` among the
remotes' ids, the remote of `id` started and added (with its stop right) unless `id` was a peer
or remote already. -/
theorem rafthttp.Transport.AddRemote_core
    (hNewURLs : types.NewURLs.spec (GF := GF) (hG := hG))
    (hStartRemote : rafthttp.startRemote.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (rs : List w64) (id : w64) (us : GoSlice) (dq : DFrac) (ss : List GoString)
    (Hne : ss ≠ []) (Hpl : ∀ s ∈ ss, types.plainPeerURL s)
    (Hown : ∀ h, go!"http://" ++ h ∈ ss → Rh.owner h = id) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trStopInv Rh R γs ∗
        sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr) ∗
        ghostVar γr (1 : Qp).half (rs, false) ∗ us ↦*{dq} ss ∗ R ∗ R ∗ R ∗ R }}
      (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
        (Val #id)) (Val #us))
    {{ RET #(); ghostVar γr (1 : Qp).half (rs ++ [id], false) ∗ us ↦*{dq} ss }} := by
  wp_start as ⟨#Htr, #Hst, #Hgd, Hlive, Hus, HR1, HR2, HR3, HR4⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss0, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr,
    #Hlg, %Hlgnn, #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok,
    #Hdrf, #Hls, %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HP⟩
  · iframe #
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hlive Hgr
  cases Hag
  obtain ⟨Hrs1, Hnn⟩ := Hrs
  obtain ⟨Hpmnn, Hrmnn⟩ := Hnn rfl
  -- `id` joins the remotes' ids
  imod ghostVar_update_halves (rs ++ [id], false) γr _ _ $$ Hlive Hgr with ⟨Hlive, Hgr⟩
  (try wp_auto)
  rw [_root_.decide_eq_false (show ¬ rm = map.nil from Hrmnn)]
  (try wp_auto)
  wp_apply wp_lookup2_mapOrNil _ pm _ PM id $$ [Hpm] as Hpm
  · iframe Hpm
  (try wp_auto)
  cases hp : PM !! id with
  | some pi =>
    simp only [Option.isSome_some, _root_.decide_true]
    ar_return
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
  (try wp_auto)
  wp_apply wp_lookup2_mapOrNil _ rm _ RM id $$ [Hrm] as Hrm
  · iframe Hrm
  (try wp_auto)
  cases hr : RM !! id with
  | some g =>
    simp only [Option.isSome_some, _root_.decide_true]
    ar_return
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
  (try wp_auto)
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_apply hNewURLs us dq ss Hne Hpl $$ [Hus] as %urls %uvs ⟨Hus, Hurls, %Huvs⟩
  · iframe
  ipersist Hurls
  (try wp_auto)
  have Hune : uvs ≠ [] := by
    intro h; rw [h] at Huvs; exact Hne (List.length_eq_zero_iff.1 Huvs.1.symm)
  wp_apply hStartRemote Rh t lid γd R urls uvs id Hune
      (fun u hu => peerURL_of_parsed Rh id ss Hown u (Huvs.2 u hu)) $$ [HR1 HR2 HR3 HR4]
    as %g ⟨#Hgok, Hgstop⟩
  · iframe; iframe #
  (try wp_auto)
  iunfold mapOrNil at Hrm
  icases Hrm with (⟨%Hrn, -⟩ | Hrm)
  · exact absurd Hrn Hrmnn
  wp_apply wp_mapInsert $$ [Hrm] as Hrm
  · iframe Hrm
  imod trStop_add_remote Rh R γs pm rm PM RM id g hr $$ Hst Hg Hgstop with Hg
  (try wp_auto)
  repeat' (first
    | (wp_apply hIDStringPtr _ _ _ $$ [id] as %_ ⟨id, -⟩; iexact id)
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZStrings _ us dq ss $$ [Hus] as %_ Hus; iframe Hus)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
    | wp_auto)
  iunfold remotesOk at Hro
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP
    iexists pm, rm, PM, _, rs ++ [id], false
    iframe Hp Hr Hpm Hg Hgr
    isplitl [Hrm]
    · iunfold mapOrNil; iright; iexact Hrm
    isplitr
    · ipureintro
      refine ⟨fun k hk => ?_, fun _ => ⟨Hpmnn, Hrmnn⟩⟩
      by_cases hk' : k = id
      · subst hk'; exact List.mem_append_right _ (List.mem_singleton_self _)
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk')] at hk
        exact List.mem_append_left _ (Hrs1 k hk)
    isplitr
    · iframe #
    imodintro
    iunfold remotesOk
    iapply (BigSepM.bigSepM_insert hr).2
    iframe Hro
    iexact Hgok
  (try wp_auto)
  iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
