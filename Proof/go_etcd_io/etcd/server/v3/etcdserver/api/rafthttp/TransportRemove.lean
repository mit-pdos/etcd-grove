/-
**`Transport.RemovePeer` and `RemoveAllPeers`, over the transport's lock** (D43 M5a, 2026-10-26).
Lean-first. Both take the write lock and call `removePeer` on one id or on each key of `t.peers`
(deleting from the map it ranges over): `removePeer` stops a known peer (its stop right taken from
the stop invariant), deletes it from the peers' map and the leader stats' followers' map, removes
it from the probers and logs; the peers' ids lose it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__stop
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The peers' facts of a map are its sub-map's. -/
theorem peersOk_delete (Rh : RaftHttp GF) (lid : w64) (γd : GName) (R : IProp GF)
    (PM : GMap w64 GoInterface) (id : w64) :
    peersOk Rh lid γd R PM ⊢ peersOk Rh lid γd R (GMap.delete id PM) := by
  unfold peersOk
  cases h : PM !! id with
  | none => rw [GMap.delete_notin _ _ h]
  | some pi =>
    iintro H
    icases (BigSepM.bigSepM_delete (m := PM) h).1 $$ H with ⟨-, H⟩
    iexact H

/-- **A peer removed** (`removePeer`, under the write lock, its half of the record): the record
loses it, and its stop right leaves the stop invariant. -/
theorem trStop_remove_peer (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (pm rm : Loc)
    (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (id : w64) (pi : GoInterface)
    (hs : PM !! id = some pi) :
    ⊢ trStopInv Rh R γs -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM) : trRec) -∗ £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm, GMap.delete id PM, RM) : trRec) ∗
      ∃ p : Loc, ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
        peerStop Rh id R p := by
  iintro #Hinv Hg Hlc
  unfold trStopInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%pm', %rm', %PM', %RM', Hg', Hps, Hrs⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm, GMap.delete id PM, RM) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  icases (BigSepM.bigSepM_delete (m := PM) hs).1 $$ Hps with ⟨Hp, Hps⟩
  imod Hclose $$ [Hg' Hps Hrs] with -
  · inext
    iexists pm, rm, _, RM
    iframe
  imodintro
  iframe

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.removePeer(id)`** under the write lock, with the peers' map (`pm`, non-nil, owned whole),
its half of the record, its peers' facts and the leader stats: it returns, the peer of `id` (if
any) stopped, and `id` gone from the peers' map, the record and the followers' map. -/
theorem rafthttp.Transport.removePeer_core
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs : GName)
    (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (id : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trProbers t ∗ trStopInv Rh R γs ∗
        t.[rafthttp.Transport, go!"peers"] ↦ pm ∗ pm ↦$ PM ∗
        ghostVar γs (1 : Qp).half ((pm, rm, PM, RM) : trRec) ∗ □ peersOk Rh lid γd R PM ∗
        trStats t 1 }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"removePeer")) (Val #id))
    {{ RET #(); t.[rafthttp.Transport, go!"peers"] ↦ pm ∗ pm ↦$ (GMap.delete id PM) ∗
        ghostVar γs (1 : Qp).half ((pm, rm, GMap.delete id PM, RM) : trRec) ∗ trStats t 1 }} := by
  wp_start as ⟨#Htr, #Hprb, #Hst, Hp, Hpm, Hg, #Hpo, Hts⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss0, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr,
    #Hlg, %Hlgnn, #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok,
    #Hdrf, #Hls, %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx, %Hmem⟩
  iunfold trProbers at Hprb
  icases Hprb with ⟨%pp, %sp, #Hppf, #Hppok, #Hspf, #Hspok⟩
  iunfold probing.proberOk at Hppok Hspok
  icases Hppok with ⟨%pti, %Hpti, -, #Hprem⟩
  icases Hspok with ⟨%sti, %Hsti, -, #Hsrem⟩
  subst Hpti Hsti
  iunfold trStats at Hts
  icases Hts with ⟨%ls', #Hls', #Hlsi, Hlsf⟩
  ihave %Hlseq := typedPointsto_agree_wand _ _ _ _ _ $$ Hls Hls'
  subst Hlseq
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto_lc 1
  wp_apply wp_map_lookup2 $$ [$Hpm] as Hpm
  (try wp_auto)
  cases hp : PM !! id with
  | none =>
    simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
    (try wp_auto)
    repeat' (first
      | (wp_apply hIDStringPtr _ _ _ $$ [id] as %_ ⟨id, -⟩; iexact id)
      | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
      | (wp_apply hZString as %_ -)
      | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
         iintro %_ ⟨-, -⟩)
      | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
      | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
      | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
      | wp_auto)
    iapply HΦ
    rw [GMap.delete_notin _ _ hp]
    iframe
    iunfold trStats; iexists ls; iframe; iframe #
  | some pi =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    iunfold peersOk at Hpo
    ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
      peerOk Rh lid id γd R p)) hp $$ Hpo
    icases Hpi with ⟨%p, %Hpp, #Hpok⟩
    imod trStop_remove_peer Rh R γs pm rm PM RM id pi hp $$ Hst Hg Hlc1 with ⟨Hg, %p', %Hp', Hps⟩
    subst Hpp
    have hpp : p' = p := by
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Hp'
      exact (GoGlobalContext.intoVal_inj_loc Hp').symm
    subst hpp
    simp only [interface.mkOk]
    (try wp_auto)
    wp_apply hPeerStop Rh lid id γd R p' $$ [Hps] as -
    · iframe; iframe #
    (try wp_auto)
    wp_apply wp_mapDelete $$ [Hpm] as Hpm
    · iexact Hpm
    (try wp_auto)
    iunfold v2stats.lsFollowers at Hlsf
    icases Hlsf with ⟨%fm, %FM, #Hfm, Hfmm, %Hfnn⟩
    (try wp_auto)
    wp_apply hIDStringPtr _ _ _ $$ [id] as %ids ⟨id, -⟩
    · iexact id
    wp_apply wp_mapDelete $$ [Hfmm] as Hfmm
    · iexact Hfmm
    (try wp_auto)
    repeat' (first
      | (wp_apply hIDStringPtr _ _ _ $$ [id] as %_ ⟨id, -⟩; iexact id)
      | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
      | (wp_apply Hprem as %_ -)
      | (wp_apply Hsrem as %_ -)
      | (wp_apply hZString as %_ -)
      | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
         iintro %_ ⟨-, -⟩)
      | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
      | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
      | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
      | wp_auto)
    iapply HΦ
    iframe
    iunfold trStats; iexists ls; iframe #
    iunfold v2stats.lsFollowers; iexists fm, _; iframe #; iframe
    ipureintro
    intro k v hk
    exact Hfnn k v ((GMap.lookup_delete_Some FM ids k v).1 hk).2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.RemovePeer(id)`** on a live transport (its half of `γr`, not stopped) with the write
lock's guard: it returns, `id`'s peer (if any) removed, `id` no longer among the peers' ids. -/
theorem rafthttp.Transport.RemovePeer_core
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (rs : trIds) (id : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trProbers t ∗ trStopInv Rh R γs ∗
        sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr) ∗
        ghostVar γr (1 : Qp).half (rs, false) }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"RemovePeer")) (Val #id))
    {{ RET #(); ghostVar γr (1 : Qp).half ((rs.1, rs.2.filter (· != id)), false) }} := by
  wp_start as ⟨#Htr, #Hprb, #Hst, #Hgd, Hlive⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HP⟩
  · iframe #
  wp_auto_lc 1
  imod lc_fupd_elim_later $$ Hlc1 HP with HP
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro, Hts⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hlive Hgr
  cases Hag
  obtain ⟨Hrs1, Hnn, Hcov⟩ := Hrs
  obtain ⟨Hpmnn, Hrmnn⟩ := Hnn rfl
  imod ghostVar_update_halves ((rs.1, rs.2.filter (· != id)), false) γr _ _ $$ Hlive Hgr
    with ⟨Hlive, Hgr⟩
  iunfold mapOrNil at Hpm
  icases Hpm with (⟨%Hpn, -⟩ | Hpm)
  · exact absurd Hpn Hpmnn
  (try wp_auto)
  wp_apply (rafthttp.Transport.removePeer_core hPeerStop hIDStringPtr hInfo hWarn hZString Rh t lid
      γd R γs pm rm PM RM id) $$ [Hp Hpm Hg Hts] as ⟨Hp, Hpm, Hg, Hts⟩
  · iframe; iframe #
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr Hts]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP
    iexists pm, rm, _, RM, (rs.1, rs.2.filter (· != id)), false
    iframe Hp Hr Hrm Hg Hgr Hts
    isplitl [Hpm]
    · iunfold mapOrNil; iright; iexact Hpm
    isplitr
    · ipureintro
      refine ⟨Hrs1, fun _ => ⟨Hpmnn, Hrmnn⟩, fun hr k hk => ?_⟩
      obtain ⟨hk, hne⟩ := List.mem_filter.1 hk
      have hne' : id ≠ k := fun h => by subst h; simp at hne
      rw [GMap.lookup_delete_ne _ hne']
      exact Hcov hr k hk
    isplitr
    · imodintro; iapply peersOk_delete $$ Hpo
    iframe #
  (try wp_auto)
  iapply HΦ; iframe

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.RemoveAllPeers()`** on a live transport (its half of `γr`, not stopped) with the write
lock's guard: it returns, every peer removed (`removePeer` on each key of the map it ranges over,
which deletes it), no peer id left. -/
theorem rafthttp.Transport.RemoveAllPeers_core
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (rs : trIds) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trProbers t ∗ trStopInv Rh R γs ∗
        sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr) ∗
        ghostVar γr (1 : Qp).half (rs, false) }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"RemoveAllPeers"))
        (Val #()))
    {{ RET #(); ghostVar γr (1 : Qp).half (((rs.1, ([] : List w64)) : trIds), false) }} := by
  wp_start as ⟨#Htr, #Hprb, #Hst, #Hgd, Hlive⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply (lc := 1) wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HP⟩
  · iframe #
  imod lc_fupd_elim_later $$ Hlc1 HP with HP
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro, Hts⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hlive Hgr
  cases Hag
  obtain ⟨Hrs1, Hnn, -⟩ := Hrs
  obtain ⟨Hpmnn, Hrmnn⟩ := Hnn rfl
  imod ghostVar_update_halves (((rs.1, ([] : List w64)) : trIds), false) γr _ _ $$ Hlive Hgr
    with ⟨Hlive, Hgr⟩
  iunfold mapOrNil at Hpm
  icases Hpm with (⟨%Hpn, -⟩ | Hpm)
  · exact absurd Hpn Hpmnn
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun _ _ m' => iprop(t.[rafthttp.Transport, go!"peers"] ↦ pm ∗
      ghostVar γs (1 : Qp).half ((pm, rm, m', RM) : trRec) ∗ □ peersOk Rh lid γd R m' ∗
      trStats t 1 ∗ t_ptr ↦ t ∗ ∃ x : w64, id_ptr ↦ x)) _ _ _ pm PM (DFrac.own 1) $$ Hpm
  iintro %keys -
  isplitl [Hp Hg Hts t id]
  · iframe; iframe #
    try (iexists _; iexact id)
  isplitr
  · imodintro
    iintro %i %key %v %m' -  ⟨Hp, Hg, #Hpo', Hts, Ht, %x, Hid⟩ Hpm
    (try wp_auto)
    wp_apply (rafthttp.Transport.removePeer_core hPeerStop hIDStringPtr hInfo hWarn hZString Rh t
        lid γd R γs pm rm m' RM key) $$ [Hp Hpm Hg Hts] as ⟨Hp, Hpm, Hg, Hts⟩
    · iframe; iframe #
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _
    iframe
    imodintro; iapply peersOk_delete $$ Hpo'
  isplitr
  · imodintro
    iintro %i %key %m' - HPi
    iexact HPi
  iintro %m' ⟨Hp, Hg, #Hpo', Hts, Ht, %x, Hid⟩ Hpm
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr Hts]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP
    iexists pm, rm, m', RM, (rs.1, []), false
    iframe Hp Hr Hrm Hg Hgr Hts
    isplitl [Hpm]
    · iunfold mapOrNil; iright; iexact Hpm
    isplitr
    · ipureintro
      exact ⟨Hrs1, fun _ => ⟨Hpmnn, Hrmnn⟩, fun _ k hk => by simp at hk⟩
    iframe #
  (try wp_auto)
  iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
