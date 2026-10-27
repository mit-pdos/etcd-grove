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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
loses it, and its stop right leaves the stop invariant; (D22 J-T) its no-remote token goes back
to its pool entry, if it has one (`id ∈ L`). -/
theorem trStop_remove_peer (Rh : RaftHttp GF) (R : IProp GF) (γs : GName) (L : List w64)
    (γk γo : GName) (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc) (T : List w64)
    (id : w64) (pi : GoInterface) (hs : PM !! id = some pi) :
    ⊢ trStopInv Rh R γs L γk γo -∗ ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) -∗
      (⌜id ∉ L⌝ ∨ trTokAt γk id 1) -∗ £ 1 ={⊤}=∗
      ghostVar γs (1 : Qp).half ((pm, rm, GMap.delete id PM, RM, T) : trRec) ∗
      ∃ p : Loc, ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
        peerStop Rh id R p := by
  iintro #Hinv Hg Htk Hlc
  unfold trStopInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%pm', %rm', %PM', %RM', %T', %b, Hg', Hps, Hrs, Hpool, Hak, Hob, Hb, Hbw⟩
  ihave %Hag := ghostVar_agree γs _ _ _ _ $$ Hg Hg'
  cases Hag
  imod ghostVar_update_halves ((pm, rm, GMap.delete id PM, RM, T) : trRec) γs _ _ $$ Hg Hg'
    with ⟨Hg, Hg'⟩
  icases (BigSepM.bigSepM_delete (m := PM) hs).1 $$ Hps with ⟨Hp, Hps⟩
  iunfold trPool at Hpool
  icases Hpool with ⟨%HTL, Hpool⟩
  have hPM : ∀ x ∈ L, x ≠ id → trPoolE (GF := GF) R γk rm PM T x ⊢
      trPoolE R γk rm (GMap.delete id PM) T x := fun x _ hx =>
    trPoolE_mono R γk rm rm PM _ T T x Iff.rfl
      (fun h => by rw [GMap.lookup_delete_ne _ (Ne.symm hx)]; exact h) (fun h => h)
  ihave Hpool : iprop([∗list] x ∈ L, trPoolE R γk rm (GMap.delete id PM) T x) $$ [Hpool Htk]
  · icases Htk with (%HnL | Htok)
    · iapply BigSepL.bigSepL_mono (fun {_ x} hk => hPM x (List.mem_of_getElem? hk)
        (fun e => HnL (e ▸ List.mem_of_getElem? hk))) $$ Hpool
    · by_cases hL : id ∈ L
      · icases bigSepL_nodup_split (Φ := fun x => trPoolE R γk rm PM T x)
            (Ψ := fun x => trPoolE R γk rm (GMap.delete id PM) T x) L HTL.2 id hL hPM $$ Hpool
          with ⟨He, Hpool⟩
        iapply Hpool
        iunfold trPoolE at He
        iunfold trPoolE
        icases He with (⟨-, Htok'⟩ | ⟨%Hn, (⟨HR1, HR2, HR3, HR4, (Htok' | -)⟩ | %Hnull)⟩)
        · iunfold trTokAt at Htok Htok'
          ihave %Hv := ghostMapElem_valid_2 id γk _ _ _ _ $$ Htok Htok'
          exact absurd Hv.1 (dfrac_own_one_op_invalid _)
        · iunfold trTokAt at Htok Htok'
          ihave %Hv := ghostMapElem_valid_2 id γk _ _ _ _ $$ Htok Htok'
          exact absurd Hv.1 (dfrac_own_one_op_invalid _)
        · iright; isplitr; · ipureintro; exact Hn
          ileft; iframe
        · iright; isplitr; · ipureintro; exact Hn
          iright; ipureintro; exact Hnull
      · iapply BigSepL.bigSepL_mono (fun {_ x} hk => hPM x (List.mem_of_getElem? hk)
          (fun e => hL (e ▸ List.mem_of_getElem? hk))) $$ Hpool
  imod Hclose $$ [Hg' Hps Hrs Hpool Hak Hob Hb Hbw] with -
  · inext
    iexists pm, rm, _, RM, T, b
    iframe Hg' Hps Hrs Hak Hob Hb Hbw
    iunfold trPool
    iframe Hpool
    ipureintro; exact HTL
  imodintro
  iframe

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
    (L : List w64) (γk γo : GName) (pm rm : Loc) (PM : GMap w64 GoInterface) (RM : GMap w64 Loc)
    (T : List w64) (id : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trProbers t ∗ trStopInv Rh R γs L γk γo ∗
        t.[rafthttp.Transport, go!"peers"] ↦ pm ∗ pm ↦$ PM ∗
        ghostVar γs (1 : Qp).half ((pm, rm, PM, RM, T) : trRec) ∗ □ peersOk Rh lid γd R PM ∗
        trStats t 1 ∗ (⌜id ∉ L ∨ PM !! id = none⌝ ∨ trTokAt γk id 1) }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"removePeer")) (Val #id))
    {{ RET #(); t.[rafthttp.Transport, go!"peers"] ↦ pm ∗ pm ↦$ (GMap.delete id PM) ∗
        ghostVar γs (1 : Qp).half ((pm, rm, GMap.delete id PM, RM, T) : trRec) ∗ trStats t 1 ∗
        (⌜PM !! id = none⌝ ∨ R ∗ R ∗ R ∗ R) }} := by
  wp_start as ⟨#Htr, #Hprb, #Hst, Hp, Hpm, Hg, #Hpo, Hts, Htk⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss0, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr,
    #Hlg, %Hlgnn, #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok,
    #Hdrf, #Hls, %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx, %⟨Hmem, Hturls⟩⟩
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
    isplitl
    · iunfold trStats; iexists ls; iframe; iframe #
    ileft; ipureintro; rfl
  | some pi =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    iunfold peersOk at Hpo
    ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
      peerOk Rh lid id γd R p)) hp $$ Hpo
    icases Hpi with ⟨%p, %Hpp, #Hpok⟩
    ihave Htk : iprop(⌜id ∉ L⌝ ∨ trTokAt γk id 1) $$ [Htk]
    · icases Htk with (%Hc | Htok)
      · rcases Hc with Hc | Hc
        · ileft; ipureintro; exact Hc
        · rw [hp] at Hc; cases Hc
      · iright; iexact Htok
    imod trStop_remove_peer Rh R γs L γk γo pm rm PM RM T id pi hp $$ Hst Hg Htk Hlc1 with
      ⟨Hg, %p', %Hp', Hps⟩
    subst Hpp
    have hpp : p' = p := by
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Hp'
      exact (GoGlobalContext.intoVal_inj_loc Hp').symm
    subst hpp
    simp only [interface.mkOk]
    (try wp_auto)
    wp_apply hPeerStop Rh lid id γd R p' $$ [Hps] as ⟨HR1, HR2, HR3, HR4⟩
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
    iframe HR1 HR2 HR3 HR4
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
    (L : List w64) (γk γo : GName) (rs : trIds) (id : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trProbers t ∗ trStopInv Rh R γs L γk γo ∗
        sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr) ∗
        ghostVar γr (1 : Qp).half (rs, false) ∗ (⌜id ∉ L ∨ id ∉ rs⌝ ∨ trTokAt γk id 1) }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"RemovePeer")) (Val #id))
    {{ RET #(); ghostVar γr (1 : Qp).half (rs.filter (· != id), false) }} := by
  wp_start as ⟨#Htr, #Hprb, #Hst, #Hgd, Hlive, Htk⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HP⟩
  · iframe #
  wp_auto_lc 1
  imod lc_fupd_elim_later $$ Hlc1 HP with HP
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %T, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro,
    Hts⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hlive Hgr
  cases Hag
  obtain ⟨Hnn, Hcov, HT⟩ := Hrs
  obtain ⟨Hpmnn, Hrmnn⟩ := Hnn rfl
  imod ghostVar_update_halves (rs.filter (· != id), false) γr _ _ $$ Hlive Hgr
    with ⟨Hlive, Hgr⟩
  iunfold mapOrNil at Hpm
  icases Hpm with (⟨%Hpn, -⟩ | Hpm)
  · exact absurd Hpn Hpmnn
  (try wp_auto)
  wp_apply (rafthttp.Transport.removePeer_core hPeerStop hIDStringPtr hInfo hWarn hZString Rh t lid
      γd R γs L γk γo pm rm PM RM T id) $$ [Hp Hpm Hg Hts Htk] as ⟨Hp, Hpm, Hg, Hts, -⟩
  · iframe; iframe #
    icases Htk with (%Hc | Htok)
    · ileft; ipureintro
      rcases Hc with Hc | Hc
      · exact Or.inl Hc
      · right
        cases h : PM !! id with
        | none => rfl
        | some _ => exact absurd ((Hcov Hrmnn id).2 (by simp [h])) Hc
    · iright; iexact Htok
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr Hts]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP
    iexists pm, rm, _, RM, T, rs.filter (· != id), false
    iframe Hp Hr Hrm Hg Hgr Hts
    isplitl [Hpm]
    · iunfold mapOrNil; iright; iexact Hpm
    isplitr
    · ipureintro
      refine ⟨fun _ => ⟨Hpmnn, Hrmnn⟩, fun hr k => ?_, HT⟩
      rw [List.mem_filter]
      by_cases hne : k = id
      · subst hne; simp
      · rw [GMap.lookup_delete_ne _ (Ne.symm hne)]
        simp only [hne, bne_iff_ne, ne_eq, not_false_eq_true, decide_true, and_true]
        exact Hcov hr k
    isplitr
    · imodintro; iapply peersOk_delete $$ Hpo
    iframe #
  (try wp_auto)
  iapply HΦ; iframe

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.RemoveAllPeers()`** on a live transport (its half of `γr`, not stopped) with the write
lock's guard, (D22 J-T) the no-remote token of each peer id of `L` (`Q`, the peers' ids without
repeats): it returns, every peer removed (`removePeer` on each key of the map it ranges over,
which deletes it), no peer id left, and four of each peer's `R`s back (its pipeline's: `peer.stop`
waits for them; the four of its stream readers and writers are not returned, `peer.stop` does
not join the two `Process` goroutines). -/
theorem rafthttp.Transport.RemoveAllPeers_core
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (L : List w64) (γk γo : GName) (rs : trIds) (Q : List w64) (hQn : Q.Nodup)
    (hQ : ∀ f, f ∈ Q ↔ f ∈ rs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trProbers t ∗ trStopInv Rh R γs L γk γo ∗
        sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr) ∗
        ghostVar γr (1 : Qp).half (rs, false) ∗ [∗list] f ∈ Q, (⌜f ∉ L⌝ ∨ trTokAt γk f 1) }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"RemoveAllPeers"))
        (Val #()))
    {{ RET #(); ghostVar γr (1 : Qp).half ((([] : List w64) : trIds), false) ∗
        [∗list] _f ∈ Q, R ∗ R ∗ R ∗ R }} := by
  wp_start as ⟨#Htr, #Hprb, #Hst, #Hgd, Hlive, Htks⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply (lc := 1) wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HP⟩
  · iframe #
  imod lc_fupd_elim_later $$ Hlc1 HP with HP
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %T, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro,
    Hts⟩
  ihave %Hag := ghostVar_agree γr _ _ _ _ $$ Hlive Hgr
  cases Hag
  obtain ⟨Hnn, Hcov, HT⟩ := Hrs
  obtain ⟨Hpmnn, Hrmnn⟩ := Hnn rfl
  imod ghostVar_update_halves ((([] : List w64) : trIds), false) γr _ _ $$ Hlive Hgr
    with ⟨Hlive, Hgr⟩
  iunfold mapOrNil at Hpm
  icases Hpm with (⟨%Hpn, -⟩ | Hpm)
  · exact absurd Hpn Hpmnn
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun keys i m' => iprop(t.[rafthttp.Transport, go!"peers"] ↦ pm ∗
      ghostVar γs (1 : Qp).half ((pm, rm, m', RM, T) : trRec) ∗ □ peersOk Rh lid γd R m' ∗
      trStats t 1 ∗ t_ptr ↦ t ∗ (∃ x : w64, id_ptr ↦ x) ∗
      ⌜(∀ (j : Nat) (k : w64), i ≤ j → keys[j]? = some k → m' !! k = PM !! k) ∧
        ∀ k, (m' !! k).isSome → k ∈ keys.drop i⌝ ∗
      ([∗list] k ∈ keys.drop i, (⌜k ∉ L⌝ ∨ trTokAt γk k 1)) ∗
      [∗list] _k ∈ keys.take i, R ∗ R ∗ R ∗ R)) _ _ _ pm PM (DFrac.own 1) $$ Hpm
  iintro %keys ⟨%Hkeys, %Hklen, %Hknd⟩
  have Hperm : keys.Perm Q := by
    rw [List.perm_ext_iff_of_nodup Hknd hQn]
    intro k
    rw [Hkeys, hQ]
    exact (Hcov Hrmnn k).symm
  isplitl [Hp Hg Hts t id Htks]
  · iframe; iframe #
    isplitl [id]
    · iexists _; iexact id
    isplitr
    · ipureintro
      refine ⟨fun _ _ _ _ => rfl, fun k hk => ?_⟩
      rw [List.drop_zero]; exact (Hkeys k).2 hk
    simp only [List.drop_zero, List.take_zero]
    isplitl [Htks]
    · iapply (BigSepL.bigSepL_perm (Φ := fun k => iprop(⌜k ∉ L⌝ ∨ trTokAt γk k 1)) Hperm).2
      iexact Htks
    iapply BigSepL.bigSepL_nil.2; itrivial
  isplitr
  · imodintro
    iintro %i %key %v %m' %Hiv ⟨Hp, Hg, #Hpo', Hts, Ht, ⟨%x, Hid⟩, %⟨Hagr, Hsub⟩, Hdr, Htk⟩ Hpm
    obtain ⟨hk, hv⟩ := Hiv
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hk
    have hdrop : keys.drop i = key :: keys.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hlt, hget]
    rw [hdrop]
    icases BigSepL.bigSepL_cons.1 $$ Hdr with ⟨Hk, Hdr⟩
    (try wp_auto)
    wp_apply (rafthttp.Transport.removePeer_core hPeerStop hIDStringPtr hInfo hWarn hZString Rh t
        lid γd R γs L γk γo pm rm m' RM T key) $$ [Hp Hpm Hg Hts Hk] as ⟨Hp, Hpm, Hg, Hts, HR⟩
    · iframe; iframe #
      icases Hk with (%Hk | Hk)
      · ileft; ipureintro; exact Or.inl Hk
      · iright; iexact Hk
    icases HR with (%Hn | HR)
    · rw [hv] at Hn; cases Hn
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _
    iframe
    isplitr
    · imodintro; iapply peersOk_delete $$ Hpo'
    isplitl [Hid]
    · iexists _; iexact Hid
    isplitr
    · ipureintro
      refine ⟨fun j k hj hkj => ?_, fun k hk' => ?_⟩
      · have hne : k ≠ key := by
          rintro rfl
          have := list_nodup_getElem?_inj keys Hknd i j k hk hkj
          omega
        rw [GMap.lookup_delete_ne _ (Ne.symm hne)]
        exact Hagr j k (by omega) hkj
      · by_cases hne : k = key
        · subst hne; simp at hk'
        · rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at hk'
          have := Hsub k hk'
          rw [hdrop] at this
          rcases List.mem_cons.1 this with h | h
          · exact absurd h hne
          · exact h
    rw [List.take_succ, hget]
    simp only [Option.toList_some]
    iapply BigSepL.bigSepL_append.2
    iframe Htk
    iapply BigSepL.bigSepL_singleton.2
    iexact HR
  isplitr
  · imodintro
    iintro %i %key %m' %Hin ⟨-, -, -, -, -, -, %⟨Hagr, -⟩, -, -⟩
    obtain ⟨hk, hnone⟩ := Hin
    exfalso
    have := (Hkeys key).1 (List.mem_of_getElem? hk)
    rw [← Hagr i key (Nat.le_refl _) hk, hnone] at this
    exact Bool.false_ne_true this
  iintro %m' ⟨Hp, Hg, #Hpo', Hts, Ht, -, %⟨-, Hsub⟩, -, HRs⟩ Hpm
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr Hts]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP
    iexists pm, rm, m', RM, T, ([] : List w64), false
    iframe Hp Hr Hrm Hg Hgr Hts
    isplitl [Hpm]
    · iunfold mapOrNil; iright; iexact Hpm
    isplitr
    · ipureintro
      refine ⟨fun _ => ⟨Hpmnn, Hrmnn⟩, fun _ k => ⟨fun h => by simp at h, fun h => ?_⟩, HT⟩
      have := Hsub k h
      rw [List.drop_of_length_le (Nat.le_refl _)] at this
      simp at this
    iframe #
  (try wp_auto)
  iapply HΦ; iframe
  rw [List.take_length]
  iapply (BigSepL.bigSepL_perm (Φ := fun _ => iprop(R ∗ R ∗ R ∗ R)) Hperm).1
  iexact HRs

end proof

end EtcdGrove
end Perennial
