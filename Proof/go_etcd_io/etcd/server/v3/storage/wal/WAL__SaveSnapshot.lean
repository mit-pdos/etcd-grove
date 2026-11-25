/-
`(*WAL).SaveSnapshot` (S/wal.go:1137-1162), one proof by cases on the handle's state (wal-link L1a,
2026-11-17; the former `wp_proof`, `wp_proofNoErr` and `wp_proofPre` merged), the states' proofs its lemmas:

* `wp_shared` (a share of an open WAL), over its callees: `sync` and the snapshot record's encode on the tail
  (`encoder.encode.specTail`, a hypothesis until the tail's writer accepts writes past its preallocated
  size), their two specs each chosen at a call by whether `Sio` covers every inode (`CalleeCov.lean`),
  `ValidateSnapshotForWrite`, `Snapshot.GetIndex`, `MustMarshalMessage` of a `walpb.Snapshot`
  (`specWalSnap`), Perennial's `Mutex`. After the lock, the deferred `Unlock`'s resolution gives the later
  credit with which the share gives the handle (`walOpenWS_acquire`, `walHdl_open`: with the fresh room when
  covered); the update commits at the next resolution on the unsealed handle (`walTail_append`: `w.snapi` is
  raised after the encode, so the committed handle's `walMaxSnapIdx ≤ snapi` fails in between); the record's
  frame fits the fresh room (its encoding below `2^40` bytes); the handle is rebuilt after the encode and the
  raises (`SnapPure.lean`); then, as `Save`'s tail (the fork's fixes 0007-0008): the tail's offset (`Seek`),
  `sync` below `SegmentSizeBytes`, else (the pipeline non-nil, `walHandleIn_fp`) `cut` at the snapshot
  record's end (`walCutPos_snap`); the room after is fresh again; the handle goes back
  (`walOpenWS_release`), or, after an error (only when not covered, and then with the whole share), the whole
  share is spent (`walOpenWS_finish`).
* `wp_pre` (`Create`'s `w` before the rename), over `sync.specPre`, `encoder.encode.spec`, the same
  `walpb`/`pbutil` callees, `Mutex`, and the client's `Seek` law (`walPreSeekOk`); `w.fp` is nil, so it only
  syncs.

Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshot
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CalleeCov
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encode
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SavePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Proof.os.Off
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessageWalSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SnapPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound
public import Perennial.Proof.sync.Results
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- The snapshot record's size, from its encoding's bound. -/
theorem snap_recSize (c : w32) (d : List w8) (hd : d.length < 2 ^ 40) :
    recSize (recOf ⟨snapshotType, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 := by
  have := recSize_le snapshotType (hash.crc32.crc32c c d) d (by decide)
  omega

theorem walLastHS_snap (H : WalHist) (md : SnapshotMetadataM) (al : Bool) :
    walLastHS (H ++ [WalOpG.snap md al]) = walLastHS H := by
  simp [walLastHS, List.foldl_append]

/-- **`SaveSnapshot` on a share of an open WAL** (the state `shared`; see the file header). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.wp_shared [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [FsStepSat (NoMapLockErr Sio)] (P : WalPbIn GF)
    (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_syncNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (Sio := Sio) (W := W) P Mr)
    (wp_encodeTail : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (W := W) Mr)
    (wp_encodeTailNE : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTailNoErr (Sio := Sio) (W := W) Mr)
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.spec
      (GF := GF) (hG := hG))
    (wp_GetIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF)
      (hG := hG))
    (wp_Marshal : go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specWalSnap (GF := GF) Mr)
    (wp_cut : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (Sio := Sio) (W := W) P Mr)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp) (sp : Loc)
    (md : SnapshotMetadataM) (al cs : Bool) (sized : Bool) (Q : WalDur → IProp GF) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗
      ⌜walCov Sio ∨ q = 1⌝ ∗ ⌜walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)⌝ ∗
      walSnapAt Mr sp md al cs ∗
      ⌜md.Index' = W64 0 ∨ cs = true⌝ ∗ ⌜uint.nat md.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜(Mr.encSnap md al).length < 2 ^ 40⌝ ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir { d with H := d.H ++ [WalOpG.snap md al] }, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"SaveSnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir (d.H.length + 1) ∗ WalFs.walSyncedLb dir (d.H.length + 1)) ∨
      (⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ ∗ ∃ d : WalDur, Q d) }} := by
  wp_start as ⟨#Harea, Hw, %hq, %hcov, #Hs, %hcs, %hidx, %hsz, Hau⟩
  icases walOpenWS_pers Sio P Mr w dir γ q $$ Hw with ⟨Hw, #Hpers⟩
  icases walShPers_facts Sio P Mr w dir γ $$ Hpers with ⟨#Hmu, #Hsync, #Hseg⟩
  ihave %hS := walAreaOk_encState walCodec Mr R jr r $$ Harea
  ihave #Hwpk0 := walShPers_pkgInit Sio P Mr w dir γ $$ Hpers
  ihave #Harea0 := Harea
  iunfold WalFs.walAreaOk at Harea0
  icases Harea0 with ⟨#Hinv, -⟩
  -- the code before the lock
  ihave #Hs0 := Hs
  iunfold walSnapAt at Hs
  icases Hs with ⟨%sc, Hsr, -⟩
  ihave %Hspn := snapRoC_ne sp sc $$ Hsr
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  simp only [decide_eq_false Hspn]
  try wp_auto
  wp_apply (wp_Validate Mr sp md al cs hcs) $$ []
  · iexact Hs0
  try wp_auto
  wp_apply (wp_Marshal sp md al cs (by omega)) $$ [] as %d ⟨%Hdn, Hd, Hdc⟩
  · iframe #
  try wp_auto
  wp_apply +noauto sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hown, -⟩
  -- the deferred `w.mu.Unlock`'s resolution: its later credit takes the handle out of the share
  wp_to_resolve
  first
    | wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
    | wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal _
  inext
  iintro - Hlc
  iapply wp_value'
  iapply fupd_wp
  imod walOpenWS_acquire Sio P Mr w dir γ q $$ [Hw Hown Hlc] with ⟨-, Hheld, Hh⟩
  · iframe Hw Hown Hlc
  imodintro
  icases walHdl_open Sio P Mr w dir $$ Hh with ⟨%h, Hh, %hD, %hmd, Hr, %hroom⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %stp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu', Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hszb, ⟨hidx0, hidx1⟩, hmax⟩ := Hpure
  have hidx0' := hidx0 hD.1
  iunfold walTailW at Htw
  icases Htw with ⟨Hf, Hfdo, Hoff, Htk, %m, %bs, Hm, Hbs, %hmb, Hv⟩
  have hfit : ∀ c, RecsFit walCodec (chainRecs walCodec c (opDs Mr (WalOpG.snap md al : WalOpG WalEnt).toM)) :=
    fun c => recsFit_chainRecs_small c _ (by
      intro p hp
      simp only [WalOpG.toM, opDs, List.mem_singleton] at hp
      subst hp
      exact ⟨by show uint.nat snapshotType < 2 ^ 8; decide, by simpa using hsz⟩)
  have hfit' : (∀ b ∈ ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1,
        b ≤ ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1.length) →
      RecsFit walCodec (recsOfSegs walCodec Mr
        ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.1
        (segsOf (histN (((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1))
          ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1)) →
      RecsFit walCodec (recsOfSegs walCodec Mr
        ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.1
        (segsOf (histN (((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1 ++
          [WalOpG.snap md al])) ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1)) := by
    intro hc hold
    show RecsFit walCodec (allRecs Mr (h.H ++ [WalOpG.snap md al]) h.md h.cuts)
    rw [allRecs_snoc Mr h.H h.md h.cuts _ hc]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hold x hx
    · exact hfit _ x hx
  -- the WALs' step bound at a look (`⧖ |H|`), raised by the next resolution's receipt, deposited by the
  -- commit right after it (`notes/bounds-plan.md`, "The WAL's segment sequence")
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walTail_steps walCodec Mr R jr r dir h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) $$ Hinv Hnc Htk [Hv]
    with ⟨Hnc, Htk, Hv, #Hstp⟩
  · unfold tailVar; iexact Hv
  imodintro
  iframe Hnc
  simp only [go_etcd_io.etcd.server.v3.storage.wal.SnapshotType]
  wp_raise_receipt Hstp
  -- the commit
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walTail_append walCodec Mr R jr r w dir h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) (WalOpG.snap md al) sized
    Q hfit' (snapOp_noMax md al hidx) $$ Hinv Hnc Htk Hv Hopen Hau Hstp with ⟨Hnc, Htk, Hv, Hopen, #Hlb, HQ, %hcp⟩
  unfold tailVar
  imodintro
  iframe Hnc
  icases HQ with ⟨%dq, HQ, %hdq⟩
  ihave HQ : (∃ d : WalDur, Q d ∗ ⌜d.H = h.H⌝) $$ [HQ]
  · iexists dq; iframe HQ; ipureintro; exact hdq
  have hc : ∀ b ∈ h.cuts, b ≤ h.H.length := fun b hb => by
    simpa using walCutPos_le (hcp.1 b hb)
  try wp_auto
  have hT : (W64 5) = snapshotType := rfl
  ipersist «$v0»
  ipersist Hd
  have hguard := snap_guard Mr h md al hc hsplit hD.1
  unfold snapRec at hguard
  have hpre : h.out ++ h.pend ++ frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c (h.crc Mr)
      (Mr.encSnap md al), Mr.encSnap md al⟩) <+: (tailStream Mr (h.H ++ [WalOpG.snap md al]) h.md h.cuts).drop h.o0 :=
    ⟨[], by rw [List.append_nil]; exact hguard⟩
  have hfrm := frame_walRecEnc_tight snapshotType (hash.crc32.crc32c (h.crc Mr) (Mr.encSnap md al))
    (Mr.encSnap md al) (by decide) (by omega)
  have hroom' : walCov Sio → h.o0 + (h.out ++ h.pend ++ frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c (h.crc Mr)
      (Mr.encSnap md al), Mr.encSnap md al⟩)).length ≤ maxBytes := by
    intro hcv
    have := hroom hcv
    have : (2 : Nat) ^ 41 ≤ walFreshRoom := by unfold walFreshRoom maxBytes; omega
    simp only [List.length_append] at *
    omega
  wp_apply (walCov_encodeTail Mr wp_encodeTail wp_encodeTailNE R jr r e f fd name dir h.γ h.ino
      (h.H ++ [WalOpG.snap md al]) h.md h.cuts h.o0 h.sz h.out h.pend (h.crc Mr) _ snapshotType (Mr.encSnap md al)
      (snap_recSize _ _ hsz) hpre hoff hszb (fun hcv => by have := hroom' hcv; omega))
    $$ [Henc Hf Hfdo Hoff Htk Hm Hbs Hv «$r0»] as %err ⟨%pend', Henc, #Hrec, Hres⟩
  · iframe Harea Henv Henc
    isplitl [Hf Hfdo Hoff Htk Hm Hbs Hv]
    · iunfold walTailW
      iframe Hf Hfdo Hoff Htk
      iexists m, bs
      iframe Hm Hbs Hv
      ipureintro; exact hmb
    iunfold encRecIn
    iexists _
    iframe «$r0»
    rw [hT]
    iframe #
    have hro : (recOf ⟨snapshotType, 0#32, Mr.encSnap md al⟩).data = some (Mr.encSnap md al) := by
      simp [recOf, snapshotType, crcType]
    rw [hro]
    simp only [recBytes]
    isplitl []
    · isplitr
      · ipureintro; exact Hdn
      · iexact Hd
    · ipureintro; simp
  icases Hres with (⟨%out', %sz', ⟨%herr, %heq, %hs1, %hs2⟩, Htw⟩ | %herr)
  rotate_left
  · -- the encode failed (only when not covered, and then with the whole share)
    rcases err with ei | _
    rotate_left
    · exact absurd rfl herr.1
    have hq1 : q = 1 := hq.resolve_left herr.2
    subst hq1
    iapply fupd_wp
    imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hown
    · iframe Hpers Hheld
    imodintro
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hown]
    try wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact herr
    icases HQ with ⟨%d, HQ, -⟩
    iexists d; iexact HQ
  subst herr
  try wp_auto
  ihave #HsIT := walSnapAt_idTerm Mr sp md al cs $$ Hs0
  -- `w.snapi`, `w.enti` raised to the snapshot's index when below
  wp_apply (wp_GetIndex sp (md.Index', md.Term')) $$ []
  · iexact HsIT
  wp_join iprop(w_ptr ↦ w ∗ e_ptr ↦ sp ∗ ∃ sv : w64,
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ sv ∗
      ⌜sv = if uint.nat h.snapi < uint.nat md.Index' then md.Index' else h.snapi⌝)
    with [w e Hsnapi] as ⟨w, e, %sv, Hsnapi, %hsv⟩
  · wp_apply (wp_GetIndex sp (md.Index', md.Term')) $$ []
    · iexact HsIT
    try wp_auto
    try wp_join_done
    iframe; ipureintro
    rw [if_pos (by word)]
  · iframe; ipureintro
    rw [if_neg (by word)]
  wp_apply (wp_GetIndex sp (md.Index', md.Term')) $$ []
  · iexact HsIT
  wp_join iprop(w_ptr ↦ w ∗ e_ptr ↦ sp ∗ ∃ ev : w64,
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ ev ∗
      ⌜ev = if uint.nat h.enti < uint.nat md.Index' then md.Index' else h.enti⌝)
    with [w e Henti] as ⟨w, e, %ev, Henti, %hev⟩
  · wp_apply (wp_GetIndex sp (md.Index', md.Term')) $$ []
    · iexact HsIT
    try wp_auto
    try wp_join_done
    iframe; ipureintro
    rw [if_pos (by word)]
  · iframe; ipureintro
    rw [if_neg (by word)]
  -- the handle after the encode and the raises
  have heq' : out' ++ pend' = h.out ++ h.pend ++ frame (walRecEnc (snapRec Mr (h.crc Mr) md al)) := by
    unfold snapRec; exact heq
  obtain ⟨hsplit2, hcrc2⟩ := WalHS.split_snap Mr h md al hc hsplit hD.1 out' pend' sz' sv ev heq'
  have hmap : (h.H ++ [WalOpG.snap md al]).map WalOpG.toM = h.H.map WalOpG.toM ++ [WalOpG.snap md al] := by
    simp [WalOpG.toM]
  obtain ⟨hi1, hi2, hi3⟩ := snap_idx (h.H.map WalOpG.toM) md al h.enti h.snapi hidx0' hidx1 hidx hmax
  rw [← hsv, ← hev, ← hmap] at hi1
  rw [← hsv, ← hmap] at hi2
  rw [← hsv, ← hev] at hi3
  ihave Hh2 : walHandleIn (W := W) P Mr w dir { h with H := h.H ++ [WalOpG.snap md al], out := out', pend := pend', sz := sz', snapi := sv, enti := ev } TailMetaW
    $$ [Hlg Hdir Hdf Hdff Hmd Hsp Hdec Hrc Hns Henti Hsnapi He Henc Htw Hdh Hlocks Hls Hcap Hlks Hfp
      Hpipe Hopen]
  · iunfold walHandleIn
    iexists lg, df, stp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    rw [hcrc2]
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu' Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    ipureintro
    exact ⟨Hen, Hlt, hsplit2, hfd, hs1, hs2, ⟨fun _ => hi1, hi2⟩, hi3⟩
  have hroom2 : walCov Sio → h.o0 + out'.length + pend'.length ≤ maxBytes := by
    intro hcv
    have h1 := congrArg List.length heq
    have h2 := hroom' hcv
    simp only [List.length_append] at h1 h2 ⊢
    omega
  have hst2 : h.st = walLastHS ((h.H ++ [WalOpG.snap md al]).map WalOpG.toM) := by
    rw [hmap, walLastHS_snap]; exact hD.2
  generalize hh2 : ({ h with H := h.H ++ [WalOpG.snap md al], out := out', pend := pend', sz := sz', snapi := sv, enti := ev } : WalHS) = h2
  have e2 : h2.H = h.H ++ [WalOpG.snap md al] ∧ h2.md = h.md ∧ h2.cuts = h.cuts ∧ h2.rest = h.rest ∧
      h2.st = h.st ∧ h2.pc = h.pc ∧ h2.o0 = h.o0 ∧ h2.out = out' ∧ h2.pend = pend' := by
    subst hh2; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨eH, emd, ecuts, erest, est, epc, eo0, eout, epend⟩ := e2
  have hroom3 : walCov Sio → h2.o0 + h2.out.length + h2.pend.length ≤ maxBytes := by
    rw [eo0, eout, epend]; exact hroom2
  have hrest3 : h2.rest = 0 := by rw [erest]; exact hD.1
  have hst3 : h2.st = walLastHS (h2.H.map WalOpG.toM) := by rw [est, eH]; exact hst2
  have hlenH : h2.H.length = h.H.length + 1 := by rw [eH]; simp
  -- the tail's offset
  icases walHandleIn_pure P Mr w dir h2 TailMetaW $$ Hh2 with ⟨Hh2, %hpu2⟩
  icases walHandleIn_seek P Mr w dir h2 TailMetaW $$ Hh2 with
    ⟨%locks2, %ls2, %lt2, %f2, %fd2, %name2, Hlocks, Hls, #Hltf2, Hf, Hoff, %hsk, Hback⟩
  wp_apply (wp_tail w locks2 ls2 lt2 (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  ihave #Hlt0 := Hltf2
  iunfold fileutil.lockedFile at Hlt0
  iStructNamed Hlt0
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) (m := go!"Seek")]
  wp_call
  (try wp_auto)
  obtain ⟨ho1, ho2, ho3⟩ := save_off_toInt h2.o0 h2.out.length hsk.2
  wp_apply (os.File.Seek.wp_cur f2 fd2 name2 (DFrac.own 1) _ hsk.1 ho1 ho2) $$ [$Hf $Hoff] as ⟨Hf, Hoff⟩
  ihave Hh2 := Hback $$ Hlocks Hls Hf Hoff
  (try wp_auto)
  by_cases Hif : sint.Z (W64 ((h2.o0 : Int) + (h2.out.length : Int))) < sint.Z (W64 64000000)
  · -- below the segment size: `sync`
    rw [decide_eq_true Hif]
    (try wp_auto)
    wp_apply (walCov_sync P Mr wp_sync wp_syncNE R jr r w dir h2 hrest3 hroom3) $$ [Hh2] as %err Hres
    · iframe Harea Hh2
    icases Hres with (⟨%herr, Hh, #Hsyn⟩ | %herr)
    · -- synced: the handle back
      iapply fupd_wp
      imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hh Hr] with ⟨Hw, Hown⟩
      · iframe Hpers Hheld
        ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
        rw [← epc]
        iapply walHdl_close Sio P Mr w dir ({ h2 with out := h2.out ++ h2.pend, pend := [], sz := max h2.sz (h2.o0 + h2.out.length + h2.pend.length) } : WalHS) ⟨hrest3, hst3⟩ (by rw [emd]; exact hmd)
          (fun hcv => save_room_small _ _ _ (by
            have := save_hif h2.o0 h2.out.length ho3 Hif
            have := hpu2.2.1
            simp only [List.length_append, List.length_nil]; omega))
        iframe Hh Hr
      imodintro
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hown]
      try wp_auto
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact herr
      iframe Hw
      icases HQ with ⟨%d, HQ, %hd⟩
      iexists d
      iframe HQ
      rw [hd]
      iframe Hlb
      rw [← hlenH]
      iexact Hsyn
    · -- the sync failed (only when not covered, and then with the whole share)
      rcases err with ei | _
      rotate_left
      · exact absurd rfl herr.1
      have hq1 : q = 1 := hq.resolve_left herr.2
      subst hq1
      iapply fupd_wp
      imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hown
      · iframe Hpers Hheld
      imodintro
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hown]
      try wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact herr
      icases HQ with ⟨%d, HQ, -⟩
      iexists d; iexact HQ
  · -- at the segment size, the pipeline non-nil: `cut`
    rw [decide_eq_false Hif]
    icases walHandleIn_fp P Mr w dir h2 TailMetaW $$ Hh2 with ⟨%fp2, Hfp2, %hfp2, Hback2⟩
    (try wp_auto)
    rw [decide_eq_false hfp2]
    wp_take_receipt as Hr1
    ihave Hh2 := Hback2 $$ Hfp2
    ihave Hr2 := (receipt_add h.pc 1).2 $$ [Hr Hr1]
    · iframe
    icases save_pc_bound Mr R jr r h.pc $$ Harea Hr2 with ⟨Hr2, %hpc⟩
    have hcuts : ∀ b ∈ h2.cuts, b < h2.H.length := fun b hb => by
      rw [ecuts] at hb; rw [hlenH]; have := hc b hb; omega
    have hpw : h2.cuts.Pairwise (· < ·) := by rw [ecuts]; exact hcp.2
    have hcpos : walCutPos (h2.H.map WalOpG.toM) h2.H.length := by rw [eH]; exact walCutPos_snap h.H md al
    have hsz2 : h2.md.length + (Mr.encState h2.st).length < 2 ^ 42 := by
      have := hS h2.st; rw [emd]; omega
    wp_apply (wp_cut R jr r w dir h2 hrest3 hst3 (by rw [epc]; omega) hcuts hpw
      hcpos (by rw [hlenH]; omega) hsz2 hcov hroom3) $$ [Hh2] as %err Hres
    · iframe Harea Hh2
    icases Hres with (⟨%herr, %h', Hh, %hh', #Hsyn⟩ | %herr)
    · obtain ⟨hH', hmd', hcuts', hrest', hst', -, -, hpc', hroom'⟩ := hh'
      subst herr
      rw [epc] at hpc'
      iapply fupd_wp
      imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hh Hr2] with ⟨Hw, Hown⟩
      · iframe Hpers Hheld
        ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
        rw [← hpc']
        iapply walHdl_close Sio P Mr w dir h' ⟨hrest', by rw [hst', hH']; exact hst3⟩
          (by rw [hmd', emd]; exact hmd) (fun _ => save_room_small _ _ _ hroom')
        iframe Hh Hr2
      imodintro
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hown]
      try wp_auto
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iframe Hw
      icases HQ with ⟨%d, HQ, %hd⟩
      iexists d
      iframe HQ
      rw [hd]
      iframe Hlb
      rw [← hlenH]
      iexact Hsyn
    · rcases err with ei | _
      rotate_left
      · exact absurd rfl herr.1
      have hq1 : q = 1 := hq.resolve_left herr.2
      subst hq1
      iapply fupd_wp
      imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hown
      · iframe Hpers Hheld
      imodintro
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hown]
      try wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact herr
      icases HQ with ⟨%d, HQ, -⟩
      iexists d; iexact HQ

end proof

section pre
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`SaveSnapshot` on `Create`'s `w` before the rename** (the state `pre`; see the file header). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.wp_pre
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre (GF := GF))
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.spec (GF := GF) (hG := hG))
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.spec
      (GF := GF) (hG := hG))
    (wp_GetIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF)
      (hG := hG))
    (wp_Marshal : go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specWalSnap (GF := GF) Mr)
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (w lg : Loc) (dir : GoString) (mds : GoSlice) (md : List w8) (e lt f : Loc) (snapi enti : w64)
    (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF) (S : List w8 → IProp GF)
    (lim : Nat) (out pend : List w8) (c : w32) (sp : Loc) (sm : SnapshotMetadataM) (al cs : Bool) :
  {{ ⌜sm.Index' = W64 0 ∨ cs = true⌝ ∗ ⌜(out ++ pend ++ snapFrame Mr c sm al).length ≤ lim⌝ ∗
      ⌜lim < 2 ^ 47⌝ ∗ ⌜walPreSyncOk f W S⌝ ∗ ⌜walPreSeekOk f W lim⌝ ∗
      io.writerStream (wal.fileWi f) lim W B ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.wal.SegmentSizeBytes ↦□ (W64 64000000) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ (null : Loc) ∗
      encEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗
      walPreIn w lg dir mds md e lt f snapi enti ∗ ownEncoder e (wal.fileWi f) c pend ∗
      W out ∗ walSnapAt Mr sp sm al cs }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"SaveSnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err;
      ∃ (snapi' enti' : w64), walPreIn w lg dir mds md e lt f snapi' enti' ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ (null : Loc) ∗
      ⌜(snapi' = snapi ∨ snapi' = sm.Index') ∧ (enti' = enti ∨ enti' = sm.Index')⌝ ∗
      ((⌜err = GoInterface.nil⌝ ∗
          ownEncoder e (wal.fileWi f) (hash.crc32.crc32c c (Mr.encSnap sm al)) [] ∗
          S (out ++ pend ++ snapFrame Mr c sm al)) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ ∃ (c' : w32) (pend' : List w8),
          ownEncoder e (wal.fileWi f) c' pend' ∗
          ((∃ a b : List w8, B a b) ∨ (∃ o : List w8, W o)))) }} := by
  wp_start as ⟨%hcs, %hlim, %hlim47, %hsync, %hseek, #Hw, #Hseg, Hfp, #Henv, #Hzap, #Hpb, Hpre, He, Hout, #Hs⟩
  ihave #Hs0 := Hs
  iunfold walSnapAt at Hs
  icases Hs with ⟨%sc, Hsr, -⟩
  ihave %Hspn := snapRoC_ne sp sc $$ Hsr
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  simp only [decide_eq_false Hspn]
  try wp_auto
  wp_apply (wp_Validate Mr sp sm al cs hcs) $$ []
  · iexact Hs0
  try wp_auto
  have hsz48 : (Mr.encSnap sm al).length < 2 ^ 48 := by
    have h1 := recEnc_length (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩)
    have h2 : (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩).length ≤
        (snapFrame Mr c sm al).length := by
      unfold snapFrame WalEnc.frame; simp only [List.length_append]; omega
    have h3 : (Mr.encSnap sm al).length ≤
        recSize (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩) := by
      have hne : ¬ (snapshotType = crcType ∧ Mr.encSnap sm al = []) := fun h => by
        exact absurd h.1 (by decide)
      unfold recSize recOf; simp only [if_neg hne]; omega
    unfold walRecEnc at h2
    simp only [List.length_append] at hlim; omega
  wp_apply (wp_Marshal sp sm al cs hsz48) $$ [] as %d ⟨%Hdn, Hd, Hdc⟩
  · iframe #
  try wp_auto
  iunfold walPreIn at Hpre
  icases Hpre with ⟨%locks, Hlg, #Hlgok, Hdir, Hmd, #Hmds, Hns, #Hmu, Henti, Hsnapi, Hfe, %Hen,
    Hlocks, Hls, Hcap, #Hlt⟩
  wp_apply wp_Lock $$ [] as ⟨Hown, -⟩
  · iexact Hmu
  try wp_auto
  simp only [go_etcd_io.etcd.server.v3.storage.wal.SnapshotType]
  try wp_auto
  have hT : (W64 5) = snapshotType := rfl
  have hfl : out.length + pend.length +
      (WalEnc.frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩)).length
      ≤ lim := by
    simp only [snapFrame, List.length_append] at hlim; omega
  have hsz : recSize (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩)
      < 2 ^ 47 := by
    have h1 : (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩).length =
        recSize (recOf ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩) :=
      recEnc_length _
    have h2 : (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al), Mr.encSnap sm al⟩).length ≤
        (WalEnc.frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap sm al),
          Mr.encSnap sm al⟩)).length := by
      unfold WalEnc.frame; simp only [List.length_append]; omega
    omega
  ipersist «$v0»
  ipersist Hd
  wp_apply (wp_encode e (wal.fileWi f) W B lim out pend c _ snapshotType (Mr.encSnap sm al) hsz hfl)
    $$ [Hw] [He Hout «$r0»] as %err ⟨%pend', He, #Hrec, Hres⟩
  · iexact Hw
  · iframe; iframe #
    iunfold encRecIn
    iexists _
    iframe «$r0»
    rw [hT]
    iframe #
    have hro : (recOf ⟨snapshotType, 0#32, Mr.encSnap sm al⟩).data = some (Mr.encSnap sm al) := by
      simp [recOf, snapshotType, crcType]
    rw [hro]
    simp only [recBytes]
    isplitl []
    · isplitr
      · ipureintro; exact Hdn
      · iexact Hd
    · ipureintro; simp
  icases Hres with (⟨%ys, ⟨%Herr, %Hys⟩, Hout⟩ | ⟨%a, %b, ⟨%Herr, %Hpe, %Hab⟩, Hbad⟩)
  rotate_left
  · -- the encode failed
    rcases err with ei | _
    rotate_left
    · exact absurd rfl Herr
    try wp_auto
    wp_apply wp_Unlock $$ [Hown]
    · iframe
      isplitl []
      · iexact Hmu
      inext; itrivial
    try wp_auto
    iapply HΦ
    iexists snapi, enti
    iunfold walPreIn
    isplitl [Hlg Hdir Hmd Hns Henti Hsnapi Hfe Hlocks Hls Hcap]
    · iexists locks
      iframe; iframe #; ipureintro; exact Hen
    iframe Hfp
    isplitr
    · ipureintro; exact ⟨Or.inl rfl, Or.inl rfl⟩
    iright
    isplitr
    · ipureintro; exact Herr
    iexists _, _
    iframe He
    ileft; iexists _, _; iexact Hbad
  subst Herr
  have hlen2 : (out ++ ys).length + pend'.length ≤ lim := by
    have := congrArg List.length Hys; simp only [List.length_append] at this ⊢; omega
  have heq : out ++ ys ++ pend' = out ++ pend ++ snapFrame Mr c sm al := by
    rw [List.append_assoc, Hys, snapFrame, List.append_assoc]
  try wp_auto
  ihave #HsIT := walSnapAt_idTerm Mr sp sm al cs $$ Hs0
  wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []
  · iexact HsIT
  wp_if_destruct
  all_goals (try (wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []; iexact HsIT))
  all_goals (try wp_auto)
  all_goals (try (wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []; iexact HsIT))
  all_goals (try wp_auto)
  all_goals wp_if_destruct
  all_goals (try (wp_apply (wp_GetIndex sp (sm.Index', sm.Term')) $$ []; iexact HsIT))
  all_goals (try wp_auto)
  all_goals (
    wp_apply (wp_tail w locks [] lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
    · iframe
    ihave #Hlt0 := Hlt
    iunfold fileutil.lockedFile at Hlt0
    iStructNamed Hlt0
    rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) (m := go!"Seek")]
    wp_call
    (try wp_auto)
    wp_apply (hseek (out ++ ys) (by omega)) $$ [Hout] as Hout
    · iexact Hout
    (try wp_auto)
    -- `curOff < SegmentSizeBytes || w.fp == nil`: `w.fp` is nil, so a `sync` either way
    by_cases Hif : sint.Z (W64 ((out ++ ys).length : Int)) < sint.Z (W64 64000000)
    all_goals (first | rw [decide_eq_true Hif] | rw [decide_eq_false Hif])
    all_goals (try wp_auto)
    all_goals (
    wp_apply (wp_sync w lg dir mds md e lt f _ _ W B S lim (out ++ ys) pend'
      (hash.crc32.crc32c c (Mr.encSnap sm al)) hlen2 hsync) $$ [Hw]
      [Hlg Hdir Hmd Hns Henti Hsnapi Hfe Hlocks Hls Hcap He Hout] as %err2 ⟨Hpre, He, Hres2⟩
    · iexact Hw
    · iframe; iframe #
      iunfold walPreIn; iexists locks; iframe; iframe #; ipureintro; exact Hen
    try wp_auto
    wp_apply wp_Unlock $$ [Hown]
    · iframe
      isplitl []
      · iexact Hmu
      inext; itrivial
    try wp_auto
    iapply HΦ
    iexists _, _
    iframe Hpre Hfp
    isplitr
    · ipureintro
      first
        | exact ⟨Or.inl rfl, Or.inl rfl⟩
        | exact ⟨Or.inl rfl, Or.inr rfl⟩
        | exact ⟨Or.inr rfl, Or.inl rfl⟩
        | exact ⟨Or.inr rfl, Or.inr rfl⟩
    icases Hres2 with (⟨%H0, HS⟩ | ⟨%H0, Hbad⟩)
    · ileft
      rw [heq]
      iframe; ipureintro; exact H0
    · iright
      isplitr
      · ipureintro; exact H0
      iexists _, _
      iframe He
      icases Hbad with (Hb | ⟨-, Hw'⟩)
      · ileft; iexists _, _; iexact Hb
      · iright; iexists _; iexact Hw'))

end pre

section proof2
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [FsStepSat (NoMapLockErr Sio)] (P : WalPbIn GF)
    (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_syncNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (Sio := Sio) (W := W) P Mr)
    (wp_syncPre : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre (GF := GF))
    (wp_encodeTail : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (W := W) Mr)
    (wp_encodeTailNE : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTailNoErr (Sio := Sio) (W := W) Mr)
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.spec (GF := GF) (hG := hG))
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.spec
      (GF := GF) (hG := hG))
    (wp_GetIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF)
      (hG := hG))
    (wp_Marshal : go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specWalSnap (GF := GF) Mr)
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_cut : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (Sio := Sio) (W := W) P Mr)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.spec (Sio := Sio) (W := W) P Mr := by
  intro R jr r w dir st sp md al cs sized Q
  cases st with
  | shared γ q =>
    exact go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.wp_shared P Mr wp_sync wp_syncNE wp_encodeTail
      wp_encodeTailNE wp_Validate wp_GetIndex wp_Marshal wp_cut wp_tail R jr r w dir γ q sp md al cs sized Q
  | pre lg mds mdb e lt f snapi enti Wr Br Sr lim out pend c =>
    exact go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.wp_pre Mr wp_syncPre wp_encode wp_Validate
      wp_GetIndex wp_Marshal wp_Lock wp_Unlock wp_tail w lg dir mds mdb e lt f snapi enti Wr Br Sr lim out pend c sp md al cs

end proof2

end EtcdGrove
end Perennial
