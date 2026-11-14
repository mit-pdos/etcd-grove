/-
`(*WAL).SaveSnapshot` (S/wal.go:1137-1162) over its callees: `sync` (`WAL.sync.spec`), the snapshot record's
encode on the tail (`encoder.encode.specTail`, a hypothesis until the tail's writer accepts writes past its
preallocated size), `ValidateSnapshotForWrite`, `Snapshot.GetIndex`, `MustMarshalMessage` of a `walpb.Snapshot`
(`specWalSnap`), Perennial's `Mutex`. The update commits at the call's first step on the unsealed handle
(`walTail_append`: `w.snapi` is raised after the encode, so the committed handle's `walMaxSnapIdx ≤ snapi`
fails in between); the handle is rebuilt after the encode and the raises (`SnapPure.lean`), then synced.
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshot
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTail
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessageWalSnap
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SnapPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound
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

/-- The snapshot record's size, from its encoding's bound. -/
theorem snap_recSize (c : w32) (d : List w8) (hd : d.length < 2 ^ 40) :
    recSize (recOf ⟨snapshotType, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 := by
  have := recSize_le snapshotType (hash.crc32.crc32c c d) d (by decide)
  omega

theorem walLastHS_snap (H : WalHist) (md : SnapshotMetadataM) :
    walLastHS (H ++ [WalOpG.snap md]) = walLastHS H := by
  simp [walLastHS, List.foldl_append]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_encodeTail : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (W := W) Mr)
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite.spec
      (GF := GF) (hG := hG))
    (wp_GetIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF)
      (hG := hG))
    (wp_Marshal : go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specWalSnap (GF := GF) Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.SaveSnapshot.spec (W := W) P Mr := by
  intro R jr r w dir sp md cs sized Q
  wp_start as ⟨#Harea, Hw, #Hs, %hcs, %hidx, %hsz, Hau⟩
  icases (walOpenWF_iff P Mr w dir).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, Hr⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %stp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hszb, ⟨hidx0, hidx1⟩, hmax⟩ := Hpure
  have hidx0' := hidx0 hD.1
  iunfold walTailW at Htw
  icases Htw with ⟨Hf, Hfdo, Hoff, Htk, %m, %bs, Hm, Hbs, %hmb, Hv⟩
  -- the commit, before the call's first step
  ihave #Harea0 := Harea
  iunfold WalFs.walAreaOk at Harea0
  icases Harea0 with ⟨#Hinv, -⟩
  have hfit : ∀ c, RecsFit walCodec (chainRecs walCodec c (opDs Mr (WalOpG.snap md : WalOpG WalEnt).toM)) :=
    fun c => recsFit_chainRecs_small c _ (by
      intro p hp
      simp only [WalOpG.toM, opDs, List.mem_singleton] at hp
      subst hp
      exact ⟨by show uint.nat snapshotType < 2 ^ 8; decide, by simpa using hsz⟩)
  have hfit' : (∀ b ∈ ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1,
        b ≤ ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1.length) →
      RecsFit walCodec (recsOfSegs walCodec Mr
        ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.1
        (segsOf (((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1.map WalOpG.toM)
          ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1)) →
      RecsFit walCodec (recsOfSegs walCodec Mr
        ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.1
        (segsOf ((((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1 ++
          [WalOpG.snap md]).map WalOpG.toM) ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1)) := by
    intro hc hold
    show RecsFit walCodec (allRecs Mr (h.H ++ [WalOpG.snap md]) h.md h.cuts)
    rw [allRecs_snoc Mr h.H h.md h.cuts _ hc]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hold x hx
    · exact hfit _ x hx
  -- the WALs' step bound at a look (`⧖ |H|`), raised by the receipt of the deferred `w.mu.Unlock`'s
  -- resolution, deposited by the commit right after it (`notes/bounds-plan.md`, "The WAL's segment sequence")
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walTail_steps walCodec Mr R jr r dir h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) $$ Hinv Hnc Htk [Hv]
    with ⟨Hnc, Htk, Hv, #Hstp⟩
  · unfold tailVar; iexact Hv
  imodintro
  iframe Hnc
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, #Hsync, -, -⟩
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
  wp_apply (wp_Validate Mr sp md cs hcs) $$ []
  · iexact Hs0
  try wp_auto
  wp_apply (wp_Marshal sp md cs (by omega)) $$ [] as %d ⟨%Hdn, Hd, Hdc⟩
  · iframe #
  try wp_auto
  wp_apply +noauto sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hown, -⟩
  wp_raise_receipt Hstp
  -- the commit, right after the lock
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walTail_append walCodec Mr R jr r w dir h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) (WalOpG.snap md) sized Q hfit'
    (snapOp_noMax md hidx) $$ Hinv Hnc Htk Hv Hopen Hau Hstp with ⟨Hnc, Htk, Hv, Hopen, #Hlb, HQ, %hcp⟩
  unfold tailVar
  imodintro
  iframe Hnc
  have hc : ∀ b ∈ h.cuts, b ≤ h.H.length := fun b hb => by
    simpa using walCutPos_le (hcp.1 b hb)
  try wp_auto
  simp only [go_etcd_io.etcd.server.v3.storage.wal.SnapshotType]
  try wp_auto
  have hT : (W64 5) = snapshotType := rfl
  ipersist «$v0»
  ipersist Hd
  have hguard := snap_guard Mr h md hc hsplit hD.1
  unfold snapRec at hguard
  have hpre : h.out ++ h.pend ++ frame (walRecEnc ⟨snapshotType, hash.crc32.crc32c (h.crc Mr)
      (Mr.encSnap md), Mr.encSnap md⟩) <+: (tailStream Mr (h.H ++ [WalOpG.snap md]) h.md h.cuts).drop h.o0 :=
    ⟨[], by rw [List.append_nil]; exact hguard⟩
  wp_apply (wp_encodeTail R jr r e f fd name dir h.γ h.ino (h.H ++ [WalOpG.snap md]) h.md h.cuts h.o0 h.sz
      h.out h.pend (h.crc Mr) _ snapshotType (Mr.encSnap md) (snap_recSize _ _ hsz) hpre hoff hszb)
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
    have hro : (recOf ⟨snapshotType, 0#32, Mr.encSnap md⟩).data = some (Mr.encSnap md) := by
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
  · -- the encode failed
    rcases err with ei | _
    rotate_left
    · exact absurd rfl herr
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
  ihave #HsIT := walSnapAt_idTerm Mr sp md cs $$ Hs0
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
  have heq' : out' ++ pend' = h.out ++ h.pend ++ frame (walRecEnc (snapRec Mr (h.crc Mr) md)) := by
    unfold snapRec; exact heq
  obtain ⟨hsplit2, hcrc2⟩ := WalHS.split_snap Mr h md hc hsplit hD.1 out' pend' sz' sv ev heq'
  have hmap : (h.H ++ [WalOpG.snap md]).map WalOpG.toM = h.H.map WalOpG.toM ++ [WalOpG.snap md] := by
    simp [WalOpG.toM]
  obtain ⟨hi1, hi2, hi3⟩ := snap_idx (h.H.map WalOpG.toM) md h.enti h.snapi hidx0' hidx1 hidx hmax
  rw [← hsv, ← hev, ← hmap] at hi1
  rw [← hsv, ← hmap] at hi2
  rw [← hsv, ← hev] at hi3
  ihave Hh2 : walHandleIn (W := W) P Mr w dir { h with H := h.H ++ [WalOpG.snap md], out := out', pend := pend', sz := sz', snapi := sv, enti := ev } TailMetaW
    $$ [Hlg Hdir Hdf Hdff Hmd Hsp Hdec Hrc Hns Henti Hsnapi He Henc Htw Hdh Hlocks Hls Hcap Hlks Hfp
      Hpipe Hopen]
  · iunfold walHandleIn
    iexists lg, df, stp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    rw [hcrc2]
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    ipureintro
    exact ⟨Hen, Hlt, hsplit2, hfd, hs1, hs2, ⟨fun _ => hi1, hi2⟩, hi3⟩
  wp_apply (wp_sync R jr r w dir { h with H := h.H ++ [WalOpG.snap md], out := out', pend := pend', sz := sz', snapi := sv, enti := ev } hD.1) $$ [Hh2] as %err Hres
  · iframe Harea Hh2
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hown]
  try wp_auto
  iapply HΦ
  icases Hres with (⟨%herr, Hh, #Hsyn⟩ | %herr)
  · ileft
    isplitr
    · ipureintro; exact herr
    icases HQ with ⟨%d, HQ, %hd⟩
    isplitl [Hh Hr]
    · iapply (walOpenWF_iff P Mr w dir).2
      iexists _
      ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
      iframe Hh
      simp only
      iframe Hr
      ipureintro
      refine ⟨⟨hD.1, ?_⟩, hmd⟩
      show h.st = walLastHS ((h.H ++ [WalOpG.snap md]).map WalOpG.toM)
      rw [hmap, walLastHS_snap]; exact hD.2
    iexists d
    iframe HQ
    rw [hd]
    iframe Hlb
    have hl : (h.H ++ [WalOpG.snap md]).length = h.H.length + 1 := by simp
    rw [← hl]
    iexact Hsyn
  · iright
    isplitr
    · ipureintro; exact herr
    icases HQ with ⟨%d, HQ, -⟩
    iexists d; iexact HQ

end proof

end EtcdGrove
end Perennial
