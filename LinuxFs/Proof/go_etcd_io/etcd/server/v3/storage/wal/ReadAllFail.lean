/- Lean-first (no Rocq counterpart).

# What `ReadAll`'s error exits leave (`walReadFailedF`; unit `closefailed`)

`ReadAll` registers the tail at its look at the invariant before the loop (`walInv_readCommitReg`). An
exit before `ZeroToEnd` (the loop's arms, the decoder's error at the mode check) holds it registered, not
yet zeroed, idle: it unregisters it on the spot (`walInv_untailPend`, `walInvBody_untailL` with the
pending token). An exit after the fdatasync that follows `ZeroToEnd` (the directory's `Fsync`, `syncDir`,
`!match`) holds its key and the tail synced (`TailMetaS`): it unregisters it the same way
(`walInv_untailKey`, `walInvBody_untail`). Both leave the failed handle's idle form (`walFailIdle`), so
`Close` syncs an idle tail and puts it back as `Close.specOpening` does. The two exits in between
(`ZeroToEnd`'s error, the fdatasync's) leave the tail lent (`walFailLent`), for `Close`'s `w.sync()`.

`walReadFailedF_idle`/`walReadFailedF_lent` build the sealed handle from the pieces each exit holds.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.UnregLent
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A registered, not yet zeroed tail unregistered** (see the file header). -/
theorem walInv_untailPend (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG)
    (hTM : TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γ]> ∅) -∗ walPendTok (W := W) dir γ k -∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs
      ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗ walTailsFrag (W := W) ∅ ∗
        osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro #Hinv Hnc Htf Htk Hv Hm Hb
  iapply walInv_step walCodec Mr R jr r
    iprop(walTailsFrag (W := W) (<[dir := γ]> ∅) ∗ walPendTok (W := W) dir γ k ∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    iprop(walTailsFrag (W := W) ∅ ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨Htf, Htk, Hv, Hm, Hbs⟩
      imod walInvBody_untailL Mr R jr r s dir γ γ k true H md cuts wr ino m bs hTM hwr
        $$ Hb Htf Htk Hv Hm Hbs with ⟨%d, -, Hb, Htf, Hm, Hbs⟩
      imodintro
      iframe)
    $$ Hinv Hnc [Htf Htk Hv Hm Hb]
  iframe

/-- **A synced tail unregistered by its key** (see the file header). -/
theorem walInv_untailKey (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG) (hTM : TailMetaS m bs)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γ]> ∅) -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs
      ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗ walTailsFrag (W := W) ∅ ∗
        osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro #Hinv Hnc Htf Htk Hv Hm Hb
  iapply walInv_step walCodec Mr R jr r
    iprop(walTailsFrag (W := W) (<[dir := γ]> ∅) ∗ walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    iprop(walTailsFrag (W := W) ∅ ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨Htf, Htk, Hv, Hm, Hbs⟩
      imod walInvBody_untail Mr R jr r s dir γ γ H md cuts wr ino m bs hTM hwr
        $$ Hb Htf Htk Hv Hm Hbs with ⟨%d, -, Hb, Htf, Hm, Hbs⟩
      imodintro
      iframe)
    $$ Hinv Hnc [Htf Htk Hv Hm Hb]
  iframe

end iris

section intro
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- The fields every failed handle holds, but the tail (`walFailH` without its last disjunct). -/
def walFailCommon (w : Loc) (dir : GoString) (lg : Loc) (locks : GoSlice) (ls : List Loc) (lt fp : Loc) (j : Ino)
    (X : List GoString) (hj : NamesH) (gs0 : List SegG) (gL : SegG) (fls : List Loc) (df : Loc)
    (dfd : w64) (ph : DirPhS) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* (ls ++ [lt]) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗ walPipeH fp dir j 0 ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗ encEnv ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd j ph ∗ osCallPerm (1 : Qp).half.half ∗
    osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    walOutFrag (W := W) ⟨(gs0 ++ [gL]).map (·.ino), [(j, .except X)], [dir]⟩ ∗
    walNamesFrag (W := W) none ∗ walDirKey (W := W) dir j X ∗
    ⌜ls.length = gs0.length ∧ (walNames hj.cur).getLast? = some gL.name ∧
      hj.cur !! gL.name = some (.file gL.ino) ∧ (∀ t ∈ walTmps, t ∈ X) ∧
      ∀ g ∈ gs0, g.om.size = g.bs.length⌝ ∗
    ([∗list] g ∈ gs0, segRes g) ∗ ([∗list] k ↦ g ∈ gs0, walTieFile dir true fls k g) ∗
    ([∗list] k ↦ lf ∈ ls ++ [lt], fileutil.lockedFile lf (fls.getD k null)))

/-- `walReadFailedF` from its parts. -/
theorem walReadFailedF_intro (Mr : WalMarshal) (w : Loc) (dir : GoString) (lg : Loc) (locks : GoSlice) (ls : List Loc)
    (lt fp : Loc) (j : Ino) (X : List GoString) (hj : NamesH) (gs0 : List SegG) (gL : SegG)
    (fls : List Loc) (df : Loc) (dfd : w64) (ph : DirPhS) :
    walReadFailed (W := W) w dir ∗ walFailCommon w dir lg locks ls lt fp j X hj gs0 gL fls df dfd ph ∗
      (walFailIdle w dir (fls.getD gs0.length null) gL ∨
        walFailLent Mr w dir X hj (fls.getD gs0.length null) gL) ⊢
      walReadFailedF Mr w dir := by
  unfold walReadFailedF walFailH walFailCommon
  iintro ⟨Hf, ⟨Hlg, #Hz, Hdir, Hlocks, Hls, Hfp, Hpipe, Hns, #Hmu, #Henv, Hdff, Hdf, Hdfs, Hph, Hn, Hout,
    Hnf, #Hk, %hp, Hsegs, Hfiles, #Hlks⟩, Ht⟩
  iframe Hf
  iexists lg, locks, ls, lt, fp, j, X, hj, gs0, gL, fls, df, dfd, ph
  iframe
  iframe #
  ipureintro; exact hp

/-- `walReadFailedF` into its parts. -/
theorem walReadFailedF_elim (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    walReadFailedF Mr w dir ⊢ walReadFailed (W := W) w dir ∗
      ∃ (lg : Loc) (locks : GoSlice) (ls : List Loc) (lt fp : Loc) (j : Ino) (X : List GoString) (hj : NamesH)
        (gs0 : List SegG) (gL : SegG) (fls : List Loc) (df : Loc) (dfd : w64) (ph : DirPhS),
      walFailCommon w dir lg locks ls lt fp j X hj gs0 gL fls df dfd ph ∗
      (walFailIdle w dir (fls.getD gs0.length null) gL ∨
        walFailLent Mr w dir X hj (fls.getD gs0.length null) gL) := by
  unfold walReadFailedF walFailH walFailCommon
  iintro ⟨Hf, %lg, %locks, %ls, %lt, %fp, %j, %X, %hj, %gs0, %gL, %fls, %df, %dfd, %ph, Hlg, #Hz, Hdir,
    Hlocks, Hls, Hfp, Hpipe, Hns, #Hmu, #Henv, Hdff, Hdf, Hdfs, Hph, Hn, Hout, Hnf, #Hk, %hp, Hsegs,
    Hfiles, #Hlks, Ht⟩
  iframe Hf
  iexists lg, locks, ls, lt, fp, j, X, hj, gs0, gL, fls, df, dfd, ph
  iframe
  iframe #
  ipureintro; exact hp

/-- The failed ghost handle holds the lock token (as `walOpening_lockedTok`). -/
theorem walReadFailed_lockedTok (w : Loc) (dir : GoString) :
    walReadFailed (W := W) w dir ⊢ walLockedTok (W := W) := by
  unfold walReadFailed walHandleP
  iintro ⟨%γ, -, -, -, Hl⟩
  iexact Hl

/-- The synced or unsynced halves of the tail, as a segment of the same inode and size
(`WAL__CloseOpening`'s `syncOut_seg`). -/
theorem syncOut_segF (g : SegG) (hlen : g.bs.length = g.om.size) (P : Prop) :
    ((⌜P⌝ ∗ osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om.synced ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) (g.bs.map (fun x => durB x.1))) ∨
      (⌜¬ P⌝ ∗ osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs)) ⊢
      ∃ g' : SegG, ⌜g'.ino = g.ino ∧ g'.om.size = g'.bs.length⌝ ∗ segRes (L := hG.goose_localGS) g' := by
  iintro (⟨-, Hm, Hb⟩ | ⟨-, Hm, Hb⟩)
  · iexists { g with om := g.om.synced, bs := g.bs.map (fun x => durB x.1) }
    unfold segRes
    iframe Hm Hb
    ipureintro
    exact ⟨rfl, by simp [OsMeta.synced, hlen]⟩
  · iexists g
    unfold segRes
    iframe Hm Hb
    ipureintro
    exact ⟨rfl, hlen.symm⟩

end intro

end WalFs
end EtcdGrove
end Perennial

end
