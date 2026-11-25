/- Lean-first (no Rocq counterpart).

# What `ReadAll`'s error exits leave (`walReadFailedF`; unit `closefailed`)

`ReadAll` registers the tail at its look at the invariant before the loop (`walInv_readCommitReg`). An
exit before `ZeroToEnd` (the loop's arms, the decoder's error at the mode check) holds it registered, not
yet zeroed, idle: it unregisters it on the spot (`walInv_untailPend`, `walInvBody_untailL` with the
pending token). An exit after the fdatasync that follows `ZeroToEnd` (the directory's `Fsync`, `syncDir`,
`!match`) holds its key and the tail synced (`TailMetaS`): it unregisters it the same way
(`walInv_untailKey`, `walInvBody_untail`). Both leave the failed handle's idle form (`walFailIdle`), so
`Close` syncs an idle tail and puts it back as `Close.spec` (state `opening`) does. The two exits in between
(`ZeroToEnd`'s error, the fdatasync's) leave the tail lent (`walFailLent`), for `Close`'s `w.sync()`.

`walReadFailedF_idle`/`walReadFailedF_lent` build the sealed handle from the pieces each exit holds.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.UnregLent
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenPinTake
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCommit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

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
theorem walInv_untailPend {Lk : GMap GoString Nat} (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG)
    (hTM : TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γ]> ∅) Lk -∗ walPendTok (W := W) dir γ k -∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs
      ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗ walTailsFrag (W := W) ∅ ∗
        osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro #Hinv Hnc Htf Htk Hv Hm Hb
  iapply walInv_step walCodec Mr R jr r
    iprop(walTailsFrag (W := W) (<[dir := γ]> ∅) Lk ∗ walPendTok (W := W) dir γ k ∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    iprop(walTailsFrag (W := W) ∅ ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨Htf, Htk, Hv, Hm, Hbs⟩
      imod walInvBody_lksSet (L := L) walCodec Mr R jr r s _ Lk ∅ (LksOk.empty s) $$ Hb Htf with ⟨Hb, Htf⟩
      imod walInvBody_untailL Mr R jr r s dir γ γ k true H md cuts wr ino m bs hTM hwr
        $$ Hb Htf Htk Hv Hm Hbs with ⟨%d, -, Hb, Htf, Hm, Hbs⟩
      imodintro
      iframe)
    $$ Hinv Hnc [Htf Htk Hv Hm Hb]
  iframe

/-- **A synced tail unregistered by its key** (see the file header). -/
theorem walInv_untailKey {Lk : GMap GoString Nat} (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG) (hTM : TailMetaS m bs)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailsFrag (W := W) (<[dir := γ]> ∅) Lk -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs
      ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗ walTailsFrag (W := W) ∅ ∗
        osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro #Hinv Hnc Htf Htk Hv Hm Hb
  iapply walInv_step walCodec Mr R jr r
    iprop(walTailsFrag (W := W) (<[dir := γ]> ∅) Lk ∗ walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    iprop(walTailsFrag (W := W) ∅ ∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨Htf, Htk, Hv, Hm, Hbs⟩
      imod walInvBody_lksSet (L := L) walCodec Mr R jr r s _ Lk ∅ (LksOk.empty s) $$ Hb Htf with ⟨Hb, Htf⟩
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
    os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd j ph ∗ osCallPerm (callKey W.roots dir) (1 : Qp).half.half ∗
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
  unfold walReadFailed walHandleP walLockedTok
  iintro ⟨%γ, %i, %I, -, -, -, Hl, -⟩
  iexists I; iexact Hl

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

/-- `walTie_files` (`CloseOpeningFiles.lean`) for a prefix of the files: the streams of `fs` give the halves of
`gs` and their files, the file list `fls` at least as long. -/
theorem walTie_filesLe (dir : GoString) (write : Bool) :
    ∀ (gs : List SegG) (fs : List (DecFile GF)) (fls : List Loc),
    fs.length = gs.length → gs.length ≤ fls.length →
    (∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
      ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[k]? = some f ∧
        F.S = walFileS f fd (child dir g.name) (walSegFd write lo lk g.ino) g) →
    ([∗list] F ∈ fs, ∃ r, F.S r) ⊢
      ([∗list] g ∈ gs, segRes (L := hG.goose_localGS) g) ∗
      [∗list] k ↦ g ∈ gs, walTieFile dir write fls k g
  | [], [], _, _, _, _ => by
    iintro -
    isplitl
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | g :: gs, F :: fs, f0 :: fls, hl1, hl2, hk => by
    obtain ⟨f, fd, lo, lk, hf, hS⟩ := hk 0 F g rfl rfl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    have e : ∀ (k : Nat) (g' : SegG), walTieFile (GF := GF) dir write (f0 :: fls) (k + 1) g' =
        walTieFile dir write fls k g' := by
      intro k g'; simp [walTieFile]
    have ih := walTie_filesLe dir write gs fs fls (by simpa using hl1) (by simpa using hl2)
      (fun k F' g' h1 h2 => hk (k + 1) F' g' h1 h2)
    iintro H
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨⟨%r, Hs⟩, H⟩
    rw [hS]
    unfold walFileS
    icases Hs with ⟨-, Hf, Hfd, Hlks, -, Hm, Hb⟩
    ihave Hlks := fdLocksW_locks _ _ $$ Hlks
    icases ih $$ H with ⟨Hsg, Hfs⟩
    isplitl [Hm Hb Hsg]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe Hsg
      unfold segRes; iframe
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      simp only [e]
      iframe Hfs
      unfold walTieFile
      iexists fd, lo, lk
      iframe
  | [], _ :: _, _, hl1, _, _ => by simp at hl1
  | _ :: _, [], _, hl1, _, _ => by simp at hl1
  | _ :: _, _ :: _, [], _, hl2, _ => by simp at hl2

/-- **A failed handle, its tail put back** (`walFailIdle`), from the pieces `ReadAll`'s exits hold: the
non-tail files' streams (`fsI`, read as `gs0`), the tail's halves `gT` and file `ft`, the encoder. -/
theorem walReadFailedF_idleIntro (Mr : WalMarshal) (w : Loc) (dir : GoString) (lg : Loc) (locks : GoSlice)
    (ls : List Loc) (lt fp : Loc) (j : Ino) (X : List GoString) (hj : NamesH) (gs0 : List SegG) (gL : SegG)
    (fls : List Loc) (df : Loc) (dfd : w64) (ph : DirPhS) (fsI : List (DecFile GF)) (gT : SegG)
    (fdt : w64) (d : OsFd) (e : Loc)
    (hfl : fsI.length = gs0.length) (hll : ls.length = gs0.length) (hfll : gs0.length ≤ fls.length)
    (hfk : ∀ (k : Nat) (F : DecFile GF) (g : SegG), fsI[k]? = some F → gs0[k]? = some g →
      ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[k]? = some f ∧
        F.S = walFileS f fd (child dir g.name) (walSegFd true lo lk g.ino) g)
    (hlast : (walNames hj.cur).getLast? = some gL.name) (hiL : hj.cur !! gL.name = some (.file gL.ino))
    (hXt : ∀ t ∈ walTmps, t ∈ X) (hsz : ∀ g ∈ gs0, g.om.size = g.bs.length)
    (hgT : gT.ino = gL.ino ∧ gT.om.size = gT.bs.length) (hd : d.ino = gL.ino) :
    walReadFailed (W := W) w dir ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗ walPipeH fp dir j 0 ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
        (BI.pure True : IProp GF) ∗ encEnv ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
      os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd j ph ∗ osCallPerm (callKey W.roots dir) (1 : Qp).half.half ∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      walOutFrag (W := W) ⟨(gs0 ++ [gL]).map (·.ino), [(j, .except X)], [dir]⟩ ∗
      walNamesFrag (W := W) none ∗ walDirKey (W := W) dir j X ∗
      ([∗list] k ↦ lf ∈ ls ++ [lt], fileutil.lockedFile lf (fls.getD k null)) ∗
      ([∗list] F ∈ fsI, ∃ r, F.S r) ∗
      walTailsFrag (W := W) ∅ ∗ segRes gT ∗ os.ownFile (fls.getD gs0.length null) fdt (child dir gL.name) (DFrac.own 1) ∗
      osFd fdt (DFrac.own 1) d ∗ fdLocks fdt d ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
      (⌜e = null⌝ ∨ ∃ c : w32, ownEncoder e (wal.fileWi (fls.getD gs0.length null)) c []) ⊢
    walReadFailedF Mr w dir := by
  iintro ⟨Hf, Hlg, #Hz, Hdir, Hlocks, Hls, Hfp, Hpipe, Hns, #Hmu, #Henv, Hdff, Hdf, Hdfs, Hph, Hn, Hout,
    Hnf, #Hk, #Hlks, Hst, Htf, HsT, Hft, Hfdt, Hlkt, He, Henc⟩
  icases walTie_filesLe dir true gs0 fsI fls hfl hfll hfk $$ Hst with ⟨Hsegs, Hfiles⟩
  iapply walReadFailedF_intro Mr w dir lg locks ls lt fp j X hj gs0 gL fls df dfd ph
  iframe Hf
  unfold walFailCommon
  iframe
  isplitr
  · iframe #
    ipureintro; exact ⟨hll, hlast, hiL, hXt, hsz⟩
  ileft
  unfold walFailIdle
  iframe Htf
  iexists gT, fdt, d, e
  iframe
  ipureintro; exact ⟨hgT.1, hgT.2, hd⟩

/-- **A failed handle, its tail lent** (`walFailLent`), from the pieces `ReadAll`'s exits at `ZeroToEnd`'s and
its fdatasync's errors hold. -/
theorem walReadFailedF_lentIntro (Mr : WalMarshal) (w : Loc) (dir : GoString) (lg : Loc) (locks : GoSlice)
    (ls : List Loc) (lt fp : Loc) (j : Ino) (X : List GoString) (hj : NamesH) (gs0 : List SegG) (gL : SegG)
    (fls : List Loc) (df : Loc) (dfd : w64) (ph : DirPhS) (fsI : List (DecFile GF)) (γt : GName)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz k : Nat) (fdt : w64)
    (segs : List SegG) (gLL : SegG)
    (hfl : fsI.length = gs0.length) (hll : ls.length = gs0.length) (hfll : gs0.length ≤ fls.length)
    (hfk : ∀ (k : Nat) (F : DecFile GF) (g : SegG), fsI[k]? = some F → gs0[k]? = some g →
      ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[k]? = some f ∧
        F.S = walFileS f fd (child dir g.name) (walSegFd true lo lk g.ino) g)
    (hlast : (walNames hj.cur).getLast? = some gL.name) (hiL : hj.cur !! gL.name = some (.file gL.ino))
    (hXt : ∀ t ∈ walTmps, t ∈ X) (hsz : ∀ g ∈ gs0, g.om.size = g.bs.length)
    (hwr : o0 = (tailStream Mr H md cuts).length) (hcl : CloseLeftOk X hj segs gLL) (hgLL : gLL.ino = gL.ino) :
    walReadFailed (W := W) w dir ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗ walPipeH fp dir j 0 ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
      sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
        (BI.pure True : IProp GF) ∗ encEnv ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
      os.ownFile df dfd dir (DFrac.own 1) ∗ osDirFdS dfd j ph ∗ osCallPerm (callKey W.roots dir) (1 : Qp).half.half ∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      walOutFrag (W := W) ⟨(gs0 ++ [gL]).map (·.ino), [(j, .except X)], [dir]⟩ ∗
      walNamesFrag (W := W) none ∗ walDirKey (W := W) dir j X ∗
      ([∗list] k ↦ lf ∈ ls ++ [lt], fileutil.lockedFile lf (fls.getD k null)) ∗
      ([∗list] F ∈ fsI, ∃ r, F.S r) ∗
      walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) ∗
      (walTailP (W := W) (fls.getD gs0.length null) fdt (child dir gL.name) dir γt gL.ino H md cuts o0 sz [] k false
          (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0) ∨
        walTailPE (W := W) Mr (fls.getD gs0.length null) fdt (child dir gL.name) dir γt gL.ino H md cuts o0 k) ⊢
    walReadFailedF Mr w dir := by
  iintro ⟨Hf, Hlg, #Hz, Hdir, Hlocks, Hls, Hfp, Hpipe, Hns, #Hmu, #Henv, Hdff, Hdf, Hdfs, Hph, Hn, Hout,
    Hnf, #Hk, #Hlks, Hst, Htf, He, Ht⟩
  icases walTie_filesLe dir true gs0 fsI fls hfl hfll hfk $$ Hst with ⟨Hsegs, Hfiles⟩
  iapply walReadFailedF_intro Mr w dir lg locks ls lt fp j X hj gs0 gL fls df dfd ph
  iframe Hf
  unfold walFailCommon
  iframe
  isplitr
  · iframe #
    ipureintro; exact ⟨hll, hlast, hiL, hXt, hsz⟩
  iright
  unfold walFailLent
  iexists γt, H, md, cuts, o0, sz, k, fdt
  iframe
  ipureintro; exact ⟨hwr, segs, gLL, hcl, hgLL⟩

theorem osCallPerm_halves' (k : GoString) :
    osCallPerm (L := hG.goose_localGS) k (1 : Qp).half.half ∗
      osCallPerm (L := hG.goose_localGS) k (1 : Qp).half.half ⊢
      osCallPerm (L := hG.goose_localGS) k (1 : Qp).half := by
  have h := osCallPerm_split (L := hG.goose_localGS) k (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.2

theorem pipeTmp_mem_walTmpsF (n : Nat) : pipeTmp n ∈ walTmps := by
  unfold pipeTmp walTmps; split <;> simp

end intro

section streams
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- The loop's streams: those it left behind (`fs.take (kD + k)`) and the decoder's (`fsD.drop k`). -/
theorem streams_loop (fs fsD : List (DecFile GF)) (kD k : Nat) (h : fsD = fs.drop kD) :
    ([∗list] F ∈ fs.take (kD + k), ∃ q, F.S q) ∗ ([∗list] F ∈ fsD.drop k, ∃ q, F.S q) ⊢
      [∗list] F ∈ fs, ∃ q, F.S q := by
  subst h
  rw [List.drop_drop]
  have e := (BigSepL.bigSepL_append (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))
    (l₁ := fs.take (kD + k)) (l₂ := fs.drop (kD + k)))
  rw [List.take_append_drop] at e
  iintro ⟨H1, H2⟩
  iapply e.2
  iframe

/-- Every file's stream, out of the decoder's post (any of its arms). -/
theorem decPostB_streams (C : WalCodec) (d rp : Loc) (IoE : GoInterface → Prop) (eof ueof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32) (err : GoInterface) :
    decPostB C d rp IoE eof ueof fs off c err ⊢ [∗list] F ∈ fs, ∃ q, F.S q := by
  have hm : ∀ k, ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ ([∗list] F ∈ fs.drop k, ∃ q, F.S q) ⊢
      [∗list] F ∈ fs, ∃ q, F.S q := fun k => by
    have := streams_loop (GF := GF) fs fs 0 k (by simp)
    simpa using this
  unfold decPostB
  iintro (⟨%k, Hk, Hm⟩ | ⟨-, -, -, %k, %off', %c', Hk, Hd⟩ | ⟨%k, %s, %off', %c', -, Hk, Hd⟩)
  · iapply hm k
    iframe Hk
    split
    · icases Hm with ⟨-, -, Hd⟩
      iapply ownDecoder_streams $$ Hd
    · icases Hm with ⟨-, -, Hd⟩
      iapply ownDecoder_streams $$ Hd
  · iapply hm k
    iframe Hk
    iapply ownDecoder_streams $$ Hd
  · iapply hm k
    iframe Hk
    iapply ownDecoder_streams $$ Hd

/-- The loop's streams at its exit: those it left behind (`fs.take kD`) and the decoder's post's. -/
theorem streams_loop0 (fs fsD : List (DecFile GF)) (kD : Nat) (h : fsD = fs.drop kD) :
    ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ∗ ([∗list] F ∈ fsD, ∃ q, F.S q) ⊢
      [∗list] F ∈ fs, ∃ q, F.S q := by
  have := streams_loop (GF := GF) fs fsD kD 0 h
  simpa using this

/-- Per-file facts of a list, for a prefix of it. -/
theorem prefix_facts {α β : Type _} {fs fsI X : List α} {gs gs0 Y : List β} (P : Nat → α → β → Prop)
    (hfs : fs = fsI ++ X) (hgs : gs = gs0 ++ Y)
    (h : ∀ k F g, fs[k]? = some F → gs[k]? = some g → P k F g) :
    ∀ k F g, fsI[k]? = some F → gs0[k]? = some g → P k F g := by
  intro k F g h1 h2
  apply h k F g
  · rw [hfs, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1]; exact h1
  · rw [hgs, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h2).1]; exact h2

end streams

section exits
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- **An exit of `ReadAll` before `ZeroToEnd`** (see the file header): every file's stream and the tail
registered, not yet zeroed; the tail unregistered (`walInv_untailPend`), the update committed unchanged and
the ghost handle failed (`readAll_failWpQ`), the handle `walReadFailedF` (idle). -/
theorem readAll_failPend {Lk : GMap GoString Nat} (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString)
    (sn : w64 × w64) (Q : WalDur → IProp GF) (dc : WalDur) (e : Expr) (Φ : val → IProp GF)
    (h : toVal e = none) (lg : Loc) (locks : GoSlice) (lfs fls : List Loc) (fp : Loc) (j : Ino)
    (X : List GoString) (hj : NamesH) (gs : List SegG) (fs : List (DecFile GF)) (df : Loc) (dfd : w64)
    (ph : DirPhS) (γt : GName) (k : Nat) (d0 : WalDur) (lay : WalLay) (gl : SegG)
    (hgl : gs.getLast? = some gl) (hfl : fs.length = gs.length) (hll : lfs.length = gs.length)
    (hfll : fls.length = gs.length)
    (hfk : ∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
      F.bs = g.bs.map (·.1) ∧ hj.cur !! g.name = some (.file g.ino) ∧
      ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[k]? = some f ∧
        F.S = walFileS f fd (child dir g.name) (walSegFd true lo lk g.ino) g)
    {ic : Nat} (hlastN : (walNames hj.cur).getLast? = some gl.name) (hXt : ∀ t ∈ walTmps, t ∈ X)
    (hsz : ∀ g ∈ gs, g.om.size = g.bs.length)
    (hTM : TailMetaR gl.om gl.bs ∧ (∀ z, gl.om.zf = some z → gl.om.size ≤ z) ∧ ∀ y ∈ gl.bs, y = Fs.durB y.1)
    (hwr : lay.wr = (tailStream Mr d0.H d0.metadata lay.cuts).length) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) walCodec Mr R jr r -∗ walOpening (W := W) w dir sn ic -∗ Q dc -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg -∗ zapLoggerOk lg -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks -∗ locks ↦* lfs -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp -∗ walPipeH fp dir j 0 -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false -∗
      sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
        (BI.pure True : IProp GF) -∗ encEnv -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df -∗
      os.ownFile df dfd dir (DFrac.own 1) -∗ osDirFdS dfd j ph -∗ osCallPerm (callKey R dir) (1 : Qp).half.half -∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      walOutFrag (W := W) ⟨gs.map (·.ino), [(j, .except X)], [dir]⟩ -∗
      walNamesFrag (W := W) none -∗ walDirKey (W := W) dir j X -∗
      ([∗list] k ↦ lf ∈ lfs, fileutil.lockedFile lf (fls.getD k null)) -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ (null : Loc) -∗
      ([∗list] F ∈ fs, ∃ q, F.S q) -∗
      walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) Lk -∗ walPendTok (W := W) dir γt k -∗
      (letI := walAllG (W := W); ghostVar γt (1 : Qp).half (tailG d0 lay gl.ino none)) -∗
      (∀ d, Q d -∗ walReadFailedF Mr w dir -∗ WP e {{ Φ }}) -∗ WP e {{ Φ }} := by
  iintro #Hinv Hgh HQ Hlg #Hz Hdir Hlocks Hls Hfp Hpipe Hns #Hmu #Henv Hdff Hdf Hdfs Hph Hn Hout Hnf #Hk
    #Hlks He Hst Htf Htk Hv Hcont
  obtain ⟨gs0, rfl⟩ := List.getLast?_eq_some_iff.1 hgl
  obtain ⟨fsI, Fl, rfl⟩ : ∃ fsI Fl, fs = fsI ++ [Fl] := by
    rcases List.eq_nil_or_concat fs with h0 | ⟨L, b, h0⟩
    · subst h0; simp at hfl
    · exact ⟨L, b, by simpa using h0⟩
  obtain ⟨ls, lt, rfl⟩ : ∃ ls lt, lfs = ls ++ [lt] := by
    rcases List.eq_nil_or_concat lfs with h0 | ⟨L, b, h0⟩
    · subst h0; simp at hll
    · exact ⟨L, b, by simpa using h0⟩
  have hfI : fsI.length = gs0.length := by simpa using hfl
  have hlI : ls.length = gs0.length := by simpa using hll
  obtain ⟨-, hiL, fl, fdl, lo, lk, hflk, hS⟩ := hfk gs0.length Fl gl
    (by rw [List.getElem?_append_right (by omega)]; simp [hfI]) (by simp)
  have hgetD : fls.getD gs0.length null = fl := by
    rw [List.getD_eq_getElem?_getD, hflk]; rfl
  icases (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ Hst with ⟨Hst, ⟨%ql, Hsl⟩⟩
  rw [hS]
  iunfold walFileS at Hsl
  icases Hsl with ⟨-, Hft, Hfdt, Hlkt, -, Hm, Hb⟩
  ihave Hlkt := fdLocksW_locks _ _ $$ Hlkt
  iapply wp_notCrashed_acc _ _ h
  iintro Hnc
  imod walInv_untailPend (L := hG.goose_localGS) Mr R jr r dir γt k d0.H d0.metadata lay.cuts lay.wr gl.ino
      gl.om gl.bs hTM hwr $$ Hinv Hnc Htf Htk [Hv] Hm Hb with ⟨Hnc, Htf, Hm, Hb⟩
  · unfold tailVar tailG; iexact Hv
  iframe Hnc
  imodintro
  iapply readAll_failWpQ walCodec Mr R jr r w dir sn Q dc e Φ h $$ Hinv Hgh HQ
  iintro %dq HQ Hfail
  iapply Hcont $$ HQ
  rw [← hgetD] at *
  icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
  ihave Hph := walPerm_toW hWR dir _ $$ Hph
  iapply walReadFailedF_idleIntro Mr w dir lg locks ls lt fp j X hj gs0 gl fls df dfd ph fsI gl fdl
    (walSegFd true lo lk gl.ino) null hfI hlI (by rw [hfll]; simp)
    (fun k F g h1 h2 => (hfk k F g (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1]; exact h1)
      (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h2).1]; exact h2)).2.2)
    hlastN hiL hXt (fun g hg => hsz g (List.mem_append_left _ hg))
    ⟨rfl, hsz gl (by simp)⟩ rfl
  iframe
  iframe #
  isplitl [Hm Hb]
  · unfold segRes; iframe
  ileft; ipureintro; rfl

/-- **An exit of `ReadAll` after the fdatasync that follows `ZeroToEnd`** (see the file header): the non-tail
files' streams, the tail's pieces (`walTailW … TailMetaS` unfolded: its file, fd, key, synced halves, record),
the encoder (nil, or `!match`'s over the tail); the tail unregistered by its key (`walInv_untailKey`), the
update committed unchanged and the ghost handle failed (`readAll_failWpQ`), the handle `walReadFailedF`
(idle). -/
theorem readAll_failSynced {Lk : GMap GoString Nat} (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString)
    (sn : w64 × w64) (Q : WalDur → IProp GF) (dc : WalDur) (e : Expr) (Φ : val → IProp GF)
    (h : toVal e = none) (lg : Loc) (locks : GoSlice) (ls : List Loc) (lt : Loc) (fls : List Loc) (fp : Loc)
    (j : Ino) (X : List GoString) (hj : NamesH) (gs0 : List SegG) (gl : SegG) (fsI : List (DecFile GF))
    (df : Loc) (dfd : w64) (ph : DirPhS) (γt : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 : Nat) (m : OsMeta) (bs : List ByteG) (fdl : w64) (enc : Loc)
    (hfI : fsI.length = gs0.length) (hlI : ls.length = gs0.length) (hfll : gs0.length ≤ fls.length)
    (hfk : ∀ (k : Nat) (F : DecFile GF) (g : SegG), fsI[k]? = some F → gs0[k]? = some g →
      ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[k]? = some f ∧
        F.S = walFileS f fd (child dir g.name) (walSegFd true lo lk g.ino) g)
    {ic : Nat} (hlastN : (walNames hj.cur).getLast? = some gl.name) (hiL : hj.cur !! gl.name = some (.file gl.ino))
    (hXt : ∀ t ∈ walTmps, t ∈ X) (hsz : ∀ g ∈ gs0, g.om.size = g.bs.length)
    (hTM : TailMetaS m bs) (hwr : o0 = (tailStream Mr H md cuts).length) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) walCodec Mr R jr r -∗ walOpening (W := W) w dir sn ic -∗ Q dc -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg -∗ zapLoggerOk lg -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks -∗
      locks ↦* (ls ++ [lt]) -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp -∗ walPipeH fp dir j 0 -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false -∗
      sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
        (BI.pure True : IProp GF) -∗ encEnv -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df -∗
      os.ownFile df dfd dir (DFrac.own 1) -∗ osDirFdS dfd j ph -∗ osCallPerm (callKey R dir) (1 : Qp).half.half -∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      walOutFrag (W := W) ⟨(gs0 ++ [gl]).map (·.ino), [(j, .except X)], [dir]⟩ -∗
      walNamesFrag (W := W) none -∗ walDirKey (W := W) dir j X -∗
      ([∗list] k ↦ lf ∈ ls ++ [lt], fileutil.lockedFile lf (fls.getD k null)) -∗
      ([∗list] F ∈ fsI, ∃ q, F.S q) -∗
      walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) Lk -∗
      os.ownFile (fls.getD gs0.length null) fdl (child dir gl.name) (DFrac.own 1) -∗
      (∃ (rd : Bool) (lo lk : Option Bool), osFd fdl (DFrac.own 1) ⟨gl.ino, rd, true, lo, lk⟩ ∗
        fdLocksW fdl ⟨gl.ino, rd, true, lo, lk⟩) -∗
      walTailKey (W := W) dir γt -∗
      osMeta gl.ino (DFrac.own (1 : Qp).half) m -∗ osBytes gl.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (letI := walAllG (W := W); ghostVar γt (1 : Qp).half ((H, md, cuts, o0 + ([] : List w8).length, gl.ino, none) : TailG)) -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ enc -∗
      (⌜enc = null⌝ ∨ ∃ c : w32, ownEncoder enc (wal.fileWi (fls.getD gs0.length null)) c []) -∗
      (∀ d, Q d -∗ walReadFailedF Mr w dir -∗ WP e {{ Φ }}) -∗ WP e {{ Φ }} := by
  iintro #Hinv Hgh HQ Hlg #Hz Hdir Hlocks Hls Hfp Hpipe Hns #Hmu #Henv Hdff Hdf Hdfs Hph Hn Hout Hnf #Hk
    #Hlks Hst Htf Hft ⟨%rd, %lo, %lk, Hfdt, Hlkt⟩ Hkey Hm Hb Hv He Henc Hcont
  ihave Hlkt := fdLocksW_locks _ _ $$ Hlkt
  iapply wp_notCrashed_acc _ _ h
  iintro Hnc
  imod walInv_untailKey (L := hG.goose_localGS) Mr R jr r dir γt H md cuts (o0 + ([] : List w8).length) gl.ino
      m bs hTM (by simpa using hwr) $$ Hinv Hnc Htf Hkey [Hv] Hm Hb with ⟨Hnc, Htf, Hm, Hb⟩
  · unfold tailVar; iexact Hv
  iframe Hnc
  imodintro
  iapply readAll_failWpQ walCodec Mr R jr r w dir sn Q dc e Φ h $$ Hinv Hgh HQ
  iintro %dq HQ Hfail
  iapply Hcont $$ HQ
  icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
  ihave Hph := walPerm_toW hWR dir _ $$ Hph
  iapply walReadFailedF_idleIntro Mr w dir lg locks ls lt fp j X hj gs0 gl fls df dfd ph fsI ⟨gl.name, gl.ino, m, bs⟩
    fdl ⟨gl.ino, rd, true, lo, lk⟩ enc hfI hlI hfll hfk hlastN hiL hXt hsz ⟨rfl, hTM.1.1.symm⟩ rfl
  iframe
  iframe #
  unfold segRes; iframe

end exits

end WalFs
end EtcdGrove
end Perennial

end
