/- Lean-first (no Rocq counterpart).

# The open WAL's handle over `fsExt` (W6 of `notes/wal-fsext-plan.md`; "W6 implementation log")

What a `*wal.WAL` in append mode owns, and the vocabulary of `Save`, `SaveSnapshot`, `Sync` and
their helpers (`saveEntry`, `saveState`, `saveCrc`, `sync`, `cut`).

* **The tail's stream** (`tailStream Mr H md cuts`): the intended bytes of the last segment, the
  frames of its records (`Abs.lean`'s `segStream` at the last segment, over the concrete codec
  `walCodec`); `tailCrc`: the encoder's CRC after every record of the WAL (the chain's end).
* **A writer with an acceptance guard** (`io.writerStreamG wi W G`): `io.writerStream` whose
  `Write(p)` also needs `G (out ++ p)`, a persistent fact about the stream so far. The WAL's tail
  is a crash-tracked file (half of its bytes in `walInv`): a write of bytes that are not the
  intended stream would break the crash condition, so no `W` makes the plain contract true of the
  tail. `G` is a lower bound of the tail's intended stream (`walTailG`, a mono list), which grows
  only when `Save`'s update commits. The encoder's and page writer's specs over it thread `G`
  (`encoder.encode.specG`, a hypothesis until their proofs are re-run over `writerStreamG`).
* **The tail's writer state** (`walTailW f i γW o0 out`): the file's offset at `o0 + |out|`, the
  program's halves of the tail's `OsMeta` and bytes, and the program's half of the tail's write
  position `γW` (the invariant's `lay.wr`, `walTailsRes`).
* **The handle** (`walHandleIn Mr w dir h`, `h : WalHS`): the struct's fields, the encoder over
  the tail with its CRC at `tailCrc` and its pending bytes, the stream split
  `take o0 ++ out ++ pend = tailStream`, the tail's lock and file, the last hard state at
  `w.state`, the indices `enti`/`snapi`, the pipeline (`walPipeH`, `Pipe.lean`), and the ghost handle
  (`walOpenW`). `walOpenWF Mr w dir` seals it: the client-facing handle of the specs.
* **The raft messages** `Save` reads (`WalPbIn`): the part cannot import the main tree's `hsRO`/
  `entRoC` (the raft-root clash, plan §10), so the specs are over predicates a client
  instantiates, with the laws (`MustMarshalMessage`, `GetIndex`, `IsEmptyHardState`, `MustSync`)
  taken as hypotheses by the proofs.
* **The invariant's tail conjunct** (`walTailsRes`, to be appended to `walInvBody`, plan §11): per
  WAL with an open handle, the authority of its tail's stream (`γS`) and the invariant's half of
  its write position (`γW`), agreeing with the layout (`lay.wr`, the last segment's stream).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Pipe
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.EncDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Codec
public import LinuxFs.Proof.os.Off
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

/-! ## The tail's stream (pure) -/

section pure
variable [GooseExts]

/-- **The intended bytes of the last segment** of the history `H` (metadata `md`, cut positions
`cuts`): `segStream walCodec Mr d cuts cuts.length` of a WAL with that history. -/
def tailStream (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) :
    List w8 :=
  recFrames walCodec ((chainSegs walCodec 0#32
    (segsDs Mr md true [] (segsOf (H.map WalOpG.toM) cuts))).getD cuts.length [])

/-- The records of the last segment (CRCs chained). -/
def tailRecs (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) :
    List WalRec :=
  (chainSegs walCodec 0#32 (segsDs Mr md true [] (segsOf (H.map WalOpG.toM) cuts))).getD cuts.length []

/-- Every record of the WAL (CRCs chained). -/
def allRecs (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) :
    List WalRec :=
  recsOfSegs walCodec Mr md (segsOf (H.map WalOpG.toM) cuts)

/-- **The encoder's CRC after every record of the WAL.** -/
def tailCrc (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) : w32 :=
  chainEnd walCodec 0#32 (recsOfSegs walCodec Mr md (segsOf (H.map WalOpG.toM) cuts))

theorem tailStream_recs (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) : tailStream Mr H md cuts = recFrames walCodec (tailRecs Mr H md cuts) := rfl

theorem tailStream_eq (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) :
    tailStream Mr d.H d.metadata cuts = segStream walCodec Mr d cuts cuts.length := rfl

/-- **The program's knowledge of its open WAL** (`walHandleIn`): the history (the last operation's
last `rest` records not yet encoded: `Save` commits its operation before encoding it), the
metadata, the cuts, the tail's inode, the encoder's start offset `o0` in the tail, the bytes its
writer has accepted (`out`) and its page writer's pending bytes (`pend`), the hard state at
`w.state` (`st`), the ghost names of the history (`γH`, agreeing with the invariant), of the
tail's stream (`γS`) and write position (`γW`), and the indices `enti`/`snapi`. -/
structure WalHS where
  H : List (WalOpG WalEnt)
  md : List w8
  cuts : List Nat
  ino : Ino
  o0 : Nat
  out : List w8
  pend : List w8
  rest : Nat
  st : HardStateM
  γH : GName
  γS : GName
  γW : GName
  enti : w64
  snapi : w64

/-- The tail's records encoded so far (all but the last `rest`). -/
def WalHS.encRecs (Mr : WalMarshal) (h : WalHS) : List WalRec :=
  (tailRecs Mr h.H h.md h.cuts).take ((tailRecs Mr h.H h.md h.cuts).length - h.rest)

/-- The encoder's CRC: the chain's after every record encoded so far. -/
def WalHS.crc (Mr : WalMarshal) (h : WalHS) : w32 :=
  chainEnd walCodec 0#32 ((allRecs Mr h.H h.md h.cuts).take ((allRecs Mr h.H h.md h.cuts).length - h.rest))

/-- The bytes of the tail the encoder has accepted: the frames of the records encoded so far,
split (`take o0 ++ out ++ pend`), the first `o0` the file's before the encoder was made. -/
def WalHS.Split (Mr : WalMarshal) (h : WalHS) : Prop :=
  (recFrames walCodec (h.encRecs Mr)).take h.o0 ++ h.out ++ h.pend = recFrames walCodec (h.encRecs Mr) ∧
    h.o0 ≤ (recFrames walCodec (h.encRecs Mr)).length ∧
    h.rest ≤ (tailRecs Mr h.H h.md h.cuts).length

/-- **A quiescent handle**: every record encoded, `w.state` the last saved hard state. -/
def WalHS.Done (h : WalHS) : Prop := h.rest = 0 ∧ h.st = walLastHS (h.H.map WalOpG.toM)

end pure

/-! ## The raft messages `Save` reads -/

section pb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- See the file header. `hsIn p hs`: the `*raftpb.HardState` `p` (`nil` read as the zero state)
holds `hs`, frozen; `entIn l e`: the `*raftpb.Entry` `l` holds `e`, frozen; `snapIn sp md`: the
`*walpb.Snapshot` `sp` of metadata `md`, frozen (`walSnapAt`'s object). Persistent. -/
structure WalPbIn (GF : BundledGFunctors) where
  hsIn : Loc → HardStateM → IProp GF
  entIn : Loc → EntryM → IProp GF
  hsIn_persistent : ∀ p hs, Persistent (hsIn p hs)
  entIn_persistent : ∀ l e, Persistent (entIn l e)

attribute [instance] WalPbIn.hsIn_persistent WalPbIn.entIn_persistent

/-- The entries `esL` hold `es`. -/
def walEntsIn (P : WalPbIn GF) (esL : List Loc) (es : List EntryM) : IProp GF :=
  iprop([∗list] l; e ∈ esL; es, P.entIn l e)

end pb

/-! ## The writer with an acceptance guard -/

section writer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header: `io.writerStream` whose `Write(p)` needs `G (out ++ p)`; `G` persistent
and prefix-closed (the client's: what may be written). -/
def io.writerStreamG (wi : GoInterfaceOk) (W : List w8 → IProp GF) (G : List w8 → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (out : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
    {{ W out ∗ G (out ++ xs) ∗ p ↦*{dq} xs }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜ys <+: xs ∧ sint.Z n = ys.length ∧ (err = GoInterface.nil → ys = xs)⌝ ∗
        W (out ++ ys) ∗ p ↦*{dq} xs }})

instance io.writerStreamG_persistent (wi : GoInterfaceOk) (W G : List w8 → IProp GF) :
    Persistent (io.writerStreamG wi W G) := by
  unfold io.writerStreamG; infer_instance

end writer

/-! ## The tail and the handle -/

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The tail's stream is at least `ys`** (persistent): a lower bound of the tail's intended
stream, the acceptance guard of its writer. -/
def walTailG (γS : GName) (ys : List w8) : IProp GF :=
  letI := walAllG (W := W)
  monoListLbOwn γS ys

instance walTailG_persistent (γS : GName) (ys : List w8) :
    Persistent (walTailG (W := W) γS ys) := by
  unfold walTailG; infer_instance

/-- **The tail's writer state** (`W` of the tail's `io.writerStreamG`): the file `f`'s offset at
`o0 + |out|`, the program's halves of the tail's `OsMeta` and bytes, and its half of the tail's
write position. -/
def walTailW (f : Loc) (i : Ino) (γW : GName) (o0 : Nat) (out : List w8) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ (m : OsMeta) (bs : List ByteG),
    os.ownOff f (W64 (o0 + out.length)) ∗ osMeta i (DFrac.own (1 : Qp).half) m ∗
    osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗ ghostVar γW (1 : Qp).half (o0 + out.length))

/-- **The pipeline `w.fp` of the WAL in `dir`** (`Pipe.lean`), the handle having made `k` cuts:
the pipeline (some directory inode `j`, roots `R`, path fraction `dq`, file size `sz`), the
caller's token after `n ≤ k` files received, and the claim on the name the next `Open` hands back
(`pipeTmp (n + 1)`: the name of the file received last, renamed away by its cut). -/
def walPipeH (fp : Loc) (dir : GoString) (k : Nat) : IProp GF :=
  iprop(∃ (γ : PipeNames) (R : Roots) (dq : DFrac) (j : Ino) (sz : w64) (n : Nat),
    isFilePipe fp γ R dir dq j sz ∗ pipeMain γ n ∗ tmpClaim j (pipeTmp (n + 1)) ∗ ⌜n ≤ k⌝)

/-- A non-tail lock: a `*fileutil.LockedFile` and its open file. -/
def walLockH (lf : Loc) : IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (nm : GoString) (d : OsFd),
    structFieldRef go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile go!"File" lf ↦ f ∗
    os.ownFile f fd nm (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d)

/-- **The open WAL `w` of `dir`, in the state `h`** (see the file header). -/
def walHandleIn (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS) :
    IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ (lg df sp e fp lt f : Loc) (mds locks : GoSlice) (lfs : List Loc) (fd dfd : w64)
      (name dnm : GoString) (dd : OsFd) (rc : GoFunc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dnm (DFrac.own 1) ∗ osFd dfd (DFrac.own 1) dd ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"metadata" w ↦ mds ∗
    mds ↦*□ h.md ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp ∗
    P.hsIn sp h.st ∗ ⌜sp ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"decoder" w ↦ null ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"readClose" w ↦ rc ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ h.enti ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ h.snapi ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
    ownEncoder e (wal.fileWi f) (h.crc Mr) h.pend ∗
    walTailW f h.ino h.γW h.o0 h.out ∗
    io.writerStreamG (wal.fileWi f) (walTailW f h.ino h.γW h.o0) (walTailG (W := W) h.γS) ∗
    walTailG (W := W) h.γS ((recFrames walCodec (h.encRecs Mr)).take h.o0 ++ h.out) ∗
    ghostVar h.γH (1 : Qp).half (h.H, h.md, h.cuts) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* lfs ∗ ownSliceCap Loc locks (DFrac.own 1) ∗ ⌜lfs.getLast? = some lt⌝ ∗
    ([∗list] lf ∈ lfs.dropLast, walLockH lf) ∗
    structFieldRef go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile go!"File" lt ↦ f ∗
    os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨h.ino, false, true⟩ ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗ walPipeH fp dir h.cuts.length ∗
    encEnv ∗ walCrcTable ∗
    walOpenW (W := W) w dir ∗
    ⌜WalHS.Split Mr h ∧ 0 ≤ fd.toInt⌝)

/-- **`w` is the WAL opened in `dir`, ready to append, its history `H`** (the specs' handle;
sealed): quiescent (`WalHS.Done`). The history is the program's copy's (`walDiskAt dir d` has `d.H = H`, the update of
`Save` moves both). -/
@[no_expose] def walOpenWF (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    IProp GF :=
  iprop(∃ h : WalHS, walHandleIn (W := W) P Mr w dir h ∗ ⌜h.Done⌝)

end handle

end WalFs
end EtcdGrove
end Perennial

end
