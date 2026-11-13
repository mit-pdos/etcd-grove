/- Lean-first (no Rocq counterpart).

# The open WAL's handle over `fsExt` (W6 of `notes/wal-fsext-plan.md`; "W6 implementation log")

What a `*wal.WAL` in append mode owns, and the vocabulary of `Save`, `SaveSnapshot`, `Sync` and
their helpers (`saveEntry`, `saveState`, `saveCrc`, `sync`, `cut`).

* **The tail's stream** (`tailStream Mr H md cuts`): the intended bytes of the last segment, the
  frames of its records (`Abs.lean`'s `segStream` at the last segment, over the concrete codec
  `walCodec`); `tailCrc`: the encoder's CRC after every record of the WAL (the chain's end).
* **The tail's writer** (plan W6 log, "the crash-aware tail write"): the tail is crash-tracked (half
  of its `OsMeta` and bytes in `walInv`), so it is written as a *guarded* stream
  (`io.writerStreamP`, `Proof/io/WriterStream.lean`) accepting only the bytes it is meant to hold:
  `tailOk Mr H md cuts o0 sz ys` (`ys` a prefix of the intended stream past `o0`, inside the
  preallocated size `sz`). Its state `walTailW` (the file, its offset `o0 + |out|`, the program's
  halves of the tail's `OsMeta` and bytes, the handle's key to the invariant's tail record
  `walTailKey dir γ` and its half of the tail record `(H, md, cuts, o0 + |out|, ino, none)`,
  `walTailsRes`, `Inv.lean`): the record ties the program's `H` to the invariant's, so that a
  write step, opening `walInv`, knows the bytes are the stream's. `wal.tailWriter` is the
  contract (each `pwrite` step opens `walInv` with `notCrashed`, `wp_atomic_nc`); the encoder's
  and page writer's specs over it are `encoder.encode.specP` (`encoder__encodeG.lean`).
* **The handle** (`walHandleIn Mr w dir h`, `h : WalHS`): the struct's fields, the encoder over
  the tail with its CRC at `tailCrc` and its pending bytes, the stream split
  `take o0 ++ out ++ pend = tailStream`, the tail's lock and file, the last hard state at
  `w.state`, the indices `enti`/`snapi`, the pipeline (`walPipeH`, `Pipe.lean`), and the ghost handle
  (`walOpenW`). `walOpenWF Mr w dir` seals it: the client-facing handle of the specs.
* **The raft messages** `Save` reads (`WalPbIn`): the part cannot import the main tree's `hsRO`/
  `entRoC` (the raft-root clash, plan §10), so the specs are over predicates a client
  instantiates, with the laws (`MustMarshalMessage`, `GetIndex`, `IsEmptyHardState`, `MustSync`)
  taken as hypotheses by the proofs.
* **The invariant's tail conjunct** (`walTailsRes`, `Inv.lean`): per WAL with an open handle, the
  other half of the tail record, the layout's (`tailG`), and F-Z.
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
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs
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
`w.state` (`st`), the ghost name of the tail's record (`γ`, `walTailsRes`), the tail's size `sz`
(preallocated), and the indices `enti`/`snapi`. -/
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
  γ : GName
  sz : Nat
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

/-! ## The tail's guard -/

/-- **What the tail's writer accepts** (`io.writerStreamP`'s guard): the bytes after the encoder's
start `o0` are a prefix of the tail's intended stream past `o0`, inside the preallocated size `sz`. -/
def tailOk [GooseExts] (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (o0 sz : Nat) (ys : List w8) : Prop :=
  ys <+: (tailStream Mr H md cuts).drop o0 ∧ o0 + ys.length ≤ sz

/-- **What the program knows of the tail's `OsMeta` `m` and bytes `bs`** (`walTailW`): all its bytes,
no mappings, its known zeros past its size (`MetaOk.zf`: a fact of the state, which the WAL
invariant does not keep and a step's crash condition needs, `crashOkA_tail`'s `hzf`). -/
def TailMeta (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ ∀ z, m.zf = some z → m.size ≤ z

theorem tailOk_prefix [GooseExts] {Mr : WalMarshal} {H : List (WalOpG WalEnt)} {md : List w8}
    {cuts : List Nat} {o0 sz : Nat} {xs ys : List w8} (h : xs <+: ys)
    (hy : tailOk Mr H md cuts o0 sz ys) : tailOk Mr H md cuts o0 sz xs :=
  ⟨h.trans hy.1, Nat.le_trans (Nat.add_le_add_left h.length_le _) hy.2⟩

/-! ## The tail and the handle -/

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The tail's writer state after accepting `out`** (`W` of the tail's `io.writerStreamP`, see
the file header): the file `f` (fd `fd` of inode `i`, with write access: `Create` opens it
write-only, `ReadAll` read-write), its offset at `o0 + |out|`, the program's halves of the tail's `OsMeta` (of size `sz`) and bytes, the handle's key to its tail
record `γ` in `dir`, and its half of the record: history `H`, metadata `md`, cuts, write position
`o0 + |out|`, inode `i`, no write in flight; and what the program knows of the tail's `OsMeta`
(`TailMeta`: all its bytes, no mappings, its zeros past the size). -/
def walTailW (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8) :
    IProp GF :=
  letI := walAllG (W := W)
  iprop(os.ownFile f fd name (DFrac.own 1) ∗ (∃ rd : Bool, osFd fd (DFrac.own 1) ⟨i, rd, true⟩) ∗
    os.ownOff f (W64 (o0 + out.length)) ∗ walTailKey (W := W) dir γ ∗
    ∃ (m : OsMeta) (bs : List ByteG),
    osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
    ⌜m.size = sz ∧ TailMeta m bs⌝ ∗
    ghostVar γ (1 : Qp).half ((H, md, cuts, o0 + out.length, i, none) : TailG))

/-- **The pipeline `w.fp` of the WAL in `dir`** (`Pipe.lean`), the handle having made `k` cuts:
the pipeline (over the directory's inode `j`, the handle's `walDirH`'s; roots `R`, path fraction `dq`,
file size `sz`), the
caller's token after `n ≤ k` files received, and the claim on the name the next `Open` hands back
(`pipeTmp (n + 1)`: the name of the file received last, renamed away by its cut). -/
def walPipeH (fp : Loc) (dir : GoString) (j : Ino) (k : Nat) : IProp GF :=
  iprop(∃ (γ : PipeNames) (R : Roots) (dq : DFrac) (sz : w64) (n : Nat),
    isFilePipe fp γ R dir dq j sz ∗ pipeMain γ n ∗ tmpClaim j (pipeTmp (n + 1)) ∗ ⌜n ≤ k⌝)

/-- A non-tail lock: a `*fileutil.LockedFile` (`fileutil.lockedFile`, what `fileutil.LockFile`
returns) and its open file, whole. -/
def walLockH (lf : Loc) : IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (nm : GoString) (d : OsFd),
    fileutil.lockedFile lf f ∗ os.ownFile f fd nm (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d)

/-- **The handle's share of its WAL directory `j`** (W2's `cut`, its rename; the directory-claim map,
`notes/wal-fsext-plan.md`, W1 log, seventh session): the directory's key `walDirKey dir j X` (the
invariant holds the claim `(j, .except X, hj)` once, `DirKeysOk`), the program's half of that claim
(the claim changes only with both halves, so `hj` is the directory as it is), a fraction of the
directory's path and the shared invariant of its roots, half of the call permission (the file
pipeline holds the other, plan §11), the directory's open fd `dfd` (`w.dirFile`, which `cut`
fsyncs: `os.File.Sync.specDirS`), and the tail's name: the `.wal` name `nm0` holding the tail's
inode `ino`, the tail file's name `child dir nm0` (`w.seq()` parses it: `walFileName sq ix`, its
sequence below `2^64 - 1`, which `cut` increments), the largest `.wal` name of the directory (the
invariant's: the last segment's, `WalAbsD.names`; stable while the handle holds half the claim). The
claim leaves out the pipeline's names (`walTmps ⊆ X`: the pipeline holds their claims). -/
def walDirH (dir : GoString) (j : Ino) (dfd : w64) (ino : Ino) (name : GoString) : IProp GF :=
  iprop(∃ (R : Roots) (q : Qp) (X : List GoString) (hj : NamesH) (nm0 : GoString) (ph : DirPhS),
    walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    osPathS R dir (DFrac.own q) j ∗ osSharedInv R ∗ osCallPerm (1 : Qp).half ∗ osDirFdS dfd j ph ∗
    ⌜walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file ino) ∧ name = child dir nm0 ∧
      (∀ t ∈ walTmps, t ∈ X) ∧
      (∃ sq ix : Nat, nm0 = walFileName sq ix ∧ sq + 1 < 2 ^ 64) ∧
      ∀ b n, hj.cur !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0⌝)

/-- **The open WAL `w` of `dir`, in the state `h`** (see the file header). The pure facts: the
stream split, the tail's offset inside its size (both below ext4's maximum offset, `Seek`'s), and
the indices `enti`/`snapi` bounding every index of the history (`cut` names the next segment
`max(enti, snapi) + 1`, above `walLastIdx`, without wrapping). -/
def walHandleIn (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS) :
    IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ (lg df sp e fp lt f : Loc) (mds locks : GoSlice) (lfs : List Loc) (fd dfd : w64)
      (name dnm : GoString) (j : Ino) (rc : GoFunc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dnm (DFrac.own 1) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"metadata" w ↦ mds ∗
    mds ↦*□ h.md ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp ∗
    P.hsIn sp h.st ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"decoder" w ↦ null ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"readClose" w ↦ rc ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ h.enti ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ h.snapi ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗
    ownEncoder e (wal.fileWi f) (h.crc Mr) h.pend ∗
    walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out ∗
    walDirH (W := W) dir j dfd h.ino name ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* lfs ∗ ownSliceCap Loc locks (DFrac.own 1) ∗ ⌜lfs.getLast? = some lt⌝ ∗
    ([∗list] lf ∈ lfs.dropLast, walLockH lf) ∗
    fileutil.lockedFile lt f ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗ walPipeH fp dir j h.cuts.length ∗
    encEnv ∗ walCrcTable ∗
    walOpenW (W := W) w dir ∗
    ⌜WalHS.Split Mr h ∧ 0 ≤ fd.toInt ∧ h.o0 + h.out.length ≤ h.sz ∧ h.sz ≤ 0xffffffff000 ∧
      h.o0 + h.out.length + h.pend.length ≤ 0xffffffff000 ∧
      walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi) ∧
      max (uint.nat h.enti) (uint.nat h.snapi) + 1 < 2 ^ 64⌝)

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
