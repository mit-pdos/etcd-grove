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
public import LinuxFs.Proof.os.TcKnows
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Pipe
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.EncDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Codec
public import LinuxFs.Proof.os.Off
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.go_uber_org.zap.Defs
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs
public import Perennial.Ghost.GhostVar
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit

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
(preallocated), the indices `enti`/`snapi`, and the files the handle's pipeline has handed over
(`pc`: its `count`, which restarts at 0 with each `Open`/`Create`, unlike `cuts`, which counts the
cuts of the WAL read back too; `cut` names its file `count % 2`, a signed remainder, so needs
`pc + 2 < 2^63`). -/
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
  pc : Nat

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

/-- **The highest snapshot record's index of `P`** (0 if none): `walLastIdx`'s second fold
(`walLastIdx_snap`). `w.snapi` bounds it in every state of the handle (`SaveSnapshot` raises
`w.snapi` to the maximum, S/wal.go:1161; `ReadAll` to every snapshot record it reads, :576, which
are all those above the first segment it reads, the names being increasing). -/
def walMaxSnapIdx (P : WalHist) : Nat :=
  P.foldl (fun x o => match o with
    | .save _ _ => x
    | .snap m => max x (uint.nat m.Index')) 0

theorem walLastIdx_snap (P : WalHist) :
    walLastIdx P = max (P.foldl (fun x o => match o with
      | .save _ es => (es.getLast?.map (fun e => uint.nat e.Index')).getD x
      | .snap _ => x) 0) (walMaxSnapIdx P) := rfl

/-- **The bytes a batch of entries takes in the WAL**, over-approximated: each entry's encoding plus 64
bytes (its record's type, CRC and length fields, the frame's length word and padding; `frame_walRecEnc_tight`,
`StreamBound.lean`), summed (`Save`'s premise; ledger 2026-11-14, "the batch's size"). -/
def walBatchBytes (Mr : WalMarshal) (es : List EntryM) : Nat :=
  (es.map (fun e => (Mr.encEntry e).length + 64)).sum

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

/-- **The candidates of every byte past the tail's size known, across a sync** (W6 log, sixteenth
session, finding 1): zeros known from `z` on (at least the size, `MetaOk.zf`), the candidates of the
bytes between the size and `z` known (`tc`: a truncate's cut-off bytes, a write's announced bytes past
the size, `pwPostK true`), and the page cache known zero to the end of the page holding `z` (or `z`
page-aligned at the size), so that a sync (`OsMeta.synced`: `tc` forgotten, zeros from `syncZ` on)
leaves the zeros known from the size on (`OsMeta.synced_zf_size`). A write past the size reads these
candidates (`wp_osPWriteFinishK`'s `zs`); a write landing up to `z` raises `cz` to its end's page
(`Fs.pwCz`). -/
def TailZ (m : Fs.OsMeta) : Prop :=
  ∃ z, m.zf = some z ∧ m.size ≤ z ∧ Fs.pageEnd z ≤ max m.size m.cz ∧
    ∀ b, m.size ≤ b → b < z → ∃ c, m.tc !! b = some c

theorem TailZ.ge {m : Fs.OsMeta} (h : TailZ m) : ∀ z, m.zf = some z → m.size ≤ z := by
  obtain ⟨z0, h0, h1, -⟩ := h
  intro z hz; rw [h0, Option.some.injEq] at hz; subst hz; exact h1

/-- What a sync needs of `TailZ` (`OsMeta.syncZ` is the size). -/
theorem TailZ.pageEnd_size {m : Fs.OsMeta} (h : TailZ m) : Fs.pageEnd m.size ≤ max m.size m.cz := by
  obtain ⟨z, -, h1, h2, -⟩ := h
  exact Nat.le_trans (Fs.pageEnd_mono h1) h2

/-- **A sync keeps `TailZ`**, given the page cache known zero to the end of the size's page. -/
theorem TailZ.synced_of {m : Fs.OsMeta} (hB : Fs.pageEnd m.size ≤ max m.size m.cz) :
    TailZ m.synced := by
  have hz : m.syncZ = m.size := by
    unfold Fs.OsMeta.syncZ; have := Fs.le_pageEnd m.size; split <;> omega
  refine ⟨m.size, by simp [Fs.OsMeta.synced, hz], by simp [Fs.OsMeta.synced], ?_, ?_⟩
  · simp only [Fs.OsMeta.synced]; exact hB
  · intro b h1 h2; simp only [Fs.OsMeta.synced] at h1; omega

theorem TailZ.synced {m : Fs.OsMeta} (h : TailZ m) : TailZ m.synced := TailZ.synced_of h.pageEnd_size

/-- **A write inside the size keeps `TailZ`** (the zeros known and the candidates past the size
untouched, `cz` raised at most). -/
theorem TailZ.pwPost_in {m : Fs.OsMeta} {off n k : Nat} (h : TailZ m) (hin : off + n ≤ m.size)
    (hk : k ≤ n) : TailZ (Fs.pwPost m off n k) := by
  obtain ⟨z, hz, h1, h2, h3⟩ := h
  have hmin : min off m.size = off := by omega
  have hsz : (Fs.pwPost m off n k).size = m.size := by
    simp only [Fs.pwPost, Fs.pwSize]; split <;> omega
  have hzf : (Fs.pwPost m off n k).zf = some z := by
    simp only [Fs.pwPost, Fs.announce_zf, hz, hmin, Option.map_some, Option.some.injEq]
    split <;> omega
  refine ⟨z, hzf, by rw [hsz]; exact h1, ?_, ?_⟩
  · rw [hsz]; have := Fs.le_pwCz m off n k; show Fs.pageEnd z ≤ max m.size (Fs.pwCz m off n k); omega
  · intro b hb1 hb2
    rw [hsz] at hb1
    obtain ⟨c, hc⟩ := h3 b hb1 hb2
    refine ⟨c, ?_⟩
    show (m.announce (min off m.size) (off + n) (max m.size (off + n))).tc !! b = some c
    rw [Fs.announce_tc, if_neg (by simp [Fs.inRange]; omega)]; exact hc

/-- **Nothing but zeros known past `hi`** (I3b; W6 log, twenty-first session, finding C, amended in the
twenty-second): each candidate `m` knows of a byte at or past the largest size a crash may leave is a zero,
stamped 0 or by a known resize (a truncate announces its zeros up to the end of the page past the old size,
which may pass `hi`). True of a handle's tail (`OsMeta.synced`: nothing known but the zeros past `zf`; a
write or a truncate raises `hi` past every candidate it adds but the truncate's zeros), not of a crash's
tail (`ZeroToEnd`'s window: the disk's bytes past its size). With `|old| ≤ hi`, a zero stamped 0 past `hi`
is `old`'s byte (`WinShape`): what the writer past the size needs of the bytes it grows over. -/
def PastZ (m : Fs.OsMeta) : Prop :=
  ∀ b c, m.hi ≤ b → m.pc b = some c → ∀ q ∈ c, q.1 = 0 ∧ (q.2 = 0 ∨ q.2 ∈ m.rz)

/-- `PastZ` of `M` from `m`'s: `M`'s candidates past its `hi` are `m`'s or the zero. -/
theorem PastZ.of_pc {m M : Fs.OsMeta} (h : PastZ m) (hhi : m.hi ≤ M.hi) (hrz : ∀ x ∈ m.rz, x ∈ M.rz)
    (hpc : ∀ b c, M.hi ≤ b → M.pc b = some c → m.pc b = some c ∨ c = [(0, 0)]) : PastZ M := by
  intro b c hb hc q hq
  rcases hpc b c hb hc with h1 | rfl
  · obtain ⟨h1, h2⟩ := h b c (by omega) h1 q hq
    exact ⟨h1, h2.imp_right (hrz _)⟩
  · simp only [List.mem_singleton] at hq; subst hq; exact ⟨rfl, .inl rfl⟩

/-- The candidate list of the zeros known past `zf`. -/
theorem pc_zf_cases {M : Fs.OsMeta} {b : Nat} {c : Fs.Cands} (ht : M.tc !! b = none)
    (hc : M.pc b = some c) : c = [(0, 0)] := by
  unfold Fs.OsMeta.pc at hc
  rw [ht] at hc
  cases hz : M.zf with
  | none => rw [hz] at hc; cases hc
  | some z =>
    rw [hz] at hc
    dsimp only at hc
    split at hc
    · exact (Option.some.inj hc).symm
    · cases hc

/-- **A change's first step keeps `PastZ`** (it forgets candidates and raises `hi`). -/
theorem PastZ.announce {m : Fs.OsMeta} (h : PastZ m) (lo hi tg : Nat) : PastZ (m.announce lo hi tg) := by
  refine h.of_pc (by simp only [Fs.announce_hi]; omega) (by simp) fun b c _ hc => ?_
  cases ht : (m.announce lo hi tg).tc !! b with
  | none => exact .inr (pc_zf_cases ht hc)
  | some c1 =>
    have ht' := ht
    rw [Fs.announce_tc] at ht'
    split at ht'
    · cases ht'
    · left
      unfold Fs.OsMeta.pc at hc ⊢
      rw [ht] at hc; rw [ht']; exact hc

/-- **A write keeps `PastZ`** (`pwPost`: the announcement, its size and `cz`). -/
theorem PastZ.pwPost {m : Fs.OsMeta} (h : PastZ m) (off n k : Nat) : PastZ (Fs.pwPost m off n k) :=
  h.announce (min off m.size) (off + n) (max m.size (off + n))

/-- **A sync gives `PastZ`** (nothing known but the zeros past `zf`). -/
theorem PastZ.synced (m : Fs.OsMeta) : PastZ m.synced := by
  intro b c _ hc q hq
  rw [pc_zf_cases (M := m.synced) (GMap.lookup_empty b) hc] at hq
  simp only [List.mem_singleton] at hq; subst hq; exact ⟨rfl, .inl rfl⟩

/-- **A resize's outcome keeps `PastZ`**, its candidates past the old size from `m`'s or zeros of a
known stamp (`TcFrom`, `os.ftDoneH`'s), from at most its `hi` on. -/
theorem PastZ.of_tcFrom {m M : Fs.OsMeta} {s : Nat} (h : PastZ m) (hf : Fs.TcFrom m s M.tc M.rz)
    (hs : s ≤ M.hi) (hhi : m.hi ≤ M.hi) : PastZ M := by
  intro b c hb hc q hq
  cases ht : M.tc !! b with
  | none =>
    rw [pc_zf_cases ht hc] at hq
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨rfl, .inl rfl⟩
  | some c1 =>
    have e : c = c1 := by
      unfold Fs.OsMeta.pc at hc; rw [ht] at hc; exact (Option.some.inj hc).symm
    subst e
    rcases hf.2 b c (by omega) ht q hq with ⟨c0, h0, hq0⟩ | hz
    · obtain ⟨h1, h2⟩ := h b c0 (by omega) h0 q hq0
      exact ⟨h1, h2.imp_right (hf.1 _)⟩
    · exact hz

/-- **A candidate known at or past `hi` has the window's shape** (W6 log, twenty-third session, task 1):
with `PastZ` and `old` no longer than `hi` (`WalAbsD.oldHi_any`), a zero stamped 0 there is `old`'s byte
(zero past `old`), a zero of a known resize `winShape_rz`'s. What the writer past the size needs of the
bytes it grows over (`pwTail`'s `m.pc b`). -/
theorem PastZ.winShape {m : Fs.OsMeta} (h : PastZ m) {S old : List w8} (hold : old.length ≤ m.hi)
    {b : Nat} {c : Fs.Cands} (hb : m.hi ≤ b) (hc : m.pc b = some c) :
    ∀ q ∈ c, WinShape S old m.rz b q := by
  intro q hq
  obtain ⟨h1, h2⟩ := h b c hb hc q hq
  rcases h2 with h2 | h2
  · left
    have e : old.getD b 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [e, ← h1, ← h2]
  · exact .inr (.inl ⟨h1, h2⟩)

/-- **What the program knows of the tail's `OsMeta` `m` and bytes `bs`** (`walTailW`): all its bytes,
no mappings, the candidates past its size (`TailZ`: zeros known past it, `MetaOk.zf`, a fact of the
state, which the WAL invariant does not keep and a step's crash condition needs, `crashOkA_tail`'s
`hzf`), no resize window open on it (`SegExact`: a crash leaves it with its size; the invariant's
static relation does not say so of the last segment, I3b), and nothing but zeros known past it (`PastZ`;
W6 log, twenty-second session). -/
def TailMeta (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ TailZ m ∧ m.lo = m.size ∧ m.hi = m.size ∧ PastZ m

/-- **`TailMeta` with a resize window open** (I3b, `wal-tc3`): from `cut`'s truncate of the tail at its
write position until `cut`'s fdatasync (`os.File.Truncate.specWalTail`'s post, `WAL.sync.specCut`'s
pre). The truncate lands its size (`rsPost true m tg tg`: `lo = size = tg`, `hi` the old size), the
flush's writes past it raise the size; a crash may leave any size in `[lo, hi]` (`SegExact` fails).
Otherwise as `TailMeta`. -/
def TailMetaW (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ TailZ m ∧ m.lo ≤ m.size ∧ m.size ≤ m.hi ∧ PastZ m

theorem TailMeta.win {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMeta m bs) : TailMetaW m bs :=
  ⟨h.1, h.2.1, h.2.2.1, Nat.le_of_eq h.2.2.2.1, Nat.le_of_eq h.2.2.2.2.1.symm, h.2.2.2.2.2⟩

theorem TailMeta.pastZ {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMeta m bs) : PastZ m :=
  h.2.2.2.2.2

theorem TailMetaW.pastZ {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMetaW m bs) : PastZ m :=
  h.2.2.2.2.2

/-- **No resize window open on the tail, or its least crash size at most the write position `wr`**
(`walTailW`'s; I3b, W6 log, twenty-second session, option (A) of the twenty-first): true of a handle at
rest (a window is opened by a truncate to `wr`, which sets `lo = wr`, or by a write past the size, whose
completion ends at `wr ≥ lo`; a failed one loses the handle), not of the invariant (a write past the
size from an exact tail keeps `lo` at the size until it completes). The truncate at `wr` needs it of a
window (`os.truncSup`'s `P`, `walTail_truncSup`). -/
def LoWr (m : Fs.OsMeta) (wr : Nat) : Prop := (m.lo = m.size ∧ m.hi = m.size) ∨ m.lo ≤ wr

theorem LoWr.of_exact {m : Fs.OsMeta} {wr : Nat} (h1 : m.lo = m.size) (h2 : m.hi = m.size) :
    LoWr m wr := .inl ⟨h1, h2⟩

theorem TailMeta.loWr {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMeta m bs) (wr : Nat) : LoWr m wr :=
  .inl ⟨h.2.2.2.1, h.2.2.2.2.1⟩

theorem LoWr.mono {m : Fs.OsMeta} {wr wr' : Nat} (h : LoWr m wr) (hw : wr ≤ wr') : LoWr m wr' := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (Nat.le_trans h hw)

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
(`TailMeta`: all its bytes, no mappings, its zeros past the size), the size below `2^62` (the
model's `Write` bound: whoever builds it, `Create` and `ReadAll`, knows the size, at most
ext4's `s_maxbytes`), the fd open, and no window open or its least crash size at most the write
position (`LoWr`). With `tm := TailMetaW`, the tail in a resize window (`cut`'s truncate until its
fdatasync). -/
def walTailW (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop := TailMeta) : IProp GF :=
  letI := walAllG (W := W)
  iprop(os.ownFile f fd name (DFrac.own 1) ∗ (∃ rd : Bool, osFd fd (DFrac.own 1) ⟨i, rd, true⟩) ∗
    os.ownOff f (W64 (o0 + out.length)) ∗ walTailKey (W := W) dir γ ∗
    ∃ (m : OsMeta) (bs : List ByteG),
    osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
    ⌜m.size = sz ∧ tm m bs ∧ sz < 2 ^ 62 ∧ 0 ≤ fd.toInt ∧ LoWr m (o0 + out.length)⌝ ∗
    ghostVar γ (1 : Qp).half ((H, md, cuts, o0 + out.length, i, none) : TailG))

/-- **The pipeline `w.fp` of the WAL in `dir`** (`Pipe.lean`), the handle having taken at most `k`
files from it (`WalHS.pc`):
the pipeline (over the directory's inode `j`, the handle's `walDirH`'s; roots `R`, path fraction `dq`,
file size `sz`), the
caller's token after `n ≤ k` files received, and the claim on the name the next `Open` hands back
(`pipeTmp (n + 1)`: the name of the file received last, renamed away by its cut); `fp` non-nil
(`Close` tests it, S/wal.go:1057). -/
def walPipeH (fp : Loc) (dir : GoString) (j : Ino) (k : Nat) : IProp GF :=
  iprop(∃ (γ : PipeNames) (R : Roots) (dq : DFrac) (sz : w64) (n : Nat),
    isFilePipe fp γ R dir dq j sz ∗ pipeMain γ n ∗ tmpClaim j (pipeTmp (n + 1)) ∗ ⌜n ≤ k⌝ ∗ ⌜fp ≠ null⌝)

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
sequence below `2^63 + k`, `k` the files the handle's pipeline has handed over (`WalHS.pc`): each `cut`
increments both, so with `cut.spec`'s `pc + 2 < 2^63` the incremented sequence does not wrap; a
producer at `k = 0` gives a sequence below `2^63`), the largest `.wal` name of the directory (the
invariant's: the last segment's, `WalAbsD.names`; stable while the handle holds half the claim). The
claim leaves out the pipeline's names (`walTmps ⊆ X`: the pipeline holds their claims) and no `.wal`
name (`DirKeysOk`'s: `cut`'s rename target is in the claim, `os.Rename.specFileSnc`'s `N'.Mem bt`);
the WAL is named (`walNamed`, persistent: `walCut_osAUnc`'s `walCutP` takes it); the record of what
the handle holds out of the parked state (`walOutFrag`: the tail, the directory's claim, the
pipeline's names; W1 log, tenth session); the lock holder's half of the tails' authority, with this
WAL's tail registered (`walTailsFrag`, W1 log, eleventh session), and no name registration pending
(`walNamesFrag none`): what `Close` needs to give the lock token back (`walLockedTok_unlock`; W10,
W7-W12 log, fourth session; `Create` and `ReadAll` establish them when they return the handle). -/
def walDirH (dir : GoString) (j : Ino) (dfd : w64) (ino : Ino) (name : GoString) (k : Nat) : IProp GF :=
  iprop(∃ (R : Roots) (q : Qp) (X : List GoString) (hj : NamesH) (nm0 : GoString) (ph : DirPhS),
    walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    osPathS R dir (DFrac.own q) j ∗ osSharedInv R ∗ osCallPerm (1 : Qp).half ∗ osDirFdS dfd j ph ∗
    walNamed (W := W) dir ∗ walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ ∗
    (∃ γt : GName, walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName))) ∗
    walNamesFrag (W := W) none ∗
    ⌜walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file ino) ∧ name = child dir nm0 ∧
      (∀ t ∈ walTmps, t ∈ X) ∧ (∀ b ∈ X, walNameP b = false) ∧
      (∃ sq ix : Nat, nm0 = walFileName sq ix ∧ sq < 2 ^ 63 + k) ∧
      ∀ b n, hj.cur !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0⌝)

/-- **The open WAL `w` of `dir`, in the state `h`** (see the file header). The metadata slice is
non-nil (`recBytes … (some md)`: `cut` encodes it as a record's data, present, `recOf`; `Create`
takes it non-nil). The pure facts: the
stream split, the tail's offset inside its size (both below ext4's maximum offset, `Seek`'s), and
the indices `enti`/`snapi` bounding every index of the history (`cut` names the next segment
`max(enti, snapi) + 1`, above `walLastIdx`, without wrapping): the bound on `walLastIdx` only of a
handle with every record encoded (`rest = 0`: `saveEntry` sets `w.enti` to each entry's index in
turn, S/wal.go:1086), the one on the snapshot records (`walMaxSnapIdx ≤ snapi`) always (`Save`
needs it when its entries go back below an earlier snapshot record). The encoder non-nil (`sync`
tests it, S/wal.go:968). With `tm := TailMetaW`, the tail in a resize window (`cut` between its
truncate and its fdatasync, `WAL.sync.specCut`). -/
def walHandleIn (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop := TailMeta) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ (lg df sp e fp lt f : Loc) (mds locks : GoSlice) (lfs : List Loc) (fd dfd : w64)
      (name dnm : GoString) (j : Ino) (rc : GoFunc),
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg ∗ zapLoggerOk lg ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dirFile" w ↦ df ∗
    os.ownFile df dfd dnm (DFrac.own 1) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"metadata" w ↦ mds ∗
    recBytes mds (some h.md) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp ∗
    P.hsIn sp h.st ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"decoder" w ↦ null ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"readClose" w ↦ rc ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"unsafeNoSync" w ↦ false ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
      (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"enti" w ↦ h.enti ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"snapi" w ↦ h.snapi ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"encoder" w ↦ e ∗ ⌜e ≠ null⌝ ∗
    ownEncoder e (wal.fileWi f) (h.crc Mr) h.pend ∗
    walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out tm ∗
    walDirH (W := W) dir j dfd h.ino name h.pc ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
    locks ↦* lfs ∗ ownSliceCap Loc locks (DFrac.own 1) ∗ ⌜lfs.getLast? = some lt⌝ ∗
    ([∗list] lf ∈ lfs.dropLast, walLockH lf) ∗
    fileutil.lockedFile lt f ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"fp" w ↦ fp ∗ walPipeH fp dir j h.pc ∗
    encEnv ∗ walCrcTable ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
    walOpenW (W := W) w dir ∗
    ⌜WalHS.Split Mr h ∧ 0 ≤ fd.toInt ∧ h.o0 + h.out.length ≤ h.sz ∧ h.sz ≤ 0xffffffff000 ∧
      ((h.rest = 0 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi)) ∧
        walMaxSnapIdx (h.H.map WalOpG.toM) ≤ uint.nat h.snapi) ∧
      max (uint.nat h.enti) (uint.nat h.snapi) + 1 < 2 ^ 64⌝)

/-- **`w` is the WAL opened in `dir`, ready to append, its history `H`** (the specs' handle;
sealed): quiescent (`WalHS.Done`). The history is the program's copy's (`walDiskAt dir d` has `d.H = H`, the update of
`Save` moves both). The metadata below `2 ^ 41` bytes (`cut`'s header records, `cut.spec`'s `2 ^ 42` with
`walAreaOk`'s bound on the hard state's encoding; ledger 2026-11-14): fixed at `Create`, whose premise it is
(the server's metadata is a small protobuf), and the same for every handle of the WAL (`ReadAll`'s).
The tail's resize window may be open (`TailMetaW`: a `Save` that wrote past the preallocated size and did not
sync, W6 log, thirteenth session). No bound on the stream's end (withdrawn 2026-11-14, `wal-maxb14`): the
tail's written bytes stay below ext4's `s_maxbytes` by the writes' success (`fsExt`'s `maxBytes`), which
is `walHandleIn`'s `o0 + |out| ≤ sz ≤ 0xffffffff000`, and the pending ones are at most the page writer's
buffer. -/
@[no_expose] def walOpenWF (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    IProp GF :=
  iprop(∃ h : WalHS, walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⌜h.Done⌝ ∗ ⌜h.md.length < 2 ^ 41⌝ ∗
    ⧗ h.pc)

/-- **The cuts budget** (`notes/bounds-plan.md`: the counter's owner turns the global receipt bound into
its bound): with the area's `ReceiptBoundLe GF (2 ^ 62)`, `⧗ (pc + 1)` (the handle's `⧗ pc` and the receipt
of a step of the `Save` about to cut) bounds the pipeline's count as `cut` needs (`cut.spec`'s
`pc + 2 < 2 ^ 63`). -/
theorem walPc_bound (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (n : Nat) :
    ⊢@{IProp GF} walAreaOk C Mr R jr r -∗ ⧗ (n + 1) -∗ ⌜n + 2 < 2 ^ 63⌝ := by
  iintro #Harea Hr
  unfold walAreaOk
  icases Harea with ⟨-, -, -, %hb, -⟩
  ihave %hl := receipt_lt (n + 1) $$ Hr
  ipureintro
  have := hb.receiptBound_le
  omega

end handle

end WalFs
end EtcdGrove
end Perennial

end
