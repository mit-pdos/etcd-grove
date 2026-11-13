/- Lean-first (no Rocq counterpart).

# W1: no CRC32-C collision on a torn WAL frame (`notes/wal-fsext-plan.md`, §2.5, §6 Q2)

**A new world premise, pending the user's review [user].** It is stated as minibolt's P1
(`LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/BootP1.lean`): a filter on the
extension's crashes (`fsExtsSemanticsWithS AnyStep (fun st st' => W1 C st st')`), stated of the
semantic state's crash candidates, never an axiom.

**What it says.** At a crash from `st` to `st'`, take any directory of the crashed tree, its
`.wal` files in name order (`sort.Strings` of `readWALNames`; here: every name ending in `.wal`, a
superset, which only makes the premise say more of frames the reader never sees), and a reader
started at any of them with a fresh decoder (CRC 0: `Open`/`ReadAll`, `ValidSnapshotEntries`,
`Repair` from the first file, or from a later one: `walDecodeFiles_suffix`). For every frame the
reader accepts (`acceptsFiles`: the length word and the record pass `decodeRecord`'s checks and the
reader's CRC-record check, `WalEncDecode.decStep`), the frame's *core* (its length word and its
record bytes, `frameCore`; not its 0-7 padding bytes) came back **as of one change** (`AsOfOne`):
as of the file's last sync (each byte its candidate stamped 0), or as of a change `n > 0` by which
every one of its bytes had been written (each `valAt (cand b) n`, the candidate of the largest stamp
up to `n`, and some candidate stamped in `(0, n]`). The semantics lets a crash mix the bytes of a
frame from any of their candidates; W1 says a mix that is no such state (a frame partly written
since the sync, or mixed from several changes) does not pass the reader.

**Evidence.** The WAL W3 decision (`notes/decisions.md`, "WAL W3", approved): "no CRC32-C collision
on torn data": a torn record passes only if CRC32-C of its torn data equals the torn CRC field; the
W4c CP1 runs (the tester's crash-point runs, `notes/wal-crash-handoff/`) never saw one. Like P1, it
is the WAL's own assumption (etcd relies on the CRC to reject torn tails: `decoder.go:133-150`).

**What the evidence does not cover (for the review).** The CRC covers the record's `Data` only
(`encoder.go:73-74`, `decoder.go:133-138`), not its `Type` and `Crc` fields nor the padding:
* a tear confined to the padding passes the reader with the intended record (the reader does not
  read the padding): such crashes are real and harmless, so W1 says nothing of the padding;
* a tear confined to the record's `Type` field (a frame spanning a sector boundary, the type's
  varint before it and the data after) passes the CRC with no collision, as a record of another
  type. W1, which says the core is one change's, **excludes that crash**: the CRC evidence does not
  justify it. In reachable states the byte under a fresh frame is a zero (`fallocate`'s zeros,
  `ZeroToEnd` and F-Z's fdatasync before any append, plan §2.4 item 2), so the torn type is 0,
  `ReadAll`'s "unexpected block type" error; but a stale `N.tmp` (`nonissues/etcd-wal-cut-reuses-stale-tmp.md`)
  has nonzero bytes under its headers, though it is fsynced before it is named `.wal`. Deciding
  whether to keep W1 as stated, or to weaken it to the `Data` bytes and prove the type field's case
  from wire facts (W3), is the user's.

**Satisfiable** (`W1Sat`): a crash whose every byte comes back as of the last sync satisfies it.
-/
module

public import GooseLang.Ext.Fs.Impl
public import Perennial.Golang.Defn.String
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

/-! ## The frames the reader accepts -/

/-- The length of the core of the frame at `off` of `bs`: its length word and its record bytes (the
padding after them excluded). -/
def frameCore (bs : List w8) (off : Nat) : Nat :=
  8 + (decodeFrameSize (leToU64 ((bs.drop off).take 8))).1

/-- **The offsets of the frames the reader accepts in one file**, from `lastValidOff = off` and CRC
`c` (as `walDecodeFrom`). -/
def acceptsFrom (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) : List Nat :=
  match _h : decStep C last bs off c with
  | .stop _ => []
  | .accept _ len c' => off :: acceptsFrom C last bs (off + len) c'
termination_by bs.length - off
decreasing_by have := decStep_rec_bound _h; omega

/-- **The frames the reader accepts over the files `fs`, in order, from CRC `c`** (as
`walDecodeFiles`): each as (the file's index, the frame's offset). -/
def acceptsFiles (C : WalCodec) : List (List w8) → w32 → List (Nat × Nat)
  | [], _ => []
  | [f], c => (acceptsFrom C true f 0 c).map (fun o => (0, o))
  | f :: g :: fs, c =>
    (acceptsFrom C false f 0 c).map (fun o => (0, o)) ++
      (if (walDecodeFrom C false f 0 c).stop = .eof then
        (acceptsFiles C (g :: fs) (walDecodeFrom C false f 0 c).crc).map (fun p => (p.1 + 1, p.2))
      else [])

/-! ## A directory's WAL files -/

/-- The name ends in `.wal`. -/
def walNameP (b : GoString) : Bool := decide (go!".wal" <:+ b)

/-- The `.wal` names of the directory `d`, in name order (`sort.Strings`: byte-wise). -/
def walNames (d : Dir) : List GoString :=
  ((GMap.toList d).map (·.1)).filter walNameP |>.mergeSort (fun a b => decide (go.GoStringLt a b ∨ a = b))

/-- The inodes of the files the `.wal` names of `d` name, in name order. -/
def walInos (d : Dir) : List Ino :=
  (walNames d).filterMap (fun b => match d !! b with
    | some (.file i) => some i
    | _ => none)

/-- A file's contents as reads see them (none: empty). -/
def contentsOf (F : GMap Ino OsFile) (i : Ino) : List w8 :=
  ((F !! i).map OsFile.contents).getD []

/-! ## The premise -/

/-- The bytes `[o, o + len)` of the crashed file `f'` are those of `f` **as of one change**: as of
its last sync (each its candidate stamped 0), or as of a change `n > 0` that every one of them had
been written by (each `valAt (cand b) n`, and a candidate stamped in `(0, n]`). -/
def AsOfOne (f f' : OsFile) (o len : Nat) : Prop :=
  (∀ b, o ≤ b → b < o + len → f'.cache b = valAt (f.cand b) 0) ∨
  ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
    f'.cache b = valAt (f.cand b) n ∧ ∃ p ∈ f.cand b, 0 < p.2 ∧ p.2 ≤ n

/-- **W1** at a crash from `st` to `st'` (see the file header): every frame a fresh reader accepts
over a directory's `.wal` files, from any of them on, has its core as of one change. -/
def W1 (C : WalCodec) (st st' : OsState) : Prop :=
  ∀ (j : Ino) (d : Dir), st'.fs.treeDur !! j = some d → ∀ k : Nat,
    let is := (walInos d).drop k
    let fs := is.map (contentsOf st'.fs.files)
    ∀ p ∈ acceptsFiles C fs 0#32, ∀ (i : Ino) (f f' : OsFile), is[p.1]? = some i →
      st.fs.files !! i = some f → st'.fs.files !! i = some f' →
      AsOfOne f f' p.2 (frameCore (fs.getD p.1 []) p.2)

/-- **W1 is satisfiable** (as P1's `P1Sat`): a crash whose every file comes back, byte by byte, as of
its last sync satisfies it, whatever the codec. -/
theorem W1Sat (C : WalCodec) (st st' : OsState)
    (h : ∀ i f f', st.fs.files !! i = some f → st'.fs.files !! i = some f' →
      ∀ b, f'.cache b = valAt (f.cand b) 0) :
    W1 C st st' := by
  intro j d _ k _ _ p _ i f f' _ hf hf'
  exact Or.inl (fun b _ _ => h i f f' hf hf' b)

end WalFs
end EtcdGrove
end Perennial

end
