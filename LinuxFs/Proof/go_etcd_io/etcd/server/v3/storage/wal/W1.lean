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
record bytes, `frameCore`; not its 0-7 padding bytes) came back **as of one change** (`AsOfOne`,
`AsOfW`): as of the file's last sync (each byte its candidate stamped 0), or as of a change `n > 0`
by which every one of its bytes had been **written**: the candidate `valAt (cand b) n` reads (the last
stamped at most `n`, `latestAt`) is stamped in `(0, n]` by a change that announced a nonzero value for
some byte of the core (`WroteIn`). The semantics lets a crash mix the bytes of a frame from any of their
candidates; W1 says a mix that is no such state (a frame partly written since the sync, or mixed from
several changes) does not pass the reader.

**A resize's zeros do not write a frame** (amended 2026-11-14, `notes/wal-fsext-plan.md`, I3b,
`wal-tc3`). An `ftruncate`, `fallocate`'s growth and `open`'s `O_TRUNC` announce zeros, stamped like a
write (`OsChange.ofResize`). `cut` truncates the tail at the file offset, which the page writer leaves
at a page boundary, in general inside a frame whose rest the encoder still buffers (`wal.go:882-895`):
as of the truncate, that frame is the intended bytes up to the offset and the truncate's zeros after it,
a torn frame the reader accepts only on a CRC-32C collision. Before the amendment every byte of it had a
candidate stamped in `(0, n]`, so W1 did not exclude it. The state keeps no landed change's kind, so
"written by a `pwrite`" is approximated by "by a change that announced a nonzero byte of the core": exact
for a resize (only zeros), and conservative for a `pwrite` whose data over the core is all zeros, whose
bytes W1 then treats as unwritten.

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

**What W1 excludes beyond collisions (for the review).** In a real run the reader accepts a frame
only if its core is the intended one (or on a collision, or a torn `Type`, above), but W1 asks more: that
the core is as of one change that wrote all of it. When part of the intended core is zeros, the image can
hold the intended frame with those bytes never written, or written only by zeros, and W1 excludes that
crash though the reader would rightly accept it: bytes not yet written (a frame split across two `pwrite`s,
the crash before the second, the bytes under it zeros: so before the amendment too), zeroed by a resize
(`cut`'s truncate inside the frame, the crash before the encoder's flush), or written by a `pwrite` of
zeros only. These crashes leave the intended frame; the proof cannot tell them from torn ones because
the semantics keeps values, not intentions.

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

/-- An accepted frame's core lies in the file. -/
theorem decStep_core_bound {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    {r : WalRec} {len : Nat} {c' : w32} (h : decStep C last bs off c = .accept r len c') :
    off + frameCore bs off ≤ bs.length := by
  unfold decStep at h
  unfold frameCore
  simp only at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i h5
  simp only [Nat.not_lt, List.length_drop] at h5
  omega

theorem acceptsFrom_unfold (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) :
    acceptsFrom C last bs off c =
      match decStep C last bs off c with
      | .stop _ => []
      | .accept _ len c' => off :: acceptsFrom C last bs (off + len) c' := by
  rw [acceptsFrom]; split <;> simp_all

theorem acceptsFrom_bound (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) :
    ∀ o ∈ acceptsFrom C last bs off c, o + frameCore bs o ≤ bs.length := by
  rw [acceptsFrom_unfold]
  split
  · simp
  · rename_i r len c' h
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · exact decStep_core_bound h
    · exact acceptsFrom_bound C last bs (off + len) c' o ho
termination_by bs.length - off
decreasing_by
  have := decStep_rec_bound ‹decStep C last bs off c = DecStep.accept _ _ _›
  omega

theorem acceptsFiles_bound (C : WalCodec) :
    ∀ (fs : List (List w8)) (c : w32), ∀ p ∈ acceptsFiles C fs c,
      ∃ x, fs[p.1]? = some x ∧ p.2 + frameCore x p.2 ≤ x.length
  | [], _, p, hp => by simp [acceptsFiles] at hp
  | [f], c, p, hp => by
    simp only [acceptsFiles, List.mem_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    exact ⟨f, rfl, acceptsFrom_bound C true f 0 c o ho⟩
  | f :: g :: fs, c, p, hp => by
    simp only [acceptsFiles, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨o, ho, rfl⟩ | hp
    · exact ⟨f, rfl, acceptsFrom_bound C false f 0 c o ho⟩
    · split at hp
      · simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        obtain ⟨x, hx, hb⟩ := acceptsFiles_bound C (g :: fs) _ q hq
        exact ⟨x, by simpa using hx, hb⟩
      · simp at hp

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

/-- The candidate of `l` that `valAt l n` reads: the last one stamped at most `n`. -/
def latestAt (l : Cands) (n : Nat) : Option (w8 × Nat) := (l.filter (·.2 ≤ n)).getLast?

theorem valAt_latestAt (l : Cands) (n : Nat) : valAt l n = ((latestAt l n).map (·.1)).getD 0 := rfl

theorem latestAt_mem {l : Cands} {n : Nat} {p : w8 × Nat} (h : latestAt l n = some p) :
    p ∈ l ∧ p.2 ≤ n := by
  unfold latestAt at h
  have := List.mem_of_getLast? h
  simp only [List.mem_filter, decide_eq_true_eq] at this
  exact this

/-- The change stamped `s` **wrote** the bytes `[o, o + len)` of a file whose candidates are `cs`:
it announced a nonzero value for one of them. A resize (`ftruncate`, `fallocate`'s growth, `open`'s
`O_TRUNC`) announces only zeros (`OsChange.ofResize`), so it never writes a frame; nor does a `pwrite`
whose data over those bytes is all zeros, which the state cannot tell from a resize (the state keeps
no change's kind once it has landed). -/
def WroteIn (cs : Nat → Cands) (o len s : Nat) : Prop :=
  ∃ b, o ≤ b ∧ b < o + len ∧ ∃ v : w8, (v, s) ∈ cs b ∧ v ≠ 0

/-- The values `v` of the bytes `[o, o + len)` are those of the candidates `cs` **as of one
change**: as of the last sync (each its candidate stamped 0), or as of a change `n > 0` by which
every one of them had been written (the candidate `valAt (cs b) n` reads, `latestAt`, is stamped
in `(0, n]` by a change that wrote the range, `WroteIn`: not a resize's zero). -/
def AsOfW (cs : Nat → Cands) (v : Nat → w8) (o len : Nat) : Prop :=
  (∀ b, o ≤ b → b < o + len → v b = valAt (cs b) 0) ∨
  ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
    ∃ p, latestAt (cs b) n = some p ∧ v b = p.1 ∧ 0 < p.2 ∧ WroteIn cs o len p.2

/-- `AsOfW` reads `cs` and `v` only on the range. -/
theorem AsOfW.congr {cs cs' : Nat → Cands} {v v' : Nat → w8} {o len : Nat}
    (hcs : ∀ b, o ≤ b → b < o + len → cs b = cs' b) (hv : ∀ b, o ≤ b → b < o + len → v b = v' b)
    (h : AsOfW cs v o len) : AsOfW cs' v' o len := by
  have hw : ∀ s, WroteIn cs o len s → WroteIn cs' o len s := by
    rintro s ⟨b, h1, h2, x, hx, hx0⟩
    exact ⟨b, h1, h2, x, hcs b h1 h2 ▸ hx, hx0⟩
  rcases h with h | ⟨n, hn, h⟩
  · left; intro b h1 h2; rw [← hcs b h1 h2, ← hv b h1 h2]; exact h b h1 h2
  · right; refine ⟨n, hn, fun b h1 h2 => ?_⟩
    obtain ⟨p, hp, hvp, hp0, hpw⟩ := h b h1 h2
    exact ⟨p, hcs b h1 h2 ▸ hp, hv b h1 h2 ▸ hvp, hp0, hw _ hpw⟩

/-- **`AsOfW`'s weak form** (W1 before the resize amendment, 2026-11-14): as of the last sync, or
each byte `valAt (cs b) n` with some candidate stamped in `(0, n]`. -/
theorem AsOfW.weak {cs : Nat → Cands} {v : Nat → w8} {o len : Nat} (h : AsOfW cs v o len) :
    (∀ b, o ≤ b → b < o + len → v b = valAt (cs b) 0) ∨
    ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
      v b = valAt (cs b) n ∧ ∃ q ∈ cs b, 0 < q.2 ∧ q.2 ≤ n := by
  rcases h with h | ⟨n, hn, h⟩
  · exact Or.inl h
  · right; refine ⟨n, hn, fun b h1 h2 => ?_⟩
    obtain ⟨p, hp, hvp, hp0, -⟩ := h b h1 h2
    obtain ⟨hpm, hpn⟩ := latestAt_mem hp
    exact ⟨by rw [valAt_latestAt, hp, hvp]; rfl, p, hpm, hp0, hpn⟩

/-- The bytes `[o, o + len)` of the crashed file `f'` are those of `f` **as of one change**
(`AsOfW` of `f`'s candidates and `f'`'s page cache). -/
def AsOfOne (f f' : OsFile) (o len : Nat) : Prop := AsOfW f.cand f'.cache o len

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
