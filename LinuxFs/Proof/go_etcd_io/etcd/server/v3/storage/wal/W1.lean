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
by which every one of its bytes had been **written by a `pwrite`**: the candidate `valAt (cand b) n`
reads (the last stamped at most `n`, `latestAt`) is stamped in `(0, n]` by a change that is not a
resize (its stamp not in the file's `OsFile.rzs`). The semantics lets a crash mix the bytes of a frame
from any of their candidates; W1 says a mix that is no such state (a frame partly written since the
sync, or mixed from several changes) does not pass the reader.

**A resize's zeros do not write a frame** (2026-11-14, `notes/wal-fsext-plan.md` §2.5, I3b; `wal-tc3`
approximated it by "a change that announced a nonzero byte of the core", which excluded real crashes;
`wal-tc4` states it exactly over the resize stamps the state now records, `OsFile.rzs`, bookkeeping only,
pending the user's review). An `ftruncate`, `fallocate`'s growth and `open`'s `O_TRUNC` announce zeros,
stamped like a write (`OsChange.ofResize`). `cut` truncates the tail at the file offset, which the page
writer leaves at a page boundary, in general inside a frame whose rest the encoder still buffers
(`wal.go:882-895`): as of the truncate, that frame is the intended bytes up to the offset and the
truncate's zeros after it, a torn frame the reader accepts only on a CRC-32C collision (or when the
buffered rest is zeros, below). W1 excludes it (`AsOfW.not_rz_window`). A `pwrite`'s zeros do write:
a frame whose last `pwrite`'s share of the core is zeros (the data's trailing zeros, the frame split
by the page writer) comes back as of that `pwrite` (`AsOfW.split_zero`).

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
the core is as of one change, each byte last written by a `pwrite` announced by then. It excludes a crash
that leaves the intended frame only when part of the intended core is zeros that **no announced
`pwrite` has written yet**: the page writer flushed the frame's first part, its rest (all zeros) is
still in the encoder's buffer, and the bytes under it are zeros (unwritten, or zeroed by `cut`'s
truncate). The reader accepts that image, rightly; W1 excludes it because the state has no record of
the buffered bytes (the semantics keeps values announced, not intentions). Rare: the unflushed rest of
a core is all zeros only when the record's data ends in zeros across a page boundary.

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

/-- The values `v` of the bytes `[o, o + len)` are those of the candidates `cs` **as of one
change**: as of the last sync (each its candidate stamped 0), or as of a change `n > 0` by which
every one of them had been written by a `pwrite` (the candidate `valAt (cs b) n` reads, `latestAt`,
is stamped in `(0, n]` by a change not among the resizes `rz`, the file's `OsFile.rzs`: not a
resize's zero). -/
def AsOfW (cs : Nat → Cands) (rz : List Nat) (v : Nat → w8) (o len : Nat) : Prop :=
  (∀ b, o ≤ b → b < o + len → v b = valAt (cs b) 0) ∨
  ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
    ∃ p, latestAt (cs b) n = some p ∧ v b = p.1 ∧ 0 < p.2 ∧ p.2 ∉ rz

/-- `AsOfW` reads `cs` and `v` only on the range, and is weaker with fewer resizes known. -/
theorem AsOfW.congr {cs cs' : Nat → Cands} {rz rz' : List Nat} {v v' : Nat → w8} {o len : Nat}
    (hcs : ∀ b, o ≤ b → b < o + len → cs b = cs' b) (hv : ∀ b, o ≤ b → b < o + len → v b = v' b)
    (hrz : ∀ s, s ∈ rz' → s ∈ rz)
    (h : AsOfW cs rz v o len) : AsOfW cs' rz' v' o len := by
  rcases h with h | ⟨n, hn, h⟩
  · left; intro b h1 h2; rw [← hcs b h1 h2, ← hv b h1 h2]; exact h b h1 h2
  · right; refine ⟨n, hn, fun b h1 h2 => ?_⟩
    obtain ⟨p, hp, hvp, hp0, hpr⟩ := h b h1 h2
    exact ⟨p, hcs b h1 h2 ▸ hp, hv b h1 h2 ▸ hvp, hp0, fun h' => hpr (hrz _ h')⟩

/-- **`AsOfW`'s weak form** (W1 before the resize amendment, 2026-11-14): as of the last sync, or
each byte `valAt (cs b) n` with some candidate stamped in `(0, n]`. -/
theorem AsOfW.weak {cs : Nat → Cands} {rz : List Nat} {v : Nat → w8} {o len : Nat}
    (h : AsOfW cs rz v o len) :
    (∀ b, o ≤ b → b < o + len → v b = valAt (cs b) 0) ∨
    ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
      v b = valAt (cs b) n ∧ ∃ q ∈ cs b, 0 < q.2 ∧ q.2 ≤ n := by
  rcases h with h | ⟨n, hn, h⟩
  · exact Or.inl h
  · right; refine ⟨n, hn, fun b h1 h2 => ?_⟩
    obtain ⟨p, hp, hvp, hp0, -⟩ := h b h1 h2
    obtain ⟨hpm, hpn⟩ := latestAt_mem hp
    exact ⟨by rw [valAt_latestAt, hp, hvp]; rfl, p, hpm, hp0, hpn⟩

/-! ### What `AsOfW` allows and excludes (sanity checks) -/

theorem latestAt_append_last (c0 : Cands) (x : w8) {s n : Nat} (hs : s ≤ n) :
    latestAt (c0 ++ [(x, s)]) n = some (x, s) := by
  simp [latestAt, List.filter_append, hs]

/-- **A frame each of whose bytes was last announced by a `pwrite`** is as of the latest of them. -/
theorem AsOfW.of_last {cs : Nat → Cands} {rz : List Nat} {v : Nat → w8} {o len n : Nat}
    (hn : 0 < n)
    (h : ∀ b, o ≤ b → b < o + len → ∃ c0 s, cs b = c0 ++ [(v b, s)] ∧ 0 < s ∧ s ≤ n ∧ s ∉ rz) :
    AsOfW cs rz v o len := by
  right; refine ⟨n, hn, fun b h1 h2 => ?_⟩
  obtain ⟨c0, s, hc, hs0, hsn, hsr⟩ := h b h1 h2
  exact ⟨(v b, s), by rw [hc]; exact latestAt_append_last c0 (v b) hsn, rfl, hs0, hsr⟩

/-- **Allowed: a frame split across two `pwrite`s whose second share of the core is all zeros**
(the data's trailing zeros; the padding is outside the core), the crash keeping the intended frame
after both were announced: the bytes `[o, o + k)` last announced by a `pwrite` stamped `s1`, the
rest of the core by one stamped `s2 ≥ s1` with zeros. (`wal-tc3`'s W1, `WroteIn`, excluded it: the
second `pwrite` wrote no nonzero byte of the core.) -/
theorem AsOfW.split_zero {cs : Nat → Cands} {rz : List Nat} {v : Nat → w8} {o k len s1 s2 : Nat}
    (hs1 : 0 < s1) (h12 : s1 ≤ s2) (hr1 : s1 ∉ rz) (hr2 : s2 ∉ rz)
    (h1 : ∀ b, o ≤ b → b < o + k → ∃ c0, cs b = c0 ++ [(v b, s1)])
    (h2 : ∀ b, o + k ≤ b → b < o + len → v b = 0 ∧ ∃ c0, cs b = c0 ++ [(0, s2)]) :
    AsOfW cs rz v o len := by
  refine AsOfW.of_last (n := s2) (by omega) (fun b hb1 hb2 => ?_)
  by_cases hk : b < o + k
  · obtain ⟨c0, hc⟩ := h1 b hb1 hk
    exact ⟨c0, s1, hc, hs1, h12, hr1⟩
  · obtain ⟨hv, c0, hc⟩ := h2 b (by omega) hb2
    exact ⟨c0, s2, by rw [hc, hv], by omega, Nat.le_refl _, hr2⟩

/-- **Excluded: a frame zeroed by a resize** (`cut`'s truncate window). Byte `b0` of the core was
durable `x0` at the last sync, then zeroed by the resize stamped `r` (its last candidate); byte `b1`
was written `y1 ≠ y0` by a change stamped `s > 0` since the sync (in practice `s < r`; not needed), and the crash keeps `y1`. The
core is as of no change: as of the sync `b1` differs; as of `n < s`, `b1` reads its synced
candidate; as of `n ∈ [s, r)`, `b0` reads its synced candidate (stamp 0); as of `n ≥ r`, `b0`
reads the resize's zero. -/
theorem AsOfW.not_rz_window {cs : Nat → Cands} {rz : List Nat} {v : Nat → w8}
    {o len b0 b1 r s : Nat} {x0 y0 y1 : w8} (hb0 : o ≤ b0 ∧ b0 < o + len)
    (hb1 : o ≤ b1 ∧ b1 < o + len) (h0 : cs b0 = [(x0, 0), (0, r)]) (hr : r ∈ rz)
    (h1 : cs b1 = [(y0, 0), (y1, s)]) (hs : 0 < s) (hv1 : v b1 = y1) (hy : y1 ≠ y0) :
    ¬ AsOfW cs rz v o len := by
  rintro (h | ⟨n, hn, h⟩)
  · have := h b1 hb1.1 hb1.2
    rw [hv1, h1] at this
    simp [valAt, show s ≠ 0 by omega] at this
    exact hy this
  · obtain ⟨p, hp, -, hp0, hpr⟩ := h b0 hb0.1 hb0.2
    obtain ⟨q, hq, -, hq0, -⟩ := h b1 hb1.1 hb1.2
    rw [h0] at hp
    rw [h1] at hq
    by_cases hrn : r ≤ n
    · simp [latestAt, hrn] at hp
      subst hp; exact hpr hr
    · by_cases hsn : s ≤ n
      · simp [latestAt, hrn] at hp
        subst hp; simp at hp0
      · simp [latestAt, hsn] at hq
        subst hq; simp at hq0

/-- The bytes `[o, o + len)` of the crashed file `f'` are those of `f` **as of one change**
(`AsOfW` of `f`'s candidates and resizes, and `f'`'s page cache). -/
def AsOfOne (f f' : OsFile) (o len : Nat) : Prop := AsOfW f.cand f.rzs f'.cache o len

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
