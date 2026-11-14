/- Lean-first (no Rocq counterpart).

# The WAL's abstraction relation and crash condition (`notes/wal-fsext-plan.md`, §2.1, §2.2; W1)

Pure. How a WAL directory's ghost state (`WalDur`) sits on the real tree and segment files, over an
abstract codec (`WalCodec`) and marshalling (`WalMarshal`), parameters of the layer (their protobuf
models come with W3).

* **The layout** (`WalLay`): the area directory's inode and the WAL directory's name in it, the WAL
  directory's inode, the cut positions since `Create`, the first segment still named, the named
  segments (`SegG`: name, inode, the invariant's halves of its `OsMeta` and bytes), and of the last
  segment: the bytes under its stream (`old`), how much of its stream is in the page cache (`wr`) and
  synced (`so`), and where the frames found at the generation's start end (`z0`).
* **The intended bytes** of segment `k` (`segStream`): the frames of its records, the encoder's
  chain over all segments (`chainSegs` of `segsDs` of `segsOf H cuts`, `WalEncSegs.lean`).
* **The static relation** (`WalAbsD`): the directory's `.wal` entries are the named segments, in
  name order; the cuts are cut positions, the first named segment starts at `d.cut ≤ d.pur`; every
  segment but the last holds exactly its frames, durable (a cut truncates and fdatasyncs it before
  the next starts: S/wal.go:882-888); the last holds its stream up to `wr` and `old` past it, each
  byte durable below `so`, written once since the sync between `so` and `wr` (`ByteOk`), the first
  `d.m` operations' frames below `so`; past the start's frames `old` is zeros once anything is
  appended (`ZeroToEnd` and F-Z, plan §2.4 item 2).
* **The crash condition** (`CrashOk`, plan §2.2): every crash the invariant's halves allow (the tree
  as `RegionCrashed` of the WAL's claims gives, each segment a `FileCrashedR` of its halves, and W1
  over its candidates, `W1G`) leaves the WAL absent (only if not `named`) or decoding, from the first
  file the crash kept, into the records of an image `I` of the history with `walImg d.H d.m I`
  (`CrashTo`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.W1
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncSuffix
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
public import GooseLang.Ext.Fs.NamesGhost
public import GooseLang.Ext.Fs.CrashFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section abs
variable [GooseExts]

/-! ## The layout -/

/-- A named segment file, as the invariant knows it: its name and inode, and the invariant's halves
of its `OsMeta` and of all its bytes. -/
structure SegG where
  name : GoString
  ino : Ino
  om : OsMeta
  bs : List ByteG

/-- A hex digit, lower case (`%x`). -/
def hexDigit (n : Nat) : w8 := if n < 10 then BitVec.ofNat 8 (48 + n) else BitVec.ofNat 8 (87 + n)

/-- `%016x` of `n` (`n < 2^64`). -/
def hex16 (n : Nat) : GoString := ((List.range 16).reverse).map (fun i => hexDigit (n / 16 ^ i % 16))

/-- **A segment's name** (`walName`, S/util.go: `fmt.Sprintf("%016x-%016x.wal", seq, index)`). -/
def walFileName (sq ix : Nat) : GoString := hex16 sq ++ go!"-" ++ hex16 ix ++ go!".wal"

/-- **A WAL directory's layout.** -/
structure WalLay where
  /-- The area directory's inode, and the WAL directory's name in it. -/
  jr : Ino
  nm : GoString
  /-- The WAL directory's inode. -/
  j : Ino
  /-- The start positions in the history of the segments after the first, since `Create`. -/
  cuts : List Nat
  /-- The index of the first segment still named (the earlier ones purged). -/
  first : Nat
  /-- The named segments, from `first` on, in name order. -/
  segs : List SegG
  /-- The last segment's bytes before this generation's writes on it. -/
  old : List w8
  /-- How much of the last segment's stream is in its page cache, and synced. -/
  wr : Nat
  so : Nat
  /-- Where the frames found at the generation's start end in the last segment (0 for a segment
  this generation created). -/
  z0 : Nat

/-- The history as the encoding layer has it. -/
def histM (d : WalDur) : WalHist := d.H.map WalOpG.toM

/-- The records of each segment, the CRC chained across them. -/
def segRecs (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) : List (List WalRec) :=
  chainSegs C 0#32 (segsDs Mr d.metadata true [] (segsOf (histM d) cuts))

/-- **The intended bytes of segment `k`**: the frames of its records. -/
def segStream (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) (k : Nat) : List w8 :=
  recFrames C ((segRecs C Mr d cuts).getD k [])

/-- The start position of segment `k` in the history. -/
def segStart (cuts : List Nat) (k : Nat) : Nat := ((0 :: cuts).getD k 0)

/-- A byte of the last segment: its intended value `x`, the value under it `y`, whether it is in
the intended stream (`a`), written (`w`) and synced (`s`): durable `x` if synced; else the candidate
`y` (as of the sync) followed by candidates `x` stamped by the writes that announced it (`ex`: each
attempt of a write adds one, `wp_osPWriteStart`), none if it is past the stream; if written, `x` in
the page cache and announced at least once; else `y` in the page cache (a write in flight, or one
that stopped short of it, may have announced it). -/
def ByteOk (x y : w8) (a w s : Bool) (g : ByteG) : Prop :=
  if s then g = durB x
  else ∃ ex : Cands, g.2 = (y, 0) :: ex ∧ (∀ q ∈ ex, q.1 = x ∧ 0 < q.2) ∧ (a = false → ex = []) ∧
    (if w then g.1 = x ∧ ex ≠ [] else g.1 = y)

/-- An unwritten byte, durable: its `ByteOk`. -/
theorem byteOk_durB {x y : w8} {a w s : Bool} (hw : w = false) (hs : s = false) :
    ByteOk x y a w s (durB y) := by
  subst hw hs; exact ⟨[], rfl, by simp, fun _ => rfl, rfl⟩

/-- The value of a byte that is not synced and not written. -/
theorem ByteOk.val_unw {x y : w8} {a : Bool} {g : ByteG} (h : ByteOk x y a false false g) :
    g.1 = y := by
  obtain ⟨ex, -, -, -, h⟩ := h; exact h

/-- The value of a byte that is written. -/
theorem ByteOk.val_w {x y : w8} {a s : Bool} {g : ByteG} (h : ByteOk x y a true s g) : g.1 = x := by
  unfold ByteOk at h
  split at h
  · rw [h]
  · obtain ⟨ex, -, -, -, h, -⟩ := h; exact h

/-- **A byte's `ByteOk` as the stream grows** (`Save`'s commit appends `X`): a byte of the old
stream keeps its intended value; one past it was never written nor announced. -/
theorem ByteOk.snoc {S X : List w8} {y : w8} {w s : Bool} {g : ByteG} {b : Nat}
    (h : ByteOk (S.getD b 0) y (decide (b < S.length)) w s g) (hw : w = true → b < S.length)
    (hs : s = true → b < S.length) :
    ByteOk ((S ++ X).getD b 0) y (decide (b < (S ++ X).length)) w s g := by
  by_cases hb : b < S.length
  · have e1 : (S ++ X).getD b 0 = S.getD b 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hb, ← List.getD_eq_getElem?_getD]
    have e2 : decide (b < (S ++ X).length) = decide (b < S.length) := by
      simp only [List.length_append, decide_eq_decide]; omega
    rw [e1, e2]; exact h
  · have hw' : w = false := by cases w; rfl; exact absurd (hw rfl) hb
    have hs' : s = false := by cases s; rfl; exact absurd (hs rfl) hb
    subst hw' hs'
    obtain ⟨ex, h1, -, h3, h4⟩ := h
    have hex : ex = [] := h3 (by simp; omega)
    subst hex
    exact ⟨[], h1, by simp, fun _ => rfl, h4⟩

/-- A segment's `OsMeta` half bounds a crash's size to its bytes' (no resize window open on it). -/
def SegExact (g : SegG) : Prop := g.om.lo = g.bs.length ∧ g.om.hi = g.bs.length

/-- An `OsMeta` bounds a crash's size to its size (no resize window open on its file): what
`os.truncSup`'s `P` is for the tail's truncate at its write position (`walTail_truncSup`; W6 log,
twenty-second session). -/
def OsExact (m : Fs.OsMeta) : Prop := m.lo = m.size ∧ m.hi = m.size

theorem SegExact.of_os {g : SegG} (hsz : g.om.size = g.bs.length) (h : OsExact g.om) : SegExact g :=
  ⟨h.1.trans hsz, h.2.trans hsz⟩

/-- Every named segment of `lay` but the last is exact (`WalAbsD.metas`); the last too. -/
def TailExact (lay : WalLay) : Prop := ∀ g, lay.segs.getLast? = some g → SegExact g

/-! ## The candidates past a segment's bytes -/

/-- The candidates `m` knows (`OsMeta.pc`) of `k` bytes from `b` on, up to the first it does not
know, as ghost bytes (their value 0: `W1G` reads only the candidates). -/
def pcRunN (m : OsMeta) : Nat → Nat → List ByteG
  | _, 0 => []
  | b, k + 1 => match m.pc b with
    | some c => (0, c) :: pcRunN m (b + 1) k
    | none => []

/-- The candidates `m` knows from byte `b` on, below `m.hi`, up to the first it does not know. -/
def pcRun (m : OsMeta) (b : Nat) : List ByteG := pcRunN m b (m.hi - b)

theorem pcRunN_getElem? {m : OsMeta} : ∀ {b k j : Nat} {y : ByteG}, (pcRunN m b k)[j]? = some y →
    j < k ∧ m.pc (b + j) = some y.2
  | _, 0, _, _, h => by simp [pcRunN] at h
  | b, k + 1, j, y, h => by
    unfold pcRunN at h
    split at h
    · rename_i c hc
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h; exact ⟨by omega, by simpa using hc⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨h1, h2⟩ := pcRunN_getElem? h
        exact ⟨by omega, by rw [show b + (j + 1) = b + 1 + j by omega]; exact h2⟩
    · simp at h

theorem pcRunN_length_le {m : OsMeta} : ∀ {b k : Nat}, (pcRunN m b k).length ≤ k
  | _, 0 => by simp [pcRunN]
  | b, k + 1 => by
    unfold pcRunN
    split
    · simp only [List.length_cons]; have := pcRunN_length_le (m := m) (b := b + 1) (k := k); omega
    · simp

/-- **A segment's ghost bytes, then the candidates its `OsMeta` knows past them** (W1 past the
bytes, I3b, `wal-tc6`): in a resize window, or after a write past the preallocated size, a crash may
leave the segment longer than the bytes the invariant holds (up to `om.hi`), and its frames there are
as of the candidates `om` knows past the size (`OsMeta.pc`: a truncate's cut-off bytes, `rzMeta`/
`rsPostK true`; known zeros). The bytes of an exact segment (`om.hi ≤ |bs|`). -/
def segBytesX (g : SegG) : List ByteG := g.bs ++ pcRun g.om g.bs.length

theorem segBytesX_of_hi {g : SegG} (h : g.om.hi ≤ g.bs.length) : segBytesX g = g.bs := by
  unfold segBytesX pcRun
  rw [show g.om.hi - g.bs.length = 0 by omega]
  simp [pcRunN]

theorem segBytesX_getElem?_lt {g : SegG} {b : Nat} (hb : b < g.bs.length) :
    (segBytesX g)[b]? = g.bs[b]? := List.getElem?_append_left hb

theorem segBytesX_getD_lt {g : SegG} {b : Nat} (hb : b < g.bs.length) (d : ByteG) :
    (segBytesX g).getD b d = g.bs.getD b d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, segBytesX_getElem?_lt hb]

theorem segBytesX_length_le {g : SegG} : g.bs.length ≤ (segBytesX g).length := by
  simp [segBytesX]

/-- `segBytesX g` stops at `hi` (or at the bytes' end). -/
theorem segBytesX_length_le_max (g : SegG) : (segBytesX g).length ≤ max g.bs.length g.om.hi := by
  have := pcRunN_length_le (m := g.om) (b := g.bs.length) (k := g.om.hi - g.bs.length)
  simp only [segBytesX, pcRun, List.length_append]; omega

/-- A byte of `segBytesX g` past `g.bs` is one `g.om` knows, below `g.om.hi`. -/
theorem segBytesX_getElem?_ge {g : SegG} {b : Nat} {y : ByteG} (hb : g.bs.length ≤ b)
    (h : (segBytesX g)[b]? = some y) : b < g.om.hi ∧ g.om.pc b = some y.2 := by
  unfold segBytesX at h
  rw [List.getElem?_append_right hb] at h
  obtain ⟨h1, h2⟩ := pcRunN_getElem? h
  refine ⟨by omega, ?_⟩
  rw [show b = g.bs.length + (b - g.bs.length) by omega]; exact h2

/-- The candidates of `segBytesX g` are a file's whose candidates are `g.bs`'s and, past the size
(`|g.bs|`), those `g.om` knows. -/
theorem segBytesX_cand {g : SegG} {f : Fs.OsFile} (hsz : g.om.size = g.bs.length)
    (hbs : ∀ b (y : ByteG), g.bs[b]? = some y → f.cand b = y.2)
    (hpc : ∀ b c, g.om.size ≤ b → g.om.pc b = some c → f.cand b = c) :
    ∀ b (y : ByteG), (segBytesX g)[b]? = some y → f.cand b = y.2 := by
  intro b y h
  by_cases hb : b < g.bs.length
  · rw [segBytesX_getElem?_lt hb] at h; exact hbs b y h
  · obtain ⟨-, h2⟩ := segBytesX_getElem?_ge (by omega) h
    exact hpc b y.2 (by omega) h2

/-- **The last segment `g`, no resize window open on it** (`WalAbsD.last`): its stream up to `wr`,
`old` past it, each byte durable below `so`, written once since the sync between `so` and `wr`
(`ByteOk`), `old` zeros past the start's frames once anything is appended. -/
def TailLast (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (g : SegG) : Prop :=
    let S := segStream C Mr d lay.cuts lay.cuts.length
    lay.so ≤ lay.wr ∧ lay.wr ≤ S.length ∧ g.bs.length = lay.old.length ∧ lay.wr ≤ lay.old.length ∧
    (∀ b (x : ByteG), g.bs[b]? = some x →
      ByteOk (S.getD b 0) (lay.old.getD b 0) (decide (b < S.length)) (decide (b < lay.wr))
        (decide (b < lay.so)) x) ∧
    lay.z0 ≤ lay.wr ∧ (S.take lay.z0 = lay.old.take lay.z0) ∧
    (lay.z0 < S.length → ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)

/-- **The shape of a candidate `q` of byte `b` of the last segment, at or past the write position,
in a resize window** (I3b; `TailWin`, W6 log, seventeenth session): the byte under the stream as of
the generation's start (`old`'s, stamp 0; zero past `old`), a known resize's zero (its stamp among
`rz`), or the stream's byte, stamped by a write (inside the stream). -/
def WinShape (S old : List w8) (rz : List Nat) (b : Nat) (q : w8 × Nat) : Prop :=
  q = (old.getD b 0, 0) ∨ (q.1 = 0 ∧ q.2 ∈ rz) ∨ (b < S.length ∧ q.1 = S.getD b 0 ∧ 0 < q.2)

theorem WinShape.mono_rz {S old : List w8} {rz rz' : List Nat} {b : Nat} {q : w8 × Nat}
    (h : WinShape S old rz b q) (hrz : ∀ s ∈ rz, s ∈ rz') : WinShape S old rz' b q := by
  rcases h with h | ⟨h1, h2⟩ | h
  · exact .inl h
  · exact .inr (.inl ⟨h1, hrz _ h2⟩)
  · exact .inr (.inr h)

/-- The stream grows (`Save`'s commit): a candidate keeps its shape. -/
theorem WinShape.snoc {S X old : List w8} {rz : List Nat} {b : Nat} {q : w8 × Nat}
    (h : WinShape S old rz b q) : WinShape (S ++ X) old rz b q := by
  rcases h with h | h | ⟨h1, h2, h3⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨by simp; omega, ?_, h3⟩)
    rw [h2, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]

/-- A known resize's zero has the shape. -/
theorem winShape_rz {S old : List w8} {rz : List Nat} {b n : Nat} (h : n ∈ rz) :
    WinShape S old rz b ((0 : w8), n) := .inr (.inl ⟨rfl, h⟩)

/-- **The candidates of the last segment `g` past the write position `wr`, in a window** (`TailWin`'s
last conjunct): every byte `g.om` may leave past its bytes is known (`segBytesX g` reaches `hi`), and
each candidate of `segBytesX g` from `wr` on has `WinShape`. -/
def WinCands (S old : List w8) (wr : Nat) (g : SegG) : Prop :=
  g.om.hi ≤ (segBytesX g).length ∧
  ∀ b, wr ≤ b → b < (segBytesX g).length →
    ∀ q ∈ ((segBytesX g).getD b (0, [])).2, WinShape S old g.om.rz b q

theorem WinCands.snoc {S X old : List w8} {wr : Nat} {g : SegG} (h : WinCands S old wr g) :
    WinCands (S ++ X) old wr g :=
  ⟨h.1, fun b hb1 hb2 q hq => (h.2 b hb1 hb2 q hq).snoc⟩

/-- **The last segment `g` in a resize window** (I3b; `WalAbsD.last`): `TailLast`'s `ByteOk` below the
least crash size `lo` only (W6 log, twenty-fourth session: was below `wr`; a write past the size from an
exact tail keeps `lo` at the size, so the bytes in `[wr, lo)` it may write next keep their shape; the bytes
from `lo` to `wr`, written in the window, are `WinLow`'s, in `WinLast`); the segment at least `wr` long
(`cut` truncates it to `wr`, `ZeroToEnd` to the start's frames, then grows it back to its size; a write
past the size makes it longer than `old`, whose bytes past its end are zeros: `old.getD`), `z0` within
`old`; its candidates from `wr` on, and those its `OsMeta` knows past its bytes, `old`'s byte, a known
resize's zero or the stream's byte (`WinCands`: a truncate's announced zeros, a growth's bytes with the
candidates the file had past its size, a write's). -/
def TailWin (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (g : SegG) : Prop :=
    let S := segStream C Mr d lay.cuts lay.cuts.length
    lay.so ≤ lay.wr ∧ lay.wr ≤ S.length ∧ lay.z0 ≤ lay.old.length ∧ lay.wr ≤ g.bs.length ∧
    (∀ b (x : ByteG), g.bs[b]? = some x → b < g.om.lo →
      ByteOk (S.getD b 0) (lay.old.getD b 0) (decide (b < S.length)) (decide (b < lay.wr))
        (decide (b < lay.so)) x) ∧
    lay.z0 ≤ lay.wr ∧ (S.take lay.z0 = lay.old.take lay.z0) ∧
    (lay.z0 < S.length → ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0) ∧
    WinCands S lay.old lay.wr g

/-- **F-Z**: past the frames found at the generation's start, the tail is zeros (`ReadAll`'s
`ZeroToEnd` and fdatasync; a segment this generation created is zeros past its headers). -/
def TailZeros (lay : WalLay) : Prop :=
  ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0

/-- **The length word at the write position is zero** (`old`'s 8 bytes from `wr`; zero past `old`;
`TailCrashPend.lean`, `wal-tc16`). -/
def LenZ (lay : WalLay) : Prop := ∀ j, j < 8 → lay.old.getD (lay.wr + j) 0 = 0

/-- **A tail registered, not yet zeroed, whose reader stopped at `wr` with `io.EOF`**: nothing written
past the start's frames (`wr = z0`), the length word there zero (`LenZ`). -/
def TailPend (lay : WalLay) : Prop := lay.wr = lay.z0 ∧ LenZ lay

/-- **The last segment's bytes past the write position are zero-valued** (in a resize window, I3b:
finding 2, W6 log, sixteenth session; nineteenth session): `cut`'s truncate leaves none past `wr`, a write
past the size ends at `wr`, `ZeroToEnd`'s growth zeros them (the cut-off bytes of its in-flight truncate
are the exact tail's, zero by F-Z, `TailZeros`). The window's fdatasync needs it: the synced tail's
bytes past `wr` are then `old`'s, the layout's `old` zeros past `wr` (`syncLayW`). -/
def WinZero (lay : WalLay) (g : SegG) : Prop :=
  ∀ b (x : ByteG), lay.wr ≤ b → g.bs[b]? = some x → x.1 = 0

/-- **A crash may leave a zero at each byte of the last segment from the write position on** (in a
resize window, I3b; W6 log, twentieth and twenty-first sessions; in place of `lo ≤ wr`, which a write
past the size from an exact tail falsifies: it keeps `lo` at the size it found, above the write position
until it completes): each byte of `segBytesX g` from `wr` on is at or past the least size a crash may
leave (`lo`), or has a zero candidate (an exact tail's `(old b, 0)` with `old b = 0` by F-Z, a truncate's
announced zero, the zeros past `zf`; candidates are only appended, so every step keeps it). -/
def WinHead (lay : WalLay) (g : SegG) : Prop :=
  ∀ b, lay.wr ≤ b → b < (segBytesX g).length →
    g.om.lo ≤ b ∨ ∃ s, ((0 : w8), s) ∈ ((segBytesX g).getD b (0, [])).2

/-- `lo ≤ wr` (a window opened by a truncate to `wr`) gives `WinHead`. -/
theorem WinHead.of_lo {lay : WalLay} {g : SegG} (h : g.om.lo ≤ lay.wr) : WinHead lay g :=
  fun _ hb _ => .inl (Nat.le_trans h hb)

/-- **A crash leaves the last segment at least `max so z0` long, in a window** (W6 log, twenty-third
session): a window opens by a truncate to `wr` (`cut`'s, `ZeroToEnd`'s: `so, z0 ≤ wr`) or by a write past
the size from an exact tail (`lo` its size, past `wr`); writes do not lower `lo` (`announce`'s `min lo tg`
with `tg` at least the size), a growth neither. The window's crash decoding needs it: a zero a crash
leaves at or past `lo` is past the synced bytes and the frames found (`TailVals`). -/
def WinLo (lay : WalLay) (g : SegG) : Prop := max lay.so lay.z0 ≤ g.om.lo

/-- **A byte written in a resize window, from its least crash size on** (`WinLow`; W6 log,
twenty-fourth session): the stream's byte, each candidate `WinShape` (a byte written past a truncate keeps
the truncate's zero, `cut`'s flush after its truncate; a byte grown over by a write past the size, the
candidates the file had there). Weaker than `ByteOk`'s written case, which has no resize's zero. -/
def WinW (S old : List w8) (rz : List Nat) (b : Nat) (x : ByteG) : Prop :=
  x.1 = S.getD b 0 ∧ ∀ q ∈ x.2, WinShape S old rz b q

theorem WinW.mono_rz {S old : List w8} {rz rz' : List Nat} {b : Nat} {x : ByteG}
    (h : WinW S old rz b x) (hrz : ∀ s ∈ rz, s ∈ rz') : WinW S old rz' b x :=
  ⟨h.1, fun q hq => (h.2 q hq).mono_rz hrz⟩

/-- The stream grows (`Save`'s commit): a byte inside the stream keeps `WinW`. -/
theorem WinW.snoc {S X old : List w8} {rz : List Nat} {b : Nat} {x : ByteG}
    (h : WinW S old rz b x) (hb : b < S.length) : WinW (S ++ X) old rz b x := by
  refine ⟨?_, fun q hq => (h.2 q hq).snoc⟩
  rw [h.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hb]

/-- **The bytes of the last segment written in a resize window** (`WinLast`; W6 log, twenty-fourth
session): from the least crash size `lo` to `wr`, `WinW`. Empty when the window opened by a truncate to
`wr` (`lo ≤ wr`, nothing written yet); a write past the size, or `cut`'s flush after its truncate, writes
there. -/
def WinLow (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (g : SegG) : Prop :=
  ∀ b (x : ByteG), g.bs[b]? = some x → g.om.lo ≤ b → b < lay.wr →
    WinW (segStream C Mr d lay.cuts lay.cuts.length) lay.old g.om.rz b x

/-- **The last segment in a resize window** (`WalAbsD.last`'s window branch): `TailWin`, a zero a
crash may leave at each byte from `wr` on (`WinHead`; until the twenty-second session of the W6 log,
`lo ≤ wr`, which a write past the size from an exact tail falsifies; the truncate at `wr`, which
needed it of the size, gets it from the handle instead: `os.truncSup`'s `P`), `WinZero` given F-Z
(`TailZeros lay → WinZero lay g`, `wal-tc17`, finding A of the W1 log's twenty-sixth session: a pending
tail's truncate keeps `old`'s torn values past `wr`; the window's fdatasync takes `WinZero` as a
premise), and `old`
no longer than the largest size a crash may leave (a window opens from an exact tail, `hi = |bs| =
|old|`, and no step before the fdatasync lowers `hi`; `wal-tc12`'s option (b)), `WinLo`, and the bytes
written from `lo` to `wr` (`WinLow`, W6 log, twenty-fourth session). -/
def WinLast (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (g : SegG) : Prop :=
  TailWin C Mr d lay g ∧ WinHead lay g ∧ (TailZeros lay → WinZero lay g) ∧ lay.old.length ≤ g.om.hi ∧
    WinLo lay g ∧ WinLow C Mr d lay g

/-- An exact tail's bytes past `wr` are `old`'s (unwritten), so zero where `old` is (F-Z). -/
theorem TailLast.winZero {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g : SegG}
    (h : TailLast C Mr d lay g)
    (hZ : ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0) : WinZero lay g := by
  obtain ⟨h1, -, h3, -, h5, h6, -⟩ := h
  intro b x hb hx
  have hbl : b < g.bs.length := (List.getElem?_eq_some_iff.1 hx).1
  have hw : decide (b < lay.wr) = false := by simp; omega
  have hs : decide (b < lay.so) = false := by simp; omega
  have hB := h5 b x hx
  rw [hw, hs] at hB
  rw [hB.val_unw]; exact hZ b (by omega) (by omega)

/-- A byte at or past the write position, not synced: its candidates have the window's shape. -/
theorem ByteOk.winShape {S old : List w8} {rz : List Nat} {w s : Bool} {b : Nat} {g : ByteG}
    (h : ByteOk (S.getD b 0) (old.getD b 0) (decide (b < S.length)) w s g) (hs : s = false) :
    ∀ q ∈ g.2, WinShape S old rz b q := by
  subst hs
  obtain ⟨ex, h1, h2, h3, -⟩ := h
  intro q hq
  rw [h1] at hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact .inl rfl
  · have hb : b < S.length := by
      rcases Nat.lt_or_ge b S.length with hb | hb
      · exact hb
      · have := h3 (by simp; omega)
        subst this; simp at hq
    exact .inr (.inr ⟨hb, (h2 q hq).1, (h2 q hq).2⟩)

/-- A written, unsynced byte's `ByteOk` gives `WinW`. -/
theorem ByteOk.winW {S old : List w8} {rz : List Nat} {s : Bool} {b : Nat} {x : ByteG}
    (h : ByteOk (S.getD b 0) (old.getD b 0) (decide (b < S.length)) true s x) (hs : s = false) :
    WinW S old rz b x :=
  ⟨h.val_w, fun q hq => ByteOk.winShape (w := true) h hs q hq⟩

/-- `TailLast` gives `TailWin`, the segment exact (no candidates past its bytes). -/
theorem TailLast.win {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g : SegG}
    (h : TailLast C Mr d lay g) (hx : SegExact g) : TailWin C Mr d lay g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hX : segBytesX g = g.bs := segBytesX_of_hi (Nat.le_of_eq hx.2)
  refine ⟨h1, h2, by omega, by omega, fun b x hb _ => h5 b x hb, h6, h7, h8, ?_, ?_⟩
  · rw [hX]; exact Nat.le_of_eq hx.2
  · intro b hb1 hb2 q hq
    rw [hX] at hb2 hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb2, Option.getD_some] at hq
    exact (h5 b _ (List.getElem?_eq_getElem hb2)).winShape (by simp; omega) q hq

/-- The reader accepts nothing on zeros. -/
theorem decStep_zeros_any (C : WalCodec) (last : Bool) {bs : List w8} {off z : Nat} {c : w32}
    (hbs : bs.drop off = List.replicate z (0#8)) (r : WalRec) (len : Nat) (c' : w32) :
    decStep C last bs off c ≠ .accept r len c' := by
  by_cases hz : z = 0 ∨ 8 ≤ z
  · rw [decStep_zeros C last hz hbs]; intro h; cases h
  · unfold decStep
    simp only [hbs, List.length_replicate]
    rw [if_neg (by omega), if_pos (by omega)]
    intro h; cases h

/-- **The static relation of the WAL `d` and its layout `lay`**, the WAL directory's entries being
`ents` (plan §2.1). -/
structure WalAbsD (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (ents : Ents) :
    Prop where
  /-- The directory's `.wal` entries are the named segments, in name order. -/
  names : walInos ents = lay.segs.map (·.ino) ∧ (lay.segs.map (·.name)).Pairwise (fun a b => go.GoStringLt a b)
  /-- The cuts: increasing cut positions (`walCutPos`) of the history; the last named segment is
  the last segment. -/
  cuts : (∀ b ∈ lay.cuts, walCutPos (histM d) b) ∧ lay.cuts.Pairwise (· < ·) ∧
    lay.first + lay.segs.length = lay.cuts.length + 1
  /-- The name bound (W4a.2): a segment starting at `b` is named with an index above every entry
  index before `b`; the index a `uint64` (`walFileName` keeps it modulo `2^64`: `Create` names its
  segment with 0, a cut with `max(w.enti, w.snapi) + 1`, below `2^64` by the handle's bound). -/
  nameBound : ∀ k (g : SegG), lay.segs[k]? = some g → ∃ sq ix : Nat,
    g.name = walFileName sq ix ∧ ix < 2 ^ 64 ∧ (0 < lay.first + k → walLastIdx ((histM d).take (segStart lay.cuts (lay.first + k))) + 1 ≤ ix)
  /-- What `Open` reads from, and what was purged. -/
  cut : d.cut = segStart lay.cuts lay.first ∧ (0 < lay.first → d.cut ≤ d.pur)
  /-- Each segment's `OsMeta` half: its size is its bytes', no sync cut, a crash leaves it with
  a size around it (`lo ≤ |bs| ≤ hi`); exactly its size (`SegExact`) but for the last segment, whose
  resizes (`cut`'s truncate, `ReadAll`'s `ZeroToEnd`) announce other sizes until the fdatasync after
  them (I3b). -/
  metas : ∀ g ∈ lay.segs, g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo ≤ g.bs.length ∧
    g.bs.length ≤ g.om.hi ∧ (lay.segs.getLast? = some g ∨ SegExact g)
  /-- Every named segment but the last holds exactly its frames, durable. -/
  intact : ∀ k (g : SegG), k + 1 < lay.segs.length → lay.segs[k]? = some g →
    g.bs = (segStream C Mr d lay.cuts (lay.first + k)).map durB
  /-- The last segment: its stream up to `wr`, `old` past it, durable below `so`; while a resize
  window is open on it (`¬ SegExact g`, I3b: from a resize's first step to the fdatasync after it),
  only the bytes below `wr`, the segment no longer than `old` and at least `wr` long
  (`TailWin`), a zero a crash may leave from `wr` on (`WinHead`), the bytes from `wr` on zero given F-Z
  (`WinZero`) and `|old| ≤ hi` (`WinLast`). -/
  last : ∀ g, lay.segs.getLast? = some g →
    (SegExact g → TailLast C Mr d lay g) ∧ (¬ SegExact g → WinLast C Mr d lay g)
  /-- The synced operations' frames, in the last segment, are synced. -/
  synced : d.m ≤ d.H.length ∧
    (recFrames C ((segRecs C Mr { d with H := d.H.take d.m } lay.cuts).getD lay.cuts.length [])).length
      ≤ lay.so
  /-- Every segment but the last is synced (`cut` fdatasyncs a segment before it starts the next). -/
  lastSynced : segStart lay.cuts lay.cuts.length ≤ d.m
  /-- Every record fits a frame. -/
  fit : RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))
  /-- Nothing appended this generation: the reader of the last file stops after its frames (at the
  chain's CRC after all the WAL's records). -/
  tailStop : lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length → ∀ r len c',
    decStep C true lay.old lay.z0
      (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))) ≠ .accept r len c'
  /-- There is a segment (`Create` makes the first; a purge keeps the last). -/
  nonempty : lay.segs ≠ []
  /-- Every cut past the history's start (`walCutPos` allows 0): a cut follows a `Save` that wrote a
  record (`cut.spec`'s `0 < |H|`), and a crash keeps the cuts. `ReadAll` from a cut file reads past a
  nonempty prefix (`readAll_success`). -/
  cutPos : ∀ b ∈ lay.cuts, 0 < b

/-- **The last segment's facts, no resize window open on it.** -/
theorem WalAbsD.lastEx {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (hex : TailExact lay) (g : SegG) (hg : lay.segs.getLast? = some g) :
    TailLast C Mr d lay g :=
  (h.last g hg).1 (hex g hg)

/-- **The last segment's facts below `wr`**, a resize window open on it or not. -/
theorem WalAbsD.lastWin {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) :
    TailWin C Mr d lay g := by
  by_cases hx : SegExact g
  · exact ((h.last g hg).1 hx).win hx
  · exact ((h.last g hg).2 hx).1

/-- **A crash may leave a zero from the write position on, in a window** (`WalAbsD.last`'s `WinHead`). -/
theorem WalAbsD.winHead {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) (hx : ¬ SegExact g) :
    WinHead lay g :=
  ((h.last g hg).2 hx).2.1

/-- **`old` is no longer than a window's `hi`** (`WalAbsD.last`'s window branch). -/
theorem WalAbsD.oldHi {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) (hx : ¬ SegExact g) :
    lay.old.length ≤ g.om.hi :=
  ((h.last g hg).2 hx).2.2.2.1

/-- **A window's least crash size is past the synced bytes and the frames found** (`WinLo`). -/
theorem WalAbsD.winLo {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) (hx : ¬ SegExact g) :
    WinLo lay g :=
  ((h.last g hg).2 hx).2.2.2.2.1

/-- **The bytes written in a window, from `lo` to `wr`** (`WalAbsD.last`'s `WinLow`). -/
theorem WalAbsD.winLow {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) (hx : ¬ SegExact g) :
    WinLow C Mr d lay g :=
  ((h.last g hg).2 hx).2.2.2.2.2

/-- **The last segment's bytes below the write position**, window or not (W6 log, twenty-fourth
session): below the least crash size `lo`, `ByteOk`; from `lo` on (in a window only: an exact tail's `lo`
is its length), past the synced bytes and the frames found, `WinW`. -/
theorem WalAbsD.low {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) (b : Nat) (x : ByteG)
    (hb : g.bs[b]? = some x) (hbw : b < lay.wr) :
    (b < g.om.lo ∧ ByteOk ((segStream C Mr d lay.cuts lay.cuts.length).getD b 0) (lay.old.getD b 0)
        (decide (b < (segStream C Mr d lay.cuts lay.cuts.length).length)) (decide (b < lay.wr))
        (decide (b < lay.so)) x) ∨
      (g.om.lo ≤ b ∧ max lay.so lay.z0 ≤ b ∧
        WinW (segStream C Mr d lay.cuts lay.cuts.length) lay.old g.om.rz b x) := by
  by_cases hx : SegExact g
  · have hbl : b < g.bs.length := (List.getElem?_eq_some_iff.1 hb).1
    exact .inl ⟨by rw [hx.1]; exact hbl, ((h.last g hg).1 hx).2.2.2.2.1 b x hb⟩
  · by_cases hlo : b < g.om.lo
    · exact .inl ⟨hlo, (h.lastWin g hg).2.2.2.2.1 b x hb hlo⟩
    · have hwl := h.winLo g hg hx
      unfold WinLo at hwl
      exact .inr ⟨by omega, by omega, h.winLow g hg hx b x hb (by omega) hbw⟩

/-- **A byte below the write position, past the synced bytes, has `WinW`** (any stamps known
`rz'` above the tail's): `WalAbsD.low`'s two cases. What a step that lowers `lo` below the write position
(a truncate to `wr`) or writes there gives `WinLow` from. -/
theorem WalAbsD.lowW {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) (b : Nat) (x : ByteG)
    (hb : g.bs[b]? = some x) (hbw : b < lay.wr) (hso : lay.so ≤ b) {rz' : List Nat}
    (hrz : ∀ s ∈ g.om.rz, s ∈ rz') :
    WinW (segStream C Mr d lay.cuts lay.cuts.length) lay.old rz' b x := by
  rcases h.low g hg b x hb hbw with ⟨-, hB⟩ | ⟨-, -, hW⟩
  · rw [show decide (b < lay.wr) = true from decide_eq_true hbw,
      show decide (b < lay.so) = false from decide_eq_false (by omega)] at hB
    exact ByteOk.winW (rz := rz') hB rfl
  · exact hW.mono_rz hrz

/-- **The tail's least crash size is past the synced bytes and the frames found**, window or not (an
exact tail's is its length, at least `wr`). -/
theorem WalAbsD.winLo_any {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) : WinLo lay g := by
  by_cases hx : SegExact g
  · obtain ⟨h1, -, h3, h4, -, h6, -⟩ := (h.last g hg).1 hx
    unfold WinLo; rw [hx.1]; omega
  · exact h.winLo g hg hx

/-- **`old` is no longer than the tail's `hi`**, window or not (an exact tail is as long as `old`). -/
theorem WalAbsD.oldHi_any {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) :
    lay.old.length ≤ g.om.hi := by
  by_cases hx : SegExact g
  · obtain ⟨-, -, h3, -⟩ := (h.last g hg).1 hx
    rw [← h3, hx.2]; exact Nat.le_refl _
  · exact h.oldHi g hg hx

/-- **A window's bytes past the write position are zero-valued**, given F-Z (`WalAbsD.last`'s
`WinZero`). -/
theorem WalAbsD.winZero {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g) (hx : ¬ SegExact g)
    (hZ : TailZeros lay) : WinZero lay g :=
  ((h.last g hg).2 hx).2.2.1 hZ

/-- **The last segment's bytes past the write position are zero-valued**, given F-Z (`TailZeros`). -/
theorem WalAbsD.zeroPast {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (g : SegG) (hg : lay.segs.getLast? = some g)
    (hZ : ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0) : WinZero lay g := by
  by_cases hx : SegExact g
  · exact ((h.last g hg).1 hx).winZero hZ
  · exact h.winZero g hg hx hZ

/-- **Every segment's `OsMeta` half exact**, no resize window open on the last (the form of
`metas` before I3b). -/
theorem WalAbsD.metasEx {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) (hex : TailExact lay) (g : SegG) (hg : g ∈ lay.segs) :
    g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧ g.om.hi = g.bs.length := by
  obtain ⟨h1, h2, -, -, h5⟩ := h.metas g hg
  have : SegExact g := by rcases h5 with h5 | h5; exact hex g h5; exact h5
  exact ⟨h1, h2, this.1, this.2⟩

/-- The last segment's `OsMeta` and bytes decide whether a window is open: two layouts with the same
last segment are exact together. -/
theorem tailExact_of_last {lay lay' : WalLay} (h : lay'.segs.getLast? = lay.segs.getLast?)
    (hex : TailExact lay) : TailExact lay' := fun g hg => hex g (h ▸ hg)

/-- A segment whose `OsMeta` half is exact satisfies `metas`' last clause. -/
theorem segExact_metas {g : SegG} {lay : WalLay} (h : SegExact g) :
    lay.segs.getLast? = some g ∨ SegExact g := Or.inr h

/-! ## W1 over the ghost candidates -/

/-- The ghost form of `AsOfOne`: the image bytes `img` of `[o, o + len)` against the bytes `bs`'
candidates, `rz` resizes of the file known. -/
def AsOfOneG (bs : List ByteG) (rz : List Nat) (img : List w8) (o len : Nat) : Prop :=
  AsOfW (fun b => (bs.getD b (0, [])).2) rz (fun b => img.getD b 0) o len

/-- **W1 over a crashed WAL directory**, from the ghost candidates: its `.wal` files `js` (in name
order), their images `img`, read from any of them on with a fresh reader; a file that is a segment
the invariant knows (`bsOf i = some bs`) has every accepted frame whose core lies in `bs` (`wal-tc3`;
was: the whole image no longer than `bs`) as of one change of `bs`' candidates. (The image may be longer
than the bytes the invariant knows in a resize window, I3b: a frame past them is the state's, which the
ghost state does not see.) `rzOf i`: stamps known to be resizes of the file `i` (`OsFile.rzs`;
`CrashOk` passes those the layout's `OsMeta` halves know, `segRzOf`, `wal-tc5`). -/
def W1G (C : WalCodec) (js : List Ino) (img : Ino → List w8) (bsOf : Ino → Option (List ByteG))
    (rzOf : Ino → List Nat) : Prop :=
  ∀ k, ∀ p ∈ acceptsFiles C ((js.drop k).map img) 0#32, ∀ i bs, (js.drop k)[p.1]? = some i →
    bsOf i = some bs → p.2 + frameCore (img i) p.2 ≤ bs.length →
      AsOfOneG bs (rzOf i) (img i) p.2 (frameCore (img i) p.2)

/-- The ghost bytes of the segment of inode `i`, if it is one of the layout's, with the candidates
its `OsMeta` knows past them (`segBytesX`). -/
def segBytesOf (lay : WalLay) (i : Ino) : Option (List ByteG) :=
  (lay.segs.find? (fun g => decide (g.ino = i))).map segBytesX

/-- The resize stamps the layout's `OsMeta` half of the segment of inode `i` knows (`OsMeta.rz`),
if it is one of the layout's. -/
def segRzOf (lay : WalLay) (i : Ino) : List Nat :=
  ((lay.segs.find? (fun g => decide (g.ino = i))).map (·.om.rz)).getD []

theorem segRzOf_mem {lay : WalLay} {i : Ino} {s : Nat} (h : s ∈ segRzOf lay i) :
    ∃ g ∈ lay.segs, g.ino = i ∧ s ∈ g.om.rz := by
  unfold segRzOf at h
  cases hf : lay.segs.find? (fun g => decide (g.ino = i)) with
  | none => simp [hf] at h
  | some g =>
    simp only [hf, Option.map_some, Option.getD_some] at h
    exact ⟨g, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

/-- `W1G` knowing fewer resize stamps is weaker. -/
theorem W1G.mono_rz {C : WalCodec} {js : List Ino} {img : Ino → List w8}
    {bsOf : Ino → Option (List ByteG)} {rzOf rzOf' : Ino → List Nat}
    (h : W1G C js img bsOf rzOf) (hrz : ∀ i, ∀ s ∈ rzOf' i, s ∈ rzOf i) :
    W1G C js img bsOf rzOf' := fun k p hp i bs hi hbs hsz =>
  AsOfW.congr (fun _ _ _ => rfl) (fun _ _ _ => rfl) (hrz i) (h k p hp i bs hi hbs hsz)

/-- `W1G` with the stamps the layout knows, weakened to none. -/
theorem W1G.weak_rz {C : WalCodec} {js : List Ino} {img : Ino → List w8}
    {bsOf : Ino → Option (List ByteG)} {rzOf : Ino → List Nat}
    (h : W1G C js img bsOf rzOf) : W1G C js img bsOf (fun _ => []) :=
  h.mono_rz (fun _ _ hs => by cases hs)

/-- A prefix of the segments knows only stamps the whole knows. -/
theorem segRzOf_prefix {lay lay' : WalLay} (h : lay.segs <+: lay'.segs) (i : Ino) :
    ∀ s ∈ segRzOf lay i, s ∈ segRzOf lay' i := by
  obtain ⟨r, hr⟩ := h
  intro s hs
  unfold segRzOf at hs ⊢
  rw [← hr, List.find?_append]
  cases hf : lay.segs.find? (fun g => decide (g.ino = i)) with
  | none => simp [hf] at hs
  | some g => simpa [hf] using hs

/-- The image of a file a crash left (empty if none). -/
def imgOf (fo : Option Fs.OsFile) : List w8 := (fo.map Fs.OsFile.contents).getD []

theorem segBytesOf_some {lay : WalLay} {i : Ino} {bs : List ByteG} (h : segBytesOf lay i = some bs) :
    ∃ g ∈ lay.segs, g.ino = i ∧ segBytesX g = bs := by
  unfold segBytesOf at h
  cases hf : lay.segs.find? (fun g => decide (g.ino = i)) with
  | none => simp [hf] at h
  | some g =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨g, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

/-- `segBytesOf_some` for a layout whose segments are exact (`om.hi ≤ |bs|`). -/
theorem segBytesOf_some_ex {lay : WalLay} {i : Ino} {bs : List ByteG}
    (hex : ∀ g ∈ lay.segs, g.om.hi ≤ g.bs.length) (h : segBytesOf lay i = some bs) :
    ∃ g ∈ lay.segs, g.ino = i ∧ g.bs = bs := by
  obtain ⟨g, hg, hi, he⟩ := segBytesOf_some h
  exact ⟨g, hg, hi, by rw [← he, segBytesX_of_hi (hex g hg)]⟩

theorem contents_getD (f : Fs.OsFile) (b : Nat) (hb : b < f.size) : f.contents.getD b 0 = f.cache b := by
  simp [Fs.OsFile.contents, List.getD_eq_getElem?_getD, hb]

/-- **W1 over the state gives W1 over the ghost candidates** of a WAL directory's segments: the
crashed tree is the state's, each segment's image no larger than its bytes the invariant knows, its
candidates in the old state the ghost ones. -/
theorem w1G_of_W1 (C : WalCodec) (st st' : Fs.OsState) (m' : Tree) (lay : WalLay)
    (rzOf : Ino → List Nat) (hw1 : W1 C st st') (htree : st'.fs.treeDur = m')
    (hsegs : ∀ g ∈ lay.segs,
      ∃ f, st.fs.files !! g.ino = some f ∧
        (∀ b (y : ByteG), (segBytesX g)[b]? = some y → f.cand b = y.2) ∧
        ∀ s ∈ rzOf g.ino, s ∈ f.rzs) :
    W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (st'.fs.files !! i)) (segBytesOf lay) rzOf := by
  intro k p hp i bs hi hbs hsz
  obtain ⟨g, hg, rfl, rfl⟩ := segBytesOf_some hbs
  obtain ⟨f, hf, hcand, hrz⟩ := hsegs g hg
  obtain ⟨x, hx, hb⟩ := acceptsFiles_bound C _ _ p hp
  rw [List.getElem?_map, hi] at hx
  simp only [Option.map_some, Option.some.injEq] at hx
  subst hx
  cases hm : m' !! lay.j with
  | none =>
    have : walInos (entsOf m' lay.j) = [] := by
      simp [entsOf, hm, walInos, walNames, GMap.toList]
    rw [this] at hi; simp at hi
  | some d =>
    have hent : entsOf m' lay.j = d := by simp [entsOf, hm]
    rw [hent] at hp hi
    cases hf' : st'.fs.files !! g.ino with
    | none =>
      simp only [hf', imgOf, Option.map_none, Option.getD_none, List.length_nil] at hb
      unfold frameCore at hb; omega
    | some f' =>
      have hfun : (fun i => imgOf (st'.fs.files !! i)) = contentsOf st'.fs.files := rfl
      have h1 := hw1 lay.j d (by rw [htree]; exact hm) k p (by rw [← hfun]; exact hp)
        g.ino f f' hi hf hf'
      have hfs : ((((walInos d).drop k).map (contentsOf st'.fs.files)).getD p.1 []) =
          imgOf (st'.fs.files !! g.ino) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hi]; rfl
      rw [hfs] at h1
      simp only [hf', imgOf, Option.map_some, Option.getD_some] at hb h1 ⊢
      have hlen : f'.contents.length = f'.size := by simp [Fs.OsFile.contents]
      have hbyte : ∀ b, p.2 ≤ b → b < p.2 + frameCore f'.contents p.2 →
          f'.contents.getD b 0 = f'.cache b ∧ ((segBytesX g).getD b (0, [])).2 = f.cand b := by
        intro b h1 h2
        have hbs : b < f'.size := by omega
        refine ⟨contents_getD f' b hbs, ?_⟩
        have hbl : b < (segBytesX g).length := by
          simp only [hf', imgOf, Option.map_some, Option.getD_some] at hsz; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]
        exact (hcand b _ (List.getElem?_eq_getElem hbl)).symm
      exact AsOfW.congr (fun b hb1 hb2 => (hbyte b hb1 hb2).2.symm)
        (fun b hb1 hb2 => (hbyte b hb1 hb2).1.symm) hrz h1

/-! ## The crash condition -/

/-- **What a crash of the WAL `d` with the layout `lay` must leave** (plan §2.2), the crashed tree
being `m'` and the files `fo`: the WAL directory absent, only if `d` is not `named`; or present, its
`.wal` files the named segments from the `q`-th on, and an image `I` of the history
(`walImg d.H d.m I`, at least the last segment's start, so the cuts stay) such that, the WAL being
`d` with history `I` (`d'`): each kept segment but the last holds exactly `d'`'s frames of it; the
last starts with `d'`'s frames of it, and the reader stops after them (at the chain's CRC after
`d'`'s records); the first kept segment starts at most at `min d.pur |I|`. (So a fresh reader from
the first kept file reads `d'`'s records after the purged ones: `crashTo_decode`.) -/
def CrashTo (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (m' : Tree)
    (fo : Ino → Option Fs.OsFile) : Prop :=
  (d.named = false ∧ m'.entry lay.jr lay.nm = none) ∨
  ∃ (q : Nat) (I : List (WalOpG WalEnt)),
    m'.entry lay.jr lay.nm = some (.dir lay.j) ∧ q < lay.segs.length ∧
    walInos (entsOf m' lay.j) = (lay.segs.drop q).map (·.ino) ∧
    walImg d.H d.m I ∧ segStart lay.cuts lay.cuts.length ≤ I.length ∧
    segStart lay.cuts (lay.first + q) ≤ min d.pur I.length ∧
    (∀ k (g : SegG), (lay.segs.drop q)[k]? = some g → lay.first + q + k < lay.cuts.length →
      imgOf (fo g.ino) = segStream C Mr { d with H := I } lay.cuts (lay.first + q + k)) ∧
    (∀ g, lay.segs.getLast? = some g →
      let S := segStream C Mr { d with H := I } lay.cuts lay.cuts.length
      S <+: imgOf (fo g.ino) ∧ ∀ r len c', decStep C true (imgOf (fo g.ino)) S.length
        (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM { d with H := I }) lay.cuts)))
          ≠ .accept r len c')

/-- **The crash condition** (plan §2.2): for every crashed tree the WAL's claims allow
(`RegionCrashed` of the claims `cl` with the commit bound `n`) and every image of each segment its
halves allow (`FileCrashedR`), there if the crashed tree lists it among the WAL directory's `.wal`
files (a weaker premise than its being named anywhere: so the condition carries across a change of
any other name, `Create`'s drop of `nm.tmp`), on which W1 holds (`W1G`, with the resize stamps the layout's `OsMeta` halves know: `segRzOf`),
`CrashTo`. -/
def CrashOk (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (cl : List Claim)
    (n : Nat) : Prop :=
  ∀ (m' : Tree) (fo : Ino → Option Fs.OsFile), RegionCrashed cl n m' →
    (∀ g ∈ lay.segs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino)) →
    (∀ g ∈ lay.segs, g.ino ∈ walInos (entsOf m' lay.j) → (fo g.ino).isSome) →
    W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay) (segRzOf lay) →
    CrashTo C Mr d lay m' fo

end abs

end WalFs
end EtcdGrove
end Perennial

end
