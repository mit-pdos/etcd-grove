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
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncSuffix
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk
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

/-- A byte of the last segment: its intended value `x`, the value under it `y`, whether it is
written (`w`) and synced (`s`): durable `x` if synced; else, if written, `x` in the page cache with
the candidates `y` (as of the sync) and `x` (stamped by its write); else durable `y`. -/
def ByteOk (x y : w8) (w s : Bool) (g : ByteG) : Prop :=
  if s then g = durB x
  else if w then g.1 = x ∧ ∃ n, 0 < n ∧ g.2 = [(y, 0), (x, n)]
  else g = durB y

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
  index before `b`. -/
  nameBound : ∀ k (g : SegG), lay.segs[k]? = some g → ∃ sq ix : Nat,
    g.name = walFileName sq ix ∧ (0 < lay.first + k → walLastIdx ((histM d).take (segStart lay.cuts (lay.first + k))) + 1 ≤ ix)
  /-- What `Open` reads from, and what was purged. -/
  cut : d.cut = segStart lay.cuts lay.first ∧ (0 < lay.first → d.cut ≤ d.pur)
  /-- Each segment's `OsMeta` half: its size is its bytes', no sync cut. -/
  metas : ∀ g ∈ lay.segs, g.om.size = g.bs.length ∧ g.om.cut = none
  /-- Every named segment but the last holds exactly its frames, durable. -/
  intact : ∀ k (g : SegG), k + 1 < lay.segs.length → lay.segs[k]? = some g →
    g.bs = (segStream C Mr d lay.cuts (lay.first + k)).map durB
  /-- The last segment: its stream up to `wr`, `old` past it, durable below `so`. -/
  last : ∀ g, lay.segs.getLast? = some g →
    let S := segStream C Mr d lay.cuts lay.cuts.length
    lay.so ≤ lay.wr ∧ lay.wr ≤ S.length ∧ g.bs.length = lay.old.length ∧ lay.wr ≤ lay.old.length ∧
    (∀ b (x : ByteG), g.bs[b]? = some x →
      ByteOk (S.getD b 0) (lay.old.getD b 0) (decide (b < lay.wr)) (decide (b < lay.so)) x) ∧
    lay.z0 ≤ lay.wr ∧ (S.take lay.z0 = lay.old.take lay.z0) ∧
    (lay.z0 < S.length → ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)
  /-- The synced operations' frames, in the last segment, are synced. -/
  synced : d.m ≤ d.H.length ∧
    (recFrames C ((segRecs C Mr { d with H := d.H.take d.m } lay.cuts).getD lay.cuts.length [])).length
      ≤ lay.so
  /-- Nothing appended this generation: the reader of the last file stops after its frames (at the
  chain's CRC after all the WAL's records). -/
  tailStop : lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length → ∀ r len c',
    decStep C true lay.old lay.z0
      (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))) ≠ .accept r len c'

/-! ## W1 over the ghost candidates -/

/-- The ghost form of `AsOfOne`: the image bytes `img` of `[o, o + len)` against the bytes `bs`'
candidates. -/
def AsOfOneG (bs : List ByteG) (img : List w8) (o len : Nat) : Prop :=
  (∀ b, o ≤ b → b < o + len → img.getD b 0 = valAt (bs.getD b (0, [])).2 0) ∨
  ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
    img.getD b 0 = valAt (bs.getD b (0, [])).2 n ∧ ∃ p ∈ (bs.getD b (0, [])).2, 0 < p.2 ∧ p.2 ≤ n

/-- **W1 over a crashed WAL directory**, from the ghost candidates: its `.wal` files `js` (in name
order), their images `img`, read from any of them on with a fresh reader; a file that is a segment
the invariant knows (`bsOf i = some bs`) has every accepted frame's core as of one change of `bs`'
candidates. -/
def W1G (C : WalCodec) (js : List Ino) (img : Ino → List w8) (bsOf : Ino → Option (List ByteG)) :
    Prop :=
  ∀ k, ∀ p ∈ acceptsFiles C ((js.drop k).map img) 0#32, ∀ i bs, (js.drop k)[p.1]? = some i →
    bsOf i = some bs → AsOfOneG bs (img i) p.2 (frameCore (img i) p.2)

/-- The ghost bytes of the segment of inode `i`, if it is one of the layout's. -/
def segBytesOf (lay : WalLay) (i : Ino) : Option (List ByteG) :=
  (lay.segs.find? (fun g => decide (g.ino = i))).map (·.bs)

/-! ## The crash condition -/

/-- The image of a file a crash left (empty if none). -/
def imgOf (fo : Option Fs.OsFile) : List w8 := (fo.map Fs.OsFile.contents).getD []

/-- **What a crash of the WAL `d` with the layout `lay` must leave** (plan §2.2), the crashed tree
being `m'` and the files `fo`: the WAL directory absent, only if `d` is not `named`; or present, its
`.wal` files a suffix of the named segments (from the `q`-th on), and a fresh reader over them reads
the records of the WAL with segments `Ss'` after those of the purged segments, where `Ss'` are the
segments of an image `I` of the history (`walImg d.H d.m I`, `Ss'.flatten = I`) and the first file
read starts at a position at most `min d.pur |I|`. -/
def CrashTo (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (m' : Tree)
    (fo : Ino → Option Fs.OsFile) : Prop :=
  (d.named = false ∧ m'.entry lay.jr lay.nm = none) ∨
  ∃ (q : Nat) (I : List (WalOpG WalEnt)) (Ss' : List WalHist),
    m'.entry lay.jr lay.nm = some (.dir lay.j) ∧ q < lay.segs.length ∧
    walInos (entsOf m' lay.j) = (lay.segs.drop q).map (·.ino) ∧
    walImg d.H d.m I ∧ Ss'.flatten = I.map WalOpG.toM ∧ Ss'.length = lay.first + lay.segs.length ∧
    segStart lay.cuts (lay.first + q) ≤ min d.pur I.length ∧
    (walDecodeFiles C ((lay.segs.drop q).map (fun g => imgOf (fo g.ino))) 0#32).recs =
      (recsOfSegs C Mr d.metadata Ss').drop
        (recsOfSegs C Mr d.metadata (Ss'.take (lay.first + q))).length

/-- **The crash condition** (plan §2.2): for every crashed tree the WAL's claims allow
(`RegionCrashed` of the claims `cl` with the commit bound `n`) and every image of each segment its
halves allow (`FileCrashedR`) on which W1 holds (`W1G`), `CrashTo`. -/
def CrashOk (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (cl : List Claim)
    (n : Nat) : Prop :=
  ∀ (m' : Tree) (fo : Ino → Option Fs.OsFile), RegionCrashed cl n m' →
    (∀ g ∈ lay.segs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino)) →
    W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay) →
    CrashTo C Mr d lay m' fo

/-- **The crash condition at a generation's start**: nothing logged on the WAL's names (each claim's
history empty, `RegionCrashed` then keeps them as they are), every byte of every segment durable and
nothing appended (`wr = so = z0`, the last segment's stream ending at `z0`), so every crash leaves the
files as they are; the static relation then gives the crash condition (the reader reads the WAL's
records, then stops). This is what the next generation's invariant needs (`walInv_crash`). -/
theorem walAbs_crashOk_start (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (d : WalDur)
    (lay : WalLay) (cl : List Claim) (n : Nat) (ents : Ents)
    (habs : WalAbsD C Mr d lay ents)
    (hfit : RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)))
    (hlog : ∀ c ∈ cl, c.2.2.ents = [])
    (hj : (lay.j, NameSet.except [], ⟨ents, [], ents⟩) ∈ cl)
    (hr : ∃ N, (lay.jr, N, ⟨{[lay.nm := Node.dir lay.j]}, [], {[lay.nm := Node.dir lay.j]}⟩) ∈ cl ∧
      ∀ b, N.Mem b ↔ b = lay.nm)
    (hdur : lay.wr = lay.so ∧ lay.wr = lay.z0 ∧
      lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hlast : ∀ g, lay.segs.getLast? = some g → g.bs = lay.old.map durB) :
    CrashOk C Mr d lay cl n := by
  sorry

end abs

end WalFs
end EtcdGrove
end Perennial

end
