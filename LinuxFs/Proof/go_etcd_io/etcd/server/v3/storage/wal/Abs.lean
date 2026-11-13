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
  metas : ∀ g ∈ lay.segs, g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
    g.om.hi = g.bs.length
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

/-- The image of a file a crash left (empty if none). -/
def imgOf (fo : Option Fs.OsFile) : List w8 := (fo.map Fs.OsFile.contents).getD []

theorem segBytesOf_some {lay : WalLay} {i : Ino} {bs : List ByteG} (h : segBytesOf lay i = some bs) :
    ∃ g ∈ lay.segs, g.ino = i ∧ g.bs = bs := by
  unfold segBytesOf at h
  cases hf : lay.segs.find? (fun g => decide (g.ino = i)) with
  | none => simp [hf] at h
  | some g =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨g, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem contents_getD (f : Fs.OsFile) (b : Nat) (hb : b < f.size) : f.contents.getD b 0 = f.cache b := by
  simp [Fs.OsFile.contents, List.getD_eq_getElem?_getD, hb]

/-- **W1 over the state gives W1 over the ghost candidates** of a WAL directory's segments: the
crashed tree is the state's, each segment's image no larger than its bytes the invariant knows, its
candidates in the old state the ghost ones. -/
theorem w1G_of_W1 (C : WalCodec) (st st' : Fs.OsState) (m' : Tree) (lay : WalLay)
    (hw1 : W1 C st st') (htree : st'.fs.treeDur = m')
    (hsegs : ∀ g ∈ lay.segs, (∀ f', st'.fs.files !! g.ino = some f' → f'.size ≤ g.bs.length) ∧
      ∃ f, st.fs.files !! g.ino = some f ∧ ∀ b (y : ByteG), g.bs[b]? = some y → f.cand b = y.2) :
    W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (st'.fs.files !! i)) (segBytesOf lay) := by
  intro k p hp i bs hi hbs
  obtain ⟨g, hg, rfl, rfl⟩ := segBytesOf_some hbs
  obtain ⟨hsz, f, hf, hcand⟩ := hsegs g hg
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
          f'.contents.getD b 0 = f'.cache b ∧ (g.bs.getD b (0, [])).2 = f.cand b := by
        intro b h1 h2
        have hbs : b < f'.size := by omega
        refine ⟨contents_getD f' b hbs, ?_⟩
        have hbl : b < g.bs.length := Nat.lt_of_lt_of_le hbs (hsz f' hf')
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]
        exact (hcand b _ (List.getElem?_eq_getElem hbl)).symm
      rcases h1 with h1 | ⟨n, hn, h1⟩
      · left; intro b hb1 hb2
        rw [(hbyte b hb1 hb2).1, (hbyte b hb1 hb2).2]; exact h1 b hb1 hb2
      · right; refine ⟨n, hn, fun b hb1 hb2 => ?_⟩
        rw [(hbyte b hb1 hb2).1, (hbyte b hb1 hb2).2]; exact h1 b hb1 hb2

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
halves allow (`FileCrashedR`), there if the crashed tree names it, on which W1 holds (`W1G`),
`CrashTo`. -/
def CrashOk (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (cl : List Claim)
    (n : Nat) : Prop :=
  ∀ (m' : Tree) (fo : Ino → Option Fs.OsFile), RegionCrashed cl n m' →
    (∀ g ∈ lay.segs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino)) →
    (∀ g ∈ lay.segs, Named m' g.ino → (fo g.ino).isSome) →
    W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay) →
    CrashTo C Mr d lay m' fo

end abs

end WalFs
end EtcdGrove
end Perennial

end
