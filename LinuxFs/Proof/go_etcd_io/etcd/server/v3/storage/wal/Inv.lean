/- Lean-first (no Rocq counterpart).

# The WAL invariant over `fsExt` (`notes/wal-fsext-plan.md`, §2.1-§2.2; W1)

`walInv C Mr R jr r`: the invariant of the WAL area `r` (the directory of inode `jr` under the
roots `R`), in the tree's shared mode (`notes/wal-fsext-i2-design.md`). It holds:

* the real WAL state `s` and the ghost state's authorities (`walGhost s`, `Ghost.lean`);
* each WAL's layout (`WalLay`, `Abs.lean`), the halves of the WAL's name claims (`osNames`, I2: of
  each WAL directory's names, and of the area's names the WALs sit at) with the commit lower bound
  `n` of the generation's tree (`osCommitLb n`, I1), each named segment's halves (`segRes`);
* the static relation (`WalAbsD`) and the crash condition (`CrashOk`) of every WAL;
* that a directory of the area with no WAL has none after any crash its claims allow (`AbsentOk`),
  and that a durable directory (`dirDurable`) resolves after any crash (`DirsOk`);
* `Create`'s framed part (`WalsCreateOk`, W4): a claim of the area holds every WAL name; and the
  creating map's authority (`walCreatingAuth`, `CreatingOk`): each `Create` in progress's area claim,
  among the invariant's (the program's `walCreating` token names it); and that a WAL name with no WAL
  is absent, now and after every crash (`AbsentNone`), and the durable directories resolve through no
  name of the area a WAL function changes (`DirsAvoid`).

W2 (`Cut.lean`): the WAL directory's claim leaves out the pipeline's names (`WalDirClaim`, the
`N.tmp` claims are the pipeline's) and is coherent; the crash condition may carry the layout before
a cut's rename not yet made durable (`CrashOkW`).

W6 (`Save`, the tail's writes): a segment may have a write in flight (`SegFl`: its `pwTok` and
the bytes around it in place of the segment's halves, as `cfInv`'s `invRes`,
LinuxFs/Proof/os/CrashFile.lean), the layout then holding the segment as the write announced it
(`SegFl.Ok`: the token's `OsMeta`, the bytes with the write's candidates added), so that the static
relation and the crash condition are unchanged; and each WAL with an open handle shares with it
its tail (`walTailsRes`: the history, metadata, cuts, write position and tail inode, half each;
past the frames found at the generation's start the tail is zeros, F-Z; the larger of the synced
offset and that end is a record boundary, `TailBound`).

**Not yet here**: `Create`'s `dir.tmp`; a write past the tail's size (`SegFl.Ok`'s first clause:
the writes stay inside the preallocated file).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Cut
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpClaim
public import GooseLang.Ext.Fs.TreeShared
public import LinuxFs.Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The WAL invariant's namespace. -/
def walN : Namespace := nroot .@ "walfs"

section pure
variable [GooseExts]

/-- The name of the WAL directory `dir` in the area `r` (`dir = r/nm`). -/
def InArea (r dir nm : GoString) : Prop := walNameOk nm ∧ dir = r ++ go!"/" ++ nm

/-- **A directory of the area with no WAL has none after a crash**: its name in the area holds no
directory with a `.wal` file, in every tree the claims allow. -/
def AbsentOk (s : AbsDiskState) (jr : Ino) (cl : List Claim) (n : Nat) : Prop :=
  ∀ dir nm, InArea s.area dir nm → s.wal !! dir = none → ∀ m', RegionCrashed cl n m' →
    ∀ J, m'.entry jr nm = some (.dir J) → walInos (entsOf m' J) = []

/-- **A durable directory resolves after a crash.** -/
def DirsOk (R : Roots) (s : AbsDiskState) (cl : List Claim) (n : Nat) : Prop :=
  ∀ dd, s.dirs !! dd = some () → ∀ m', RegionCrashed cl n m' →
    ∃ J, lookupH R (m', []) dd = some (.dir J)

/-- All the named segments of the layouts. -/
def segsAll (Ls : GMap GoString WalLay) : List SegG := (toList Ls).flatMap (fun kv => kv.2.segs)

/-- **What the invariant says of the WALs** (pure): each WAL of `s` has a layout, its directory at
its name in the area, its directory's claim among `cl` (`WalDirClaim`) with the static relation
over the directory's names, and its crash condition (`CrashOkW`). -/
def WalsOk (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) : Prop :=
  (∀ dir d, s.wal !! dir = some d → ∃ lay nm hj, Ls !! dir = some lay ∧ InArea s.area dir nm ∧
    lay.jr = jr ∧ lay.nm = nm ∧ WalDirClaim lay.j hj cl ∧
    WalAbsD C Mr d lay hj.cur ∧ CrashOkW C Mr d lay cl n) ∧
  (∀ dir, s.wal !! dir = none → Ls !! dir = none) ∧
  ((segsAll Ls).map (·.ino)).Nodup ∧ (∀ g ∈ segsAll Ls, g.om.cut = none) ∧
  AbsentOk s jr cl n ∧ DirsOk R s cl n

/-- **A change in flight on a segment** (W6; I3b): its token `t` and change number `n`, and the
segment's `OsMeta` `m` and bytes `bs` before it; a write (`rz = none`, `wp_osPWriteStart`'s: its
offset `off` and data), or a resize to `tg` (`rz = some (tr, tg)`, `wp_osResizeStart`'s: `ftruncate`
if `tr`, else `fallocate`'s growth; `off` and `data` unused, `[]` by convention). -/
structure SegFl where
  t : Nat
  off : Nat
  data : List w8
  n : Nat
  m : OsMeta
  bs : List ByteG
  rz : Option (Bool × Nat) := none

instance SegFl.countable : Pos.Countable SegFl :=
  Pos.Countable.ofInjective
    (fun fl => Pos.Countable.encode (fl.t, fl.off, fl.data, fl.n, fl.m, fl.bs, fl.rz))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h; subst h1 h2 h3 h4 h5 h6 h7; rfl)

/-- **The segment `g` as the write in flight `fl` announced it**: the write inside the segment
(the WAL writes its tail inside the preallocated file), not empty; `g`'s `OsMeta` the token's
(`cfMeta`), its bytes `fl.bs` with the data's candidates added to the written range (`pwAnn`); and
the write past the segment's first byte (`0 < fl.off`: the tail's writes come after its header
records, synced when the segment was named), so that the invariant keeps half of byte 0 of every
segment, idle or written to: a file the program holds byte 0 of wholly (a segment it creates) is
none of them (`laysResF_ino_ne`, `InvInos.lean`; the inode-clash gap of `Create`'s and `cut`'s
commits). -/
def SegFl.Ok (fl : SegFl) (g : SegG) : Prop :=
  fl.off + fl.data.length ≤ fl.m.size ∧ fl.data ≠ [] ∧ fl.bs.length = fl.m.size ∧
  fl.m.cut = none ∧ g.om = cfMeta fl.m fl.off fl.data.length ∧
  g.bs = fl.bs.take (cfLo fl.m fl.off) ++
    pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length) ++
    fl.bs.drop (cfHi fl.m fl.off fl.data.length) ∧ 0 < fl.off

/-- **The segment `g` as the resize in flight `fl` to `tg` (`ftruncate` if `tr`, else `fallocate`'s
growth) announced it** (I3b; `wp_osResizeStart`): `g`'s `OsMeta` the token's (`TokInfo.meta`: `m` with
`[min size tg, rsHi tr size tg)` announced, the target `tg`), its bytes `fl.bs` with zero added as a
candidate of each byte cut off (`rsAnn`; none if it grows the file); the resize keeps byte 0
(`0 < min size tg`), so that the invariant keeps half of it, as `SegFl.Ok`'s `0 < fl.off`. -/
def SegFl.OkR (fl : SegFl) (tr : Bool) (tg : Nat) (g : SegG) : Prop :=
  fl.bs.length = fl.m.size ∧ fl.m.cut = none ∧
  g.om = fl.m.announce (min fl.m.size tg) (rsHi tr fl.m.size tg) tg ∧
  g.bs = fl.bs.take (min fl.m.size tg) ++ rsAnn fl.n (fl.bs.drop (min fl.m.size tg)) ∧
  0 < min fl.m.size tg

/-- **What the program and the invariant share of an open handle's tail** (half each): the history,
the metadata, the cuts, the write position, the tail's inode, the write in flight on it if any. -/
abbrev TailG := List (WalOpG WalEnt) × List w8 × List Nat × Nat × Ino × Option SegFl

/-- The tail of the layout `lay` of the WAL `d` as `TailG`. -/
def tailG (d : WalDur) (lay : WalLay) (i : Ino) (fl : Option SegFl) : TailG :=
  (d.H, d.metadata, lay.cuts, lay.wr, i, fl)

/-- **F-Z**: past the frames found at the generation's start, the tail is zeros (`ReadAll`'s
`ZeroToEnd` and fdatasync; a segment this generation created is zeros past its headers). -/
def TailZeros (lay : WalLay) : Prop :=
  ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0

/-- **The tail's record boundary** (W6): the larger of the synced offset and the end of the frames
found at the generation's start ends a record of the last segment's intended records. `z0` ends the
frames `ReadAll` found (0 for a segment this generation created); a tail's fdatasync comes after the
encoder's flush, at the end of the records encoded (`sync`'s commit re-establishes it from the
handle's `pend = []`; `cut`'s and `ReadAll`'s syncs end at a boundary too). The crash of an append
rests on it (`tail_decode`'s `hEb`, `TailCrashPure.lean`): a frame the reader accepts at a boundary
is the intended one. It depends on the WAL only through its history and metadata. -/
def TailBound (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) : Prop :=
  ∃ jE, jE ≤ ((segRecs C Mr d lay.cuts).getD lay.cuts.length []).length ∧
    (recFrames C (((segRecs C Mr d lay.cuts).getD lay.cuts.length []).take jE)).length =
      max lay.so lay.z0

theorem TailBound.congr {C : WalCodec} {Mr : WalMarshal} {d d' : WalDur} {lay : WalLay}
    (hH : d'.H = d.H) (hmd : d'.metadata = d.metadata) (h : TailBound C Mr d lay) :
    TailBound C Mr d' lay := by
  have e : segRecs C Mr d' lay.cuts = segRecs C Mr d lay.cuts := by
    simp [segRecs, histM, hH, hmd]
  unfold TailBound; rw [e]; exact h

/-- **`Create`'s part of the invariant** (W4, framed apart from `WalsOk`): a claim of the area
directory among `cl` holds every WAL name, so that a claim the program holds on a WAL name is known
to be one the invariant has the other half of (`NamesCoh.disj`), whose crashes it reasons about. -/
def WalsCreateOk (jr : Ino) (cl : List Claim) : Prop :=
  ∀ nm, walNameOk nm → ∃ N h, (jr, N, h) ∈ cl ∧ N.Mem nm

/-- The claim `c` occurs once in `cl`. -/
def ClaimOnce (c : Claim) (cl : List Claim) : Prop :=
  ∃ l1 l2, cl = l1 ++ c :: l2 ∧ c ∉ l1 ∧ c ∉ l2

/-- **What the creating map records of the new WAL's directory `J`** (the `walCreating` token's;
for the commit's `DirKeysOk`, W2 log, "the directory-claim map"): `J` is not the area directory, no
claim of `J` among `cl` holds a `.wal` name (the program holds `J`'s claim on all of them: the
shared invariant's `NamesCoh.disj` where the token is made; so `J` is no keyed WAL's directory,
whose claim holds them), no other entry's directory is `J`, and the area claim leaves out a `.wal`
name (it is none of a WAL directory's claims, `WalDirClaimOf`; `.only [nm, nm.tmp]`). -/
def CreatingNew (jr : Ino) (cl : List Claim) (CR : GMap GoString (NameSet × NamesH × Ino))
    (dir : GoString) (N : NameSet) (J : Ino) : Prop :=
  J ≠ jr ∧ (∀ c ∈ cl, c.1 = J → ∀ b, walNameP b = true → ¬ c.2.1.Mem b) ∧
  (∀ dir' x, dir' ≠ dir → CR !! dir' = some x → x.2.2 ≠ J) ∧
  ∃ b, walNameP b = true ∧ ¬ N.Mem b

/-- **The WALs being created are renamed in claims the invariant holds** (W4, framed): each entry
`dir ↦ (N, h, J)` of the creating map is a claim `(jr, N, h)` of the area directory among `cl`,
coherent, and no other claim of `jr` among `cl` holds one of its names (what the file system's
shared invariant says of claims, `NamesCoh.disj`, recorded where the token is made: the rename's
commit, inside an `os` call's update, cannot open that invariant); the claim occurs once in `cl`
(the commit replaces that one occurrence) and is no other entry's (the commit deletes only its own
entry). A new entry's claim is split off the area claim where its token is made, so it is in no
claim of `cl` before. -/
def CreatingOk (jr : Ino) (cl : List Claim) (CR : GMap GoString (NameSet × NamesH × Ino)) : Prop :=
  ∀ dir N h J, CR !! dir = some (N, h, J) → (jr, N, h) ∈ cl ∧ ClaimCoh h jr N ∧
    (∀ c ∈ cl, c ≠ (jr, N, h) → c.1 = jr → ∀ b, N.Mem b → ¬ c.2.1.Mem b) ∧
    ClaimOnce (jr, N, h) cl ∧ (∀ dir' J', dir' ≠ dir → CR !! dir' ≠ some (N, h, J')) ∧
    CreatingNew jr cl CR dir N J

/-- **A WAL name of the area with no WAL is absent** (W4, framed; strong absence, against `AbsentOk`'s
"no `.wal` file"): in every claim of the area directory holding it, now, and after every crash the
claims allow. `Create` relies on it twice: `renameWAL`'s `os.RemoveAll(dir)` finds nothing to remove,
and a crash dropping the rename that committed a fresh WAL leaves its name absent (`CrashTo`'s left
disjunct). Established at the start from the boot tree (`WalsStart`: the crash leaves a WAL-less name
absent, `walCrash_pure`). -/
def AbsentNone (s : AbsDiskState) (jr : Ino) (cl : List Claim) (n : Nat) : Prop :=
  ∀ dir nm, InArea s.area dir nm → s.wal !! dir = none →
    (∀ N h, (jr, N, h) ∈ cl → N.Mem nm → h.cur !! nm = none) ∧
    ∀ m', RegionCrashed cl n m' → m'.entry jr nm = none

/-- **The WAL directories' claim keys, and no cut pending** (framed; W2 log, "the directory-claim
map"). Each key `dir ↦ (j, X)` (`walDirKey`, persistent; an open handle holds the program's half of
that claim): the WAL in `dir` has a layout of directory `j`, not the area's; the claim `(j, .except
X, hj)` (`X` holding no `.wal` name) occurs once among the claims, coherent, and no other claim of
`j` holds a `.wal` name (the shared invariant's `NamesCoh.disj`, recorded where the key is made: an
update's opening, inside an `os` call's, cannot open that invariant). And every WAL but the one whose
cut's rename is pending (`c`, `walCutAuth`; the lock token holds `none`) has no alternative layout
(`CrashOkA … none`, i.e. `CrashOk`): a cut's rename needs it of its WAL. -/
def DirKeysOk (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat)
    (K : GMap GoString (Ino × List GoString)) (c : Option GoString) : Prop :=
  (∀ dir j X, K !! dir = some (j, X) → ∃ lay hj, Ls !! dir = some lay ∧ lay.j = j ∧ j ≠ jr ∧
    (∀ b ∈ X, walNameP b = false) ∧ ClaimOnce (j, .except X, hj) cl ∧ ClaimCoh hj j (.except X) ∧
    ∀ c' ∈ cl, c' ≠ (j, .except X, hj) → c'.1 = j → ∀ b, walNameP b = true → ¬ c'.2.1.Mem b) ∧
  (∀ dir d lay, s.wal !! dir = some d → Ls !! dir = some lay → c ≠ some dir →
    CrashOkA C Mr d lay none cl n)

/-- A name of the area a WAL function may change: a WAL name, or `nm.<sfx>` of one (`Create`'s
`nm.tmp`, the cleanup's `nm.broken.<time>`). -/
def AreaSlot (b : GoString) : Prop :=
  ∃ nm, walNameOk nm ∧ (b = nm ∨ ∃ sfx, b = nm ++ go!"." ++ sfx)

/-- **The durable directories resolve through no slot of the area a WAL function changes** (W4,
framed with `AbsentNone`): their lookup in a tree depends on no entry of `jr` at an `AreaSlot` name, so
that `Create`'s rename (of `nm.tmp` onto `nm`) leaves `DirsOk` as it was. -/
def DirsAvoid (R : Roots) (jr : Ino) (s : AbsDiskState) : Prop :=
  ∀ dd, s.dirs !! dd = some () → ∀ m1 m2 : Tree,
    (∀ j b, ¬ (j = jr ∧ AreaSlot b) → m1.entry j b = m2.entry j b) →
    lookupH R (m1, []) dd = lookupH R (m2, []) dd

/-- **A WAL directory's segments are at their names** (`ents` its entries): each segment's name
is a `.wal` name, the entry at it the segment's file; every `.wal` entry is a file (W3/W5's gap 1:
`Open` reads the names, `searchIndex` picks a file by them). -/
def SegsNamed (segs : List SegG) (ents : Ents) : Prop :=
  (∀ g ∈ segs, walNameP g.name = true ∧ ents !! g.name = some (.file g.ino)) ∧
  ∀ b e, walNameP b = true → ents !! b = some e → ∃ i, e = .file i

/-- **`SegsNamed` after a crash**: the segments the crash kept named (their files among the
directory's `.wal` files) are at their names; every `.wal` entry is a file, and a segment's (a crash
names no other file at a `.wal` name: `cut`'s rename dropped by a crash leaves its new segment at
no `.wal` name, W2). -/
def SegsNamedC (segs : List SegG) (ents : Ents) : Prop :=
  (∀ g ∈ segs, walNameP g.name = true ∧ (g.ino ∈ walInos ents → ents !! g.name = some (.file g.ino))) ∧
  (∀ b e, walNameP b = true → ents !! b = some e → ∃ i, e = .file i) ∧
  ∀ i ∈ walInos ents, i ∈ segs.map (·.ino)

/-- **Every WAL's segments are at their names** (framed; W3/W5): now, in every claim of its
directory the invariant holds (`WalDirClaim`), and after every crash the claims allow. Established
at the start (`WalsStart`'s, from the crash: `walCrash_pure`); `cut`'s rename and `Create` must keep
it. -/
def WalsNamed (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) : Prop :=
  ∀ dir lay, Ls !! dir = some lay →
    (∀ hj, WalDirClaim lay.j hj cl → SegsNamed lay.segs hj.cur) ∧
    ∀ m', RegionCrashed cl n m' → SegsNamedC lay.segs (entsOf m' lay.j)

theorem SegsNamed.crash {segs : List SegG} {ents : Ents} (h : SegsNamed segs ents)
    (hsub : ∀ i ∈ walInos ents, i ∈ segs.map (·.ino)) : SegsNamedC segs ents :=
  ⟨fun g hg => ⟨(h.1 g hg).1, fun _ => (h.1 g hg).2⟩, h.2, hsub⟩

/-- `SegsNamed` of a claim's view of the directory, its names all but non-`.wal` ones. -/
theorem SegsNamed.restrict {segs : List SegG} {ents : Ents} {X : List GoString}
    (h : SegsNamed segs ents) (hX : ∀ b ∈ X, walNameP b = false) :
    SegsNamed segs (restrictN (.except X) ents) := by
  have hm : ∀ b, walNameP b = true → (NameSet.except X).Mem b := fun b hb hbX => by
    rw [hX b hbX] at hb; cases hb
  refine ⟨fun g hg => ?_, fun b e hb he => ?_⟩
  · obtain ⟨hw, he⟩ := h.1 g hg
    exact ⟨hw, by rw [restrictN_lookup _ _ _ (hm _ hw)]; exact he⟩
  · rw [restrictN_lookup _ _ _ (hm _ hb)] at he
    exact h.2 b e hb he

/-- The claim `c` is one of a WAL directory's, as `WalDirClaim` has them: on the directory of a
layout of `Ls`, on all names but non-`.wal` ones. -/
def WalDirClaimOf (Ls : GMap GoString WalLay) (c : Claim) : Prop :=
  ∃ dir lay, Ls !! dir = some lay ∧ c.1 = lay.j ∧
    ∃ X : List GoString, c.2.1 = .except X ∧ ∀ b ∈ X, walNameP b = false

noncomputable instance WalDirClaimOf.dec (Ls : GMap GoString WalLay) (c : Claim) :
    Decidable (WalDirClaimOf Ls c) := Classical.propDecidable _

/-- The claim `c` is parked (`walParked`): a WAL directory's, not taken out (its key, the directory's
inode and the claim's names, not in `D`: a step changing the claim's history keeps it out). -/
def ParkedClaim (Ls : GMap GoString WalLay) (D : List (Ino × NameSet)) (c : Claim) : Prop :=
  WalDirClaimOf Ls c ∧ (c.1, c.2.1) ∉ D

noncomputable instance ParkedClaim.dec (Ls : GMap GoString WalLay) (D : List (Ino × NameSet)) (c : Claim) :
    Decidable (ParkedClaim Ls D c) := Classical.propDecidable _

/-- **Every WAL's directory is at its name in the area** (W3/W5's gap 1, framed): in every claim of
the area directory `jr` holding a WAL's name, the entry there is the WAL's directory. `Open` reads
the WAL directory's path through it (from its own half of the area claim, `walAreaRes`). Established
at the start (`WalsStart`), kept by the tail's steps (no claim changes), a cut (the area claims
unchanged, the WAL directory not the area's) and `Create`'s commit (the rename puts the new WAL's
directory at its name; the others' names untouched). And **no WAL's directory is the area
directory** (`lay.j ≠ jr`; W4: `Create`'s merge of its claims back into the area claim after the
commit needs the merged claim to be no WAL directory's, `WalDirClaimOf`; established at the start from
the crash's old invariant, `CrashGood` keeping each layout's directory, kept by every step, which
keeps each layout's directory, and `Create`'s commit, `CreatingNew`'s `J ≠ jr`). -/
def WalsAt (jr : Ino) (Ls : GMap GoString WalLay) (cl : List Claim) : Prop :=
  ∀ dir lay, Ls !! dir = some lay → lay.j ≠ jr ∧ ∀ N h, (jr, N, h) ∈ cl → N.Mem lay.nm →
    h.cur !! lay.nm = some (.dir lay.j)

/-- No WAL's directory is the area directory (`WalsAt`'s first part). -/
theorem WalsAt.ne {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} (h : WalsAt jr Ls cl)
    {dir : GoString} {lay : WalLay} (hl : Ls !! dir = some lay) : lay.j ≠ jr := (h dir lay hl).1

/-- The area claims at a WAL's name (`WalsAt`'s second part). -/
theorem WalsAt.at {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} (h : WalsAt jr Ls cl)
    {dir : GoString} {lay : WalLay} (hl : Ls !! dir = some lay) {N : NameSet} {hh : NamesH}
    (hm : (jr, N, hh) ∈ cl) (hN : N.Mem lay.nm) : hh.cur !! lay.nm = some (.dir lay.j) :=
  (h dir lay hl).2 N hh hm hN

/-- A claim of the area directory is no WAL directory's claim (`WalsAt`'s first part). -/
theorem WalsAt.not_walDirClaimOf {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim}
    (h : WalsAt jr Ls cl) (c : Claim) (hc : c.1 = jr) : ¬ WalDirClaimOf Ls c := by
  rintro ⟨dir, lay, hl, hj, -⟩
  exact h.ne hl (hj ▸ hc)

/-- **`WalsAt` under a change of layouts and claims**: every new layout one of a key with the same
name and directory before, every new claim of the area one before. -/
theorem walsAt_congr {jr : Ino} {Ls Ls' : GMap GoString WalLay} {cl cl' : List Claim}
    (hL : ∀ dir lay', Ls' !! dir = some lay' →
      ∃ lay, Ls !! dir = some lay ∧ lay.nm = lay'.nm ∧ lay.j = lay'.j)
    (hc : ∀ N h, (jr, N, h) ∈ cl' → (jr, N, h) ∈ cl) (h : WalsAt jr Ls cl) : WalsAt jr Ls' cl' := by
  intro dir lay' hl'
  obtain ⟨lay, hl, hnm, hj⟩ := hL dir lay' hl'
  refine ⟨hj ▸ h.ne hl, fun N hh hm hN => ?_⟩
  rw [← hnm, ← hj]
  exact h.at hl (hc N hh hm) (hnm ▸ hN)

/-- The layout at a key replaced by one of the same name and directory (the tail's steps, a cut). -/
theorem walsAt_insert {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} {dir : GoString}
    {lay lay' : WalLay} (hl : Ls !! dir = some lay) (hnm : lay'.nm = lay.nm) (hj : lay'.j = lay.j)
    (h : WalsAt jr Ls cl) : WalsAt jr (<[dir := lay']> Ls) cl := by
  refine walsAt_congr (fun dir' l hl' => ?_) (fun _ _ hm => hm) h
  by_cases hd : dir' = dir
  · subst hd
    rw [GMap.lookup_insert_eq] at hl'
    cases hl'
    exact ⟨lay, hl, hnm.symm, hj.symm⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'
    exact ⟨l, hl', rfl, rfl⟩

/-- A claim of another directory than the area's replaced (a cut's sync logs the WAL directory's). -/
theorem walsAt_mid {jr : Ino} {Ls : GMap GoString WalLay} {l1 l2 : List Claim} {c c' : Claim}
    (hne : c'.1 ≠ jr) (h : WalsAt jr Ls (l1 ++ c :: l2)) : WalsAt jr Ls (l1 ++ c' :: l2) := by
  refine walsAt_congr (fun dir l hl => ⟨l, hl, rfl, rfl⟩) (fun N hh hm => ?_) h
  simp only [List.mem_append, List.mem_cons] at hm ⊢
  rcases hm with hm | hm | hm
  · exact Or.inl hm
  · exact absurd (by rw [← hm]) hne
  · exact Or.inr (Or.inr hm)

end pure

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

instance walOsBytes_timeless (i : Ino) (off : Nat) (dq : DFrac) (xs : List ByteG) :
    Timeless (osBytes (L := L) i off dq xs) := by unfold osBytes; infer_instance

/-- The invariant's halves of a named segment: of its `OsMeta` and of all its bytes. -/
def segRes (g : SegG) : IProp GF :=
  iprop(osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
    osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

/-- The invariant's halves of every named segment of every WAL. -/
def laysRes (Ls : GMap GoString WalLay) : IProp GF :=
  iprop([∗map] _dir ↦ lay ∈ Ls, [∗list] g ∈ lay.segs, segRes (L := L) g)

theorem laysRes_list (Ls : GMap GoString WalLay) :
    laysRes (L := L) Ls ⊣⊢ [∗list] g ∈ segsAll Ls, segRes (L := L) g := by
  unfold laysRes segsAll
  rw [BigSepL.bigSepL_flatMap]
  exact BigSepM.bigSepM_toList

/-- **The invariant's part of a segment, a change maybe in flight on it** (`F` by inode): idle, its
halves (`segRes`); with a write in flight, the write's token and the halves of the bytes around it,
the layout holding the segment as the write announced it (`SegFl.Ok`); with a resize in flight
(I3b), its token (`rsTok`, holding the bytes it cuts off) and the halves of the bytes below, the
layout holding the segment as the resize announced it (`SegFl.OkR`). -/
def segResF (F : GMap Ino SegFl) (g : SegG) : IProp GF :=
  match F !! g.ino with
  | none => segRes (L := L) g
  | some fl => match fl.rz with
    | none => iprop(pwTok (L := L) fl.t g.ino fl.off fl.data fl.m
          (cfRange fl.m fl.bs fl.off fl.data.length) fl.n ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) (fl.bs.take (cfLo fl.m fl.off)) ∗
        osBytes (L := L) g.ino (cfHi fl.m fl.off fl.data.length) (DFrac.own (1 : Qp).half)
          (fl.bs.drop (cfHi fl.m fl.off fl.data.length)) ∗ ⌜fl.Ok g⌝)
    | some (tr, tg) => iprop(rsTok (L := L) tr fl.t g.ino tg fl.m (fl.bs.drop (min fl.m.size tg)) fl.n ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) (fl.bs.take (min fl.m.size tg)) ∗
        ⌜fl.OkR tr tg g⌝)

/-- The invariant's parts of every named segment of every WAL, the writes in flight `F`. -/
def laysResF (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) : IProp GF :=
  iprop([∗list] g ∈ segsAll Ls, segResF (L := L) F g)

theorem laysResF_empty (Ls : GMap GoString WalLay) :
    laysResF (L := L) ∅ Ls ⊣⊢ laysRes (L := L) Ls := by
  refine BiEntails.trans ?_ (laysRes_list (L := L) Ls).symm
  unfold laysResF segResF
  have h : ∀ i : Ino, (∅ : GMap Ino SegFl) !! i = none := fun i => by simp
  simp only [h]
  exact .rfl

instance segResF_timeless (F : GMap Ino SegFl) (g : SegG) : Timeless (segResF (L := L) F g) := by
  unfold segResF segRes pwTok rsTok osTok osMeta
  split
  · infer_instance
  · split <;> infer_instance

/-- **The open handles' tails** (W6): the tails' authority, and for each directory with an open
handle, its WAL and layout, the last segment, F-Z, the record boundary (`TailBound`), and the
invariant's half of the tail. -/
def walTailsRes (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ T : GMap GoString GName, walTailsAuth (W := W) T ∗
    [∗map] dir ↦ γ ∈ T, ∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))

instance walTailsRes_timeless (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (F : GMap Ino SegFl) :
    Timeless (walTailsRes (W := W) C Mr s Ls F) := by
  unfold walTailsRes
  letI := walAllG (W := W)
  haveI : ∀ (γ : GName) (x : TailG), Timeless (ghostVar (GF := GF) γ (1 : Qp).half x) :=
    fun _ _ => inferInstance
  haveI : ∀ (dir : GoString) (γ : GName), Timeless (iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar (GF := GF) γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) :=
      fun _ _ => inferInstance
  infer_instance

/-- **The tails as the WAL state changes elsewhere than the histories and metadata** (`named`, the
mark, the purge bounds). -/
theorem walTailsRes_mono (C : WalCodec) (Mr : WalMarshal) (s s' : AbsDiskState) (Ls : GMap GoString WalLay) (F : GMap Ino SegFl)
    (h : ∀ dir d, s.wal !! dir = some d →
      ∃ d', s'.wal !! dir = some d' ∧ d'.H = d.H ∧ d'.metadata = d.metadata) :
    walTailsRes (W := W) C Mr s Ls F ⊢ walTailsRes (W := W) C Mr s' Ls F := by
  unfold walTailsRes
  letI := walAllG (W := W)
  iintro ⟨%T, Ha, Hm⟩
  iexists T
  iframe Ha
  iapply BigSepM.bigSepM_mono_of_forall _ $$ Hm
  intro dir γ
  iintro ⟨%d, %lay, %g, %hp, Hv⟩
  obtain ⟨d', hd', hH, hmd⟩ := h dir d hp.1
  iexists d', lay, g
  have e : tailG d' lay g.ino (F !! g.ino) = tailG d lay g.ino (F !! g.ino) := by
    simp [tailG, hH, hmd]
  rw [e]
  iframe Hv
  ipureintro
  exact ⟨hd', hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.congr hH hmd⟩

/-- **A segment's program halves, parked** (`walParked`): of its inode's `OsMeta` and of bytes from
0 on, as many as the segment's. Not `segRes g` itself: the contents are the segment's (by agreement
with the invariant's halves, `segResF`) only while no change is in flight on it, and an open handle
changes its tail's contents in the layout (`walInvBody_tail`, `TailAcc.lean`) with the tail's halves
out, so the parked entry of a segment must not depend on its contents. -/
def segResP (g : SegG) : IProp GF :=
  iprop(∃ (m : OsMeta) (bs : List ByteG), osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) m ∗
    osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜bs.length = g.bs.length⌝)

theorem segRes_segResP (g : SegG) : segRes (L := L) g ⊢ segResP (L := L) g := by
  unfold segRes segResP
  iintro ⟨Hm, Hb⟩
  iexists g.om, g.bs
  iframe Hm Hb
  ipureintro; rfl

/-- **The pipeline names, parked** (W3/W5's gap 3; part of `walParked`, `T` the record's directories
out): for each directory of `Jt` (a superset of the WALs': each WAL's directory inode `lay.j` at its
key), both pipeline names' whole claims (`walTmpsRes`, with any leftover `N.tmp` file whole) but those
of the directories `T`, which a write-mode handle holds (`Open` takes its WAL's, `Close` puts them back,
a new WAL's are its creator's). -/
def walTmpParked (Ls : GMap GoString WalLay) (T : List GoString) : IProp GF :=
  iprop(∃ (Jt : GMap GoString Ino),
    ⌜∀ dir lay, Ls !! dir = some lay → Jt !! dir = some lay.j⌝ ∗
    [∗map] dir ↦ J ∈ Jt, if dir ∈ T then emp else walTmpsRes (hG := ⟨G, L⟩) J)

instance walTmpParked_timeless (Ls : GMap GoString WalLay) (T : List GoString) :
    Timeless (walTmpParked (G := G) (L := L) Ls T) := by
  unfold walTmpParked
  haveI : ∀ (T : List GoString) (dir : GoString) (J : Ino), Timeless (iprop(if dir ∈ T then iprop(emp)
      else walTmpsRes (hG := ⟨G, L⟩) J) : IProp GF) :=
    fun T dir J => by split <;> infer_instance
  infer_instance

/-- **The parked pipeline names under a change of layouts** with the same directories (the tail's
steps, a cut). -/
theorem walTmpParked_congr (Ls Ls' : GMap GoString WalLay) (T : List GoString)
    (hL : ∀ dir lay', Ls' !! dir = some lay' → ∃ lay, Ls !! dir = some lay ∧ lay.j = lay'.j) :
    walTmpParked (G := G) (L := L) Ls T ⊢ walTmpParked (G := G) (L := L) Ls' T := by
  unfold walTmpParked
  iintro ⟨%Jt, %hp, Hm⟩
  iexists Jt
  iframe Hm
  ipureintro
  intro dir lay' hl'
  obtain ⟨lay, hl, hj⟩ := hL dir lay' hl'
  rw [← hj]; exact hp dir lay hl

/-- The layout at a key replaced by one of the same directory (the tail's steps, a cut). -/
theorem walTmpParked_insert (Ls : GMap GoString WalLay) (T : List GoString) (dir : GoString)
    (lay lay' : WalLay) (hl : Ls !! dir = some lay) (hj : lay'.j = lay.j) :
    walTmpParked (G := G) (L := L) Ls T ⊢ walTmpParked (G := G) (L := L) (<[dir := lay']> Ls) T := by
  refine walTmpParked_congr Ls _ T (fun dir' l hl' => ?_)
  by_cases hd : dir' = dir
  · subst hd
    rw [GMap.lookup_insert_eq] at hl'
    cases hl'
    exact ⟨lay, hl, hj.symm⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'
    exact ⟨l, hl', rfl⟩

/-- **A new WAL's pipeline names are out** (`Create`'s commit; its directory into the record's `T`):
its key's entry is replaced (what was parked there, if anything, dropped). -/
theorem walTmpParked_create (Ls : GMap GoString WalLay) (T : List GoString) (dir : GoString)
    (lay : WalLay) :
    walTmpParked (G := G) (L := L) Ls T ⊢
      walTmpParked (G := G) (L := L) (<[dir := lay]> Ls) (dir :: T) := by
  classical
  unfold walTmpParked
  iintro ⟨%Jt, %hp, Hm⟩
  iexists <[dir := lay.j]> Jt
  isplitr
  · ipureintro
    intro dir' lay' hl'
    by_cases hd : dir' = dir
    · subst hd
      rw [GMap.lookup_insert_eq] at hl'
      cases hl'
      rw [GMap.lookup_insert_eq]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)]
      exact hp dir' lay' hl'
  have hdel : ([∗map] dir' ↦ J ∈ Jt, if dir' ∈ T then emp else walTmpsRes (hG := ⟨G, L⟩) J) ⊢
      [∗map] dir' ↦ J ∈ GMap.delete dir Jt,
        if dir' ∈ dir :: T then emp else walTmpsRes (hG := ⟨G, L⟩) J := by
    refine Entails.trans (BigSepM.bigSepM_subseteq (GMap.delete_subseteq Jt dir))
      (BigSepM.bigSepM_mono (fun {k J} hk => ?_))
    have hkd : k ≠ dir := by
      intro e; subst e
      have h2 : get? (GMap.delete k Jt) k = none := GMap.lookup_delete_eq Jt k
      rw [h2] at hk; cases hk
    have e : (k ∈ dir :: T) ↔ k ∈ T := by simp [hkd]
    simp only [propext e]
    exact .rfl
  iapply (BigSepM.bigSepM_insert_delete (Φ := fun (dir' : GoString) (J : Ino) =>
    iprop(if dir' ∈ dir :: T then emp else walTmpsRes (hG := ⟨G, L⟩) J))).2
  isplitr
  · rw [if_pos (List.mem_cons_self ..)]; iempintro
  iapply hdel $$ Hm

/-- **`Open` takes its WAL's pipeline names** (its directory into the record's `T`). -/
theorem walTmpParked_take (Ls : GMap GoString WalLay) (T : List GoString) (dir : GoString)
    (lay : WalLay) (hl : Ls !! dir = some lay) (hT : dir ∉ T) :
    walTmpParked (G := G) (L := L) Ls T ⊢
      walTmpParked (G := G) (L := L) Ls (dir :: T) ∗ walTmpsRes (hG := ⟨G, L⟩) lay.j := by
  classical
  unfold walTmpParked
  iintro ⟨%Jt, %hp, Hm⟩
  have hJ := hp dir lay hl
  ihave Hm := (BigSepM.bigSepM_delete (Φ := fun (dir' : GoString) (J : Ino) =>
    iprop(if dir' ∈ T then emp else walTmpsRes (hG := ⟨G, L⟩) J)) hJ).1 $$ Hm
  icases Hm with ⟨Hd, Hm⟩
  rw [if_neg hT]
  iframe Hd
  iexists Jt
  isplitr
  · ipureintro; exact hp
  iapply (BigSepM.bigSepM_delete (Φ := fun (dir' : GoString) (J : Ino) =>
    iprop(if dir' ∈ dir :: T then emp else walTmpsRes (hG := ⟨G, L⟩) J)) hJ).2
  isplitr
  · rw [if_pos (List.mem_cons_self ..)]; iempintro
  iapply BigSepM.bigSepM_mono (fun {k J} hk => ?_) $$ Hm
  have hkd : k ≠ dir := by
    intro e; subst e
    have h2 : get? (delete Jt k) k = none := GMap.lookup_delete_eq Jt k
    rw [h2] at hk; cases hk
  have e : (k ∈ dir :: T) ↔ k ∈ T := by simp [hkd]
  simp only [propext e]
  exact .rfl

/-- **The put-back of a WAL's pipeline names** (`Close`, an `Open` failing after its pin): its
directory off the record's `T`. -/
theorem walTmpParked_put (Ls : GMap GoString WalLay) (T : List GoString) (dir : GoString)
    (lay : WalLay) (hl : Ls !! dir = some lay) :
    walTmpParked (G := G) (L := L) Ls T ∗ walTmpsRes (hG := ⟨G, L⟩) lay.j ⊢
      walTmpParked (G := G) (L := L) Ls (T.filter (· ≠ dir)) := by
  classical
  unfold walTmpParked
  iintro ⟨⟨%Jt, %hp, Hm⟩, Hd⟩
  have hJ := hp dir lay hl
  ihave Hm := (BigSepM.bigSepM_delete (Φ := fun (dir' : GoString) (J : Ino) =>
    iprop(if dir' ∈ T then emp else walTmpsRes (hG := ⟨G, L⟩) J)) hJ).1 $$ Hm
  icases Hm with ⟨-, Hm⟩
  iexists Jt
  isplitr
  · ipureintro; exact hp
  iapply (BigSepM.bigSepM_delete (Φ := fun (dir' : GoString) (J : Ino) =>
    iprop(if dir' ∈ T.filter (· ≠ dir) then emp else walTmpsRes (hG := ⟨G, L⟩) J)) hJ).2
  isplitl [Hd]
  · rw [if_neg (by simp)]; iexact Hd
  iapply BigSepM.bigSepM_mono (fun {k J} hk => ?_) $$ Hm
  have hkd : k ≠ dir := by
    intro e; subst e
    have h2 : get? (delete Jt k) k = none := GMap.lookup_delete_eq Jt k
    rw [h2] at hk; cases hk
  have e : (k ∈ T.filter (· ≠ dir)) ↔ k ∈ T := by simp [hkd]
  simp only [propext e]
  exact .rfl

/-- **The program's halves, parked** (W3/W5's gap 2, framed): the parking flag's invariant half
(`walParkAuth b`, `Ghost.lean`) and the record of what is out (`walOutAuth o`, gap A: its other half
is the lock token's, empty, so that `Open` finds nothing out, or the holder's of what is out, so that
a put-back knows exactly what it returns: `Parked.lean`); every segment's program halves (`segResP`)
but those of the inodes `o.O`, and the program's half of every WAL directory's claim
(`WalDirClaimOf`) but those of the keys `o.D`. A handle takes what it needs (`Open`: the opened WAL's
segments from the selected one on and its directory claim) and puts back what it does not keep
(`ReadAll`: all but the tail's); returning a half needs no token (a third half contradicts). And the
pipeline names' claims (`walTmpParked`, gap 3) but those of the directories `o.T`. **A change in
flight only on a segment taken out** (gap B: `F`, the invariant's changes in flight, only on `o.O`),
so the parked segments are idle and their halves the layout's (`Open`'s pin). -/
def walParked (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl) : IProp GF :=
  iprop(∃ (b : Bool) (o : WalOut), walParkAuth (W := W) b ∗ walOutAuth (W := W) o ∗
    ⌜∀ i, F !! i ≠ none → i ∈ o.O⌝ ∗
    ([∗list] g ∈ segsAll Ls, if g.ino ∈ o.O then emp else segResP (L := L) g) ∗
    ([∗list] c ∈ cl, if ParkedClaim Ls o.D c then
      osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp) ∗
    walTmpParked (G := G) (L := L) Ls o.T)

instance walParked_timeless (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl) :
    Timeless (walParked (L := L) (W := W) Ls cl F) := by
  haveI : ∀ g : SegG, Timeless (segResP (L := L) g) := fun g => by
    unfold segResP osMeta; infer_instance
  haveI : ∀ (j : Ino) (N : NameSet) (q : DFrac) (h : NamesH), Timeless (osNames (L := L) j N q h) :=
    fun _ _ _ _ => by unfold osNames; split <;> infer_instance
  unfold walParked
  haveI : ∀ (O : List Ino) (g : SegG),
      Timeless (iprop(if g.ino ∈ O then iprop(emp) else segResP (L := L) g) : IProp GF) :=
    fun O g => by split <;> infer_instance
  haveI : ∀ (D : List (Ino × NameSet)) (c : Claim), Timeless (iprop(if ParkedClaim Ls D c then
      osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else iprop(emp)) : IProp GF) :=
    fun D c => by split <;> infer_instance
  infer_instance

/-- **The WAL invariant's contents**, the real WAL state being `s`. -/
def walInvBody (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) : IProp GF :=
  iprop(∃ (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (F : GMap Ino SegFl),
    walGhost (W := W) s ∗ ⌜s.area = r⌝ ∗
    osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗ osCommitLb (L := L) n ∗
    laysResF (L := L) F Ls ∗ ⌜WalsOk C Mr R jr s Ls cl n⌝ ∗ ⌜WalsCreateOk jr cl⌝ ∗
    (∃ CR, walCreatingAuth (W := W) CR ∗ ⌜CreatingOk jr cl CR⌝) ∗ walTailsRes (W := W) C Mr s Ls F ∗
    ⌜AbsentNone s jr cl n ∧ DirsAvoid R jr s⌝ ∗ ⌜WalsNamed Ls cl n⌝ ∗ walParked (L := L) (W := W) Ls cl F ∗
    (∃ K c, walDirKeysAuth (W := W) K ∗ walCutAuth (W := W) c ∗ ⌜DirKeysOk C Mr jr s Ls cl n K c⌝) ∗
    ⌜WalsAt jr Ls cl⌝)

instance walInvBody_timeless (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) : Timeless (walInvBody (L := L) (W := W) C Mr R jr r s) := by
  unfold walInvBody laysResF osClaims; infer_instance

/-- **The WAL invariant** of the area `r`, the directory `jr` under the roots `R`: its contents, or,
once `walInv_crash` has taken them, the generation's `crashed` (Perennial's crash token,
`Perennial/GooseLang/CrashToken.lean`, which the crash adequacy theorem gives the crash obligation)
with the WAL's own crash token (`walCrashTok`, exclusive: the contents are taken once). A step of the
running generation holds `notCrashed` (in its state interpretation), which excludes the second
branch (`walInv_open`). -/
def walInv (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : IProp GF :=
  inv walN iprop((∃ s : AbsDiskState, walInvBody (L := L) (W := W) C Mr R jr r s) ∨
    (crashed (hC := L.goose_crashGS) ∗ walCrashTok (W := W)))

instance walInv_persistent (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    Persistent (walInv (L := L) (W := W) C Mr R jr r) := by
  unfold walInv; infer_instance

/-- **Opening the WAL invariant while the generation runs**: with `notCrashed` (which a step of the
generation has, in its state interpretation), the invariant holds its contents; it is closed again
with contents. -/
theorem walInv_open (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (E : CoPset) (hE : ↑walN ⊆ E) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) ={E, E \ ↑walN}=∗
      (∃ s, walInvBody (L := L) (W := W) C Mr R jr r s) ∗ notCrashed (hC := L.goose_crashGS) ∗
      ((∃ s, walInvBody (L := L) (W := W) C Mr R jr r s) ={E \ ↑walN, E}=∗ True) := by
  iintro #Hinv Hnc
  unfold walInv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hb | ⟨>Hc, -⟩)
  · imodintro
    iframe Hb Hnc
    iintro Hb
    iapply Hclose
    inext; ileft; iexact Hb
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc

end inv

end WalFs
end EtcdGrove
end Perennial

end
