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

A write may extend the tail past its size (a `Save` crossing the preallocated size, `sync`'s flush
after `cut`'s truncate): the layout's `OsMeta` then keeps the candidates the write announced past the
size (`wrMeta`, `pwTail`-shaped), which the token's `OsMeta` forgot and a crash may keep (W6 log,
fifteenth session).

**Not yet here**: `Create`'s `dir.tmp`.
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

/-- **The `OsMeta` of a segment with a write in flight, as the layout holds it** (W6, fifteenth
session): the token's (`cfMeta`: `m` with `[off, off + |data|)` announced), and of each byte it
announced past the size, the candidates `m` knew (`OsMeta.pc`) then the data's byte stamped `n`
(`pwTail`, as `wp_osPWriteFinishK true` leaves them), which the token's `OsMeta` forgot and a crash
may keep (`crashRestAt_take_tok`'s last fact, from the state's `tok_cand`). A write inside the size
announces nothing past it: then the token's (`wrMeta_in`). -/
def wrMeta (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) : OsMeta :=
  { cfMeta m off data.length with tc := pwTail m off data n }

/-- A write inside the size: the layout's `OsMeta` is the token's. -/
theorem wrMeta_in {m : OsMeta} {off : Nat} {data : List w8} {n : Nat}
    (hin : off + data.length ≤ m.size) : wrMeta m off data n = cfMeta m off data.length := by
  have htc : pwTail m off data n = (cfMeta m off data.length).tc := by
    apply GMap.ext; intro b
    show pwTail m off data n !! b = (cfMeta m off data.length).tc !! b
    rw [pwTail_lookup]
    unfold cfMeta
    rw [announce_tc]
    by_cases hr : inRange off (off + data.length) b = true
    · have hr' := hr
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr'
      rw [if_pos hr, if_neg (by omega), if_pos (by simp [inRange]; omega)]
    · rw [if_neg hr, if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr ⊢; omega)]
  unfold wrMeta; rw [htc]

@[simp] theorem wrMeta_size (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).size = m.size := by simp [wrMeta, cfMeta]
@[simp] theorem wrMeta_lo (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).lo = (cfMeta m off data.length).lo := rfl
@[simp] theorem wrMeta_hi (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).hi = (cfMeta m off data.length).hi := rfl
@[simp] theorem wrMeta_zf (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).zf = (cfMeta m off data.length).zf := rfl
@[simp] theorem wrMeta_cut (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).cut = m.cut := by simp [wrMeta, cfMeta]
@[simp] theorem wrMeta_rz (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).rz = (cfMeta m off data.length).rz := rfl
@[simp] theorem wrMeta_maps (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).maps = m.maps := by simp [wrMeta, cfMeta]

/-- **The segment `g` as the write in flight `fl` announced it**: the write starting inside the
segment (`pwrite` extends a file only from inside it, `pwTok`'s `off ≤ size`; it may pass the size:
a `Save` crossing the preallocated size), not empty; `g`'s `OsMeta` the token's with the candidates
announced past the size (`wrMeta`), its bytes `fl.bs` with the data's candidates added to the written
range below the size (`pwAnn`); and the write past the segment's first byte (`0 < fl.off`: the tail's writes come after its header
records, synced when the segment was named), so that the invariant keeps half of byte 0 of every
segment, idle or written to: a file the program holds byte 0 of wholly (a segment it creates) is
none of them (`laysResF_ino_ne`, `InvInos.lean`; the inode-clash gap of `Create`'s and `cut`'s
commits). -/
def SegFl.Ok (fl : SegFl) (g : SegG) : Prop :=
  fl.off ≤ fl.m.size ∧ fl.data ≠ [] ∧ fl.bs.length = fl.m.size ∧
  fl.m.cut = none ∧ g.om = wrMeta fl.m fl.off fl.data fl.n ∧
  g.bs = fl.bs.take (cfLo fl.m fl.off) ++
    pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length) ++
    fl.bs.drop (cfHi fl.m fl.off fl.data.length) ∧ 0 < fl.off

/-- **The `OsMeta` of a segment with a resize in flight, as the layout holds it** (I3b): the token's
(`TokInfo.meta`: `m` with `[min size tg, rsHi tr size tg)` announced, the target `tg`), and of each byte
it announced past the size, the candidates `m` knew (`OsMeta.pc`) then the zero stamped `n` (`rsTail` at
the old size), which the token's `OsMeta` forgot and a crash may keep (`crashRestAt_take_tok`'s last
fact, from the state's `tok_cand`): a growth's bytes past the old size, those a truncate's landing kept
in `tc`; and the resize's stamp `n` among the stamps known (`OsMeta.rz`; the state recorded it at the first
step, `OsCoh.tok_rz`). -/
def rzMeta (tr : Bool) (m : OsMeta) (tg n : Nat) : OsMeta :=
  { m.announce (min m.size tg) (rsHi tr m.size tg) tg with
    tc := rsTail tr m tg m.size n [], rz := n :: m.rz }

/-- **The segment `g` as the resize in flight `fl` to `tg` (`ftruncate` if `tr`, else `fallocate`'s
growth) announced it** (I3b; `wp_osResizeStart`): `g`'s `OsMeta` the token's with the candidates past
the size (`rzMeta`), its bytes `fl.bs` with zero added as a
candidate of each byte cut off (`rsAnn`; none if it grows the file); the resize keeps byte 0
(`0 < min size tg`), so that the invariant keeps half of it, as `SegFl.Ok`'s `0 < fl.off`. -/
def SegFl.OkR (fl : SegFl) (tr : Bool) (tg : Nat) (g : SegG) : Prop :=
  fl.bs.length = fl.m.size ∧ fl.m.cut = none ∧
  g.om = rzMeta tr fl.m tg fl.n ∧
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

/-- **A change in flight only on a registered tail** (`walTailsRes`'s pure part): a segment with a
change in flight (`F`) is the last segment of a WAL whose open handle has a tail record (`T`). A change
starts only through the tail's access (`walInvBody_tail`, `TailAcc.lean`), which needs the tail's key.
With the program's half of the tails' authority empty (`walTailsFrag ∅`, the lock token's: no tail
registered), no change is in flight (`walTailsRes_none`), so a holder of what is out with no tail
record can put back every segment it took, the WAL's last one too. -/
def TailsOnly {G : Type} (T : GMap GoString G) (Ls : GMap GoString WalLay) (F : GMap Ino SegFl) : Prop :=
  ∀ i, F !! i ≠ none → ∃ dir γ lay g, T !! dir = some γ ∧ Ls !! dir = some lay ∧
    lay.segs.getLast? = some g ∧ g.ino = i

theorem TailsOnly.none_of_empty {G : Type} {Ls : GMap GoString WalLay} {F : GMap Ino SegFl}
    (h : TailsOnly (∅ : GMap GoString G) Ls F) : ∀ i, F !! i = none := by
  intro i
  refine Classical.byContradiction fun hi => ?_
  obtain ⟨dir, γ, -, -, hT, -⟩ := h i hi
  simp at hT

/-- Fewer changes in flight, the layouts and tails unchanged. -/
theorem TailsOnly.mono_F {G : Type} {T : GMap GoString G} {Ls : GMap GoString WalLay}
    {F F' : GMap Ino SegFl} (h : TailsOnly T Ls F) (hF : ∀ i, F' !! i ≠ none → F !! i ≠ none) :
    TailsOnly T Ls F' := fun i hi => h i (hF i hi)

/-- **A registered WAL's layout replaced** (its tail's steps, a cut): the changes in flight are on its
new last segment `g` or were in flight before off its old last segment `g0`. -/
theorem TailsOnly.insert {G : Type} {T : GMap GoString G} {Ls : GMap GoString WalLay}
    {F F' : GMap Ino SegFl} {dir : GoString} {lay lay' : WalLay} {g0 g : SegG} {γ : G}
    (h : TailsOnly T Ls F) (hT : T !! dir = some γ) (hl : Ls !! dir = some lay)
    (hg0 : lay.segs.getLast? = some g0) (hg : lay'.segs.getLast? = some g)
    (hF : ∀ i, F' !! i ≠ none → i = g.ino ∨ (F !! i ≠ none ∧ i ≠ g0.ino)) :
    TailsOnly T (<[dir := lay']> Ls) F' := by
  intro i hi
  rcases hF i hi with rfl | ⟨hFi, hne⟩
  · exact ⟨dir, γ, lay', g, hT, GMap.lookup_insert _ _ _, hg, rfl⟩
  · obtain ⟨d2, γ2, l2, g2, hT2, hl2, hg2, hi2⟩ := h i hFi
    by_cases hd : d2 = dir
    · subst hd
      rw [hl] at hl2; cases hl2
      rw [hg0] at hg2; cases hg2
      exact absurd hi2.symm hne
    · exact ⟨d2, γ2, l2, g2, hT2, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)]; exact hl2, hg2, hi2⟩

/-- **A new WAL's layout** (`Create`'s commit): no tail of it registered. -/
theorem TailsOnly.insert_new {G : Type} {T : GMap GoString G} {Ls : GMap GoString WalLay}
    {F F' : GMap Ino SegFl} {dir : GoString} {lay : WalLay}
    (h : TailsOnly T Ls F) (hLd : Ls !! dir = none) (hF : ∀ i, F' !! i ≠ none → F !! i ≠ none) :
    TailsOnly T (<[dir := lay]> Ls) F' := by
  intro i hi
  obtain ⟨d2, γ2, l2, g2, hT2, hl2, hg2, hi2⟩ := h i (hF i hi)
  have hd : d2 ≠ dir := by rintro rfl; rw [hLd] at hl2; cases hl2
  exact ⟨d2, γ2, l2, g2, hT2, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)]; exact hl2, hg2, hi2⟩

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

/-- **A WAL directory's claim, as the invariant has it** (gap C; `DirKeysOk`'s facts of a key): the
directory `j` not the area's, the claim `(j, .except X, hj)` (`X` holding no `.wal` name) once among
the claims, coherent, and no other claim of `j` holding a `.wal` name. -/
def DirClaimOk (jr : Ino) (cl : List Claim) (j : Ino) (X : List GoString) (hj : NamesH) : Prop :=
  j ≠ jr ∧ (∀ b ∈ X, walNameP b = false) ∧ ClaimOnce (j, .except X, hj) cl ∧
    ClaimCoh hj j (.except X) ∧
    ∀ c' ∈ cl, c' ≠ (j, .except X, hj) → c'.1 = j → ∀ b, walNameP b = true → ¬ c'.2.1.Mem b

/-- **Every WAL's directory claim, once and exclusive** (gap C, `DirKeysOk`'s third conjunct): of
every present WAL, keyed or not, so that a holder of its program half can put it back at a later step
(`walParked_putClaim`'s `l1 ++ c :: l2`, no other claim of its key) and the pin can key it
(`walDirKey_insert`). Established at the start (`walInv_alloc`'s `hdirs1`: the boot program's claims),
kept by every step (no claim of a WAL directory changes but a cut's, which keeps these facts). -/
def DirClaimsOk (jr : Ino) (Ls : GMap GoString WalLay) (cl : List Claim) : Prop :=
  ∀ dir lay, Ls !! dir = some lay → ∃ X hj, DirClaimOk jr cl lay.j X hj

/-- **The WAL directories' claim keys, and no cut pending** (framed; W2 log, "the directory-claim
map"). Each key `dir ↦ (j, X)` (`walDirKey`, persistent; an open handle holds the program's half of
that claim): the WAL in `dir` has a layout of directory `j`, not the area's; the claim `(j, .except
X, hj)` (`X` holding no `.wal` name) occurs once among the claims, coherent, and no other claim of
`j` holds a `.wal` name (the shared invariant's `NamesCoh.disj`, recorded where the key is made: an
update's opening, inside an `os` call's, cannot open that invariant). And every WAL but the one whose
cut's rename is pending (`c`, `walCutAuth`; the lock token holds `none`) has no alternative layout
(`CrashOkA … none`, i.e. `CrashOk`): a cut's rename needs it of its WAL. And every WAL's directory claim is once and
exclusive (`DirClaimsOk`, gap C). -/
def DirKeysOk (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat)
    (K : GMap GoString (Ino × List GoString)) (c : Option GoString) : Prop :=
  (∀ dir j X, K !! dir = some (j, X) → ∃ lay hj, Ls !! dir = some lay ∧ lay.j = j ∧ j ≠ jr ∧
    (∀ b ∈ X, walNameP b = false) ∧ ClaimOnce (j, .except X, hj) cl ∧ ClaimCoh hj j (.except X) ∧
    ∀ c' ∈ cl, c' ≠ (j, .except X, hj) → c'.1 = j → ∀ b, walNameP b = true → ¬ c'.2.1.Mem b) ∧
  (∀ dir d lay, s.wal !! dir = some d → Ls !! dir = some lay → c ≠ some dir →
    CrashOkA C Mr d lay none cl n) ∧
  DirClaimsOk jr Ls cl

theorem walNameP_dotWal : walNameP go!".wal" = true := by decide

theorem exceptMem_dotWal {X : List GoString} (hX : ∀ b ∈ X, walNameP b = false) :
    (NameSet.except X).Mem go!".wal" := fun hb => by
  have h := walNameP_dotWal
  rw [hX _ hb] at h; cases h

/-- The WAL directory's claim is the only claim of `j` on all names but non-`.wal` ones. -/
theorem DirClaimOk.eq_of_mem {jr : Ino} {cl : List Claim} {j : Ino} {X X' : List GoString}
    {hj hj' : NamesH} (h : DirClaimOk jr cl j X hj) (hX' : ∀ b ∈ X', walNameP b = false)
    (hm : (j, NameSet.except X', hj') ∈ cl) : X' = X ∧ hj' = hj := by
  by_cases e : (j, NameSet.except X', hj') = (j, NameSet.except X, hj)
  · simp only [Prod.mk.injEq, NameSet.except.injEq, true_and] at e; exact e
  · exact absurd (exceptMem_dotWal hX') (h.2.2.2.2 _ hm e rfl _ walNameP_dotWal)

/-- **The claim found once by its key** (`walParked_putClaim`'s premises): no other claim of its
directory and names. -/
theorem DirClaimOk.key_once {jr : Ino} {cl : List Claim} {j : Ino} {X : List GoString} {hj : NamesH}
    (h : DirClaimOk jr cl j X hj) : ∃ l1 l2, cl = l1 ++ (j, NameSet.except X, hj) :: l2 ∧
      ∀ c' ∈ l1 ++ l2, (c'.1, c'.2.1) ≠ (j, NameSet.except X) := by
  obtain ⟨-, hX, ⟨l1, l2, hcl, h1, h2⟩, -, hex⟩ := h
  refine ⟨l1, l2, hcl, fun c' hc' e => ?_⟩
  simp only [Prod.mk.injEq] at e
  have hne : c' ≠ (j, NameSet.except X, hj) := by
    rintro rfl
    rcases List.mem_append.1 hc' with h' | h'
    · exact h1 h'
    · exact h2 h'
  have hmem : c' ∈ cl := by rw [hcl]; rcases List.mem_append.1 hc' with h' | h' <;> simp [h']
  refine hex c' hmem hne e.1 _ walNameP_dotWal ?_
  rw [e.2]; exact exceptMem_dotWal hX

/-- `DirClaimsOk` with a layout replaced by one of the same directory. -/
theorem DirClaimsOk.insert {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} {dir : GoString}
    {lay lay' : WalLay} (h : DirClaimsOk jr Ls cl) (hl : Ls !! dir = some lay) (hj : lay'.j = lay.j) :
    DirClaimsOk jr (<[dir := lay']> Ls) cl := by
  intro dir' l hl'
  by_cases e : dir' = dir
  · subst e
    rw [GMap.lookup_insert_eq] at hl'
    cases hl'
    rw [hj]; exact h _ _ hl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
    exact h _ _ hl'

/-- `DirClaimsOk` under a change of claims keeping each WAL directory's facts. -/
theorem DirClaimsOk.mono_cl {jr : Ino} {Ls : GMap GoString WalLay} {cl cl' : List Claim}
    (h : DirClaimsOk jr Ls cl)
    (hc : ∀ dir lay, Ls !! dir = some lay → ∀ X hj, DirClaimOk jr cl lay.j X hj →
      DirClaimOk jr cl' lay.j X hj) : DirClaimsOk jr Ls cl' := fun dir lay hl =>
  let ⟨X, hj, hk⟩ := h dir lay hl; ⟨X, hj, hc dir lay hl X hj hk⟩

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

/-- **Every WAL's metadata is shorter than `2^41`** (a framed conjunct of `walInvBody`; the plan's W1
log, fifteenth session): `Create` takes the bound on its metadata (its spec's premise), `walInv_alloc`
on the WALs found at boot, and no other step changes a WAL's metadata. `ReadAll` reads it
(`walInvBody_bounded`): the metadata record it decodes and returns. -/
def WalsBounded (s : AbsDiskState) : Prop :=
  ∀ dir d, s.wal !! dir = some d → d.metadata.length < 2 ^ 41

/-- `WalsBounded` is kept by a change of WAL states keeping each present WAL's metadata. -/
theorem WalsBounded.mono {s s' : AbsDiskState} (h : WalsBounded s)
    (h' : ∀ dir d', s'.wal !! dir = some d' → ∃ d, s.wal !! dir = some d ∧ d'.metadata = d.metadata) :
    WalsBounded s' := by
  intro dir d' hd'
  obtain ⟨d, hd, he⟩ := h' dir d' hd'
  rw [he]; exact h dir d hd

/-- `WalsBounded` with one WAL's state set to one with a bounded metadata. -/
theorem walsBounded_ins {s s' : AbsDiskState} {dir : GoString} {d' : WalDur} (h : WalsBounded s)
    (hw : s'.wal = <[dir := d']> s.wal) (hd' : d'.metadata.length < 2 ^ 41) : WalsBounded s' := by
  intro k e he
  rw [hw] at he
  by_cases hk : k = dir
  · subst hk; rw [GMap.lookup_insert_eq] at he; cases he; exact hd'
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at he; exact h k e he

/-- `WalsBounded` with one WAL's state set to one with the same metadata. -/
theorem walsBounded_insSame {s s' : AbsDiskState} {dir : GoString} {d d' : WalDur} (h : WalsBounded s)
    (hw : s'.wal = <[dir := d']> s.wal) (hd : s.wal !! dir = some d) (hm : d'.metadata = d.metadata) :
    WalsBounded s' :=
  walsBounded_ins h hw (by rw [hm]; exact h dir d hd)

/-- `WalsBounded` across an update of one WAL keeping its metadata (`absDiskUpd`). -/
theorem walsBounded_upd {s : AbsDiskState} {dir : GoString} {f : WalDur → WalDur} (h : WalsBounded s)
    (hm : ∀ d, (f d).metadata = d.metadata) : WalsBounded (absDiskUpd s dir f) := by
  unfold absDiskUpd
  cases hd : s.wal !! dir with
  | none => exact h
  | some d => exact walsBounded_insSame h rfl hd (hm d)

/-- **The last segment synced** (`TailIdle`'s third part; the W7-W12 log, sixth session): every byte of
the last segment durable, and zeros known (`OsMeta.zf`) only from its end on. Then an fdatasync of an
idle tail (`Close` of a handle that never registered it: `WAL.Close.specOpening`) changes nothing the
invariant says but the segment's `OsMeta` (`OsMeta.synced`, `walInvBody_syncIdle`). Established by a
crash (the segments are their files' images, `initMeta`: zeros known from the last page's end), by
`Create`'s commit (its segment fsynced before the rename) and by `Close`'s unregistration (after its
`sync`: `TailMetaS`, `CloseHandle.lean`). -/
def TailSynced (lay : WalLay) : Prop :=
  ∀ g, lay.segs.getLast? = some g → (∀ y ∈ g.bs, y = durB y.1) ∧ ∀ z, g.om.zf = some z → g.bs.length ≤ z

/-- **A WAL's tail idle** (`WalTailIdle`'s, W3/W5 fifteenth session): no resize window open on its last
segment (`TailExact`), its last segment's stream all written (`wr` its length) and synced (`TailSynced`). What `ReadAll` needs
of a WAL no handle has registered: without it, it could succeed with the history's last records missing
(the reader stops at the zeros past `wr`). -/
def TailIdle (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) : Prop :=
  TailExact lay ∧ lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ TailSynced lay

/-- `TailIdle` depends on the WAL's history and metadata only. -/
theorem TailIdle.congr {C : WalCodec} {Mr : WalMarshal} {d d' : WalDur} {lay : WalLay}
    (h : TailIdle C Mr d lay) (hH : d'.H = d.H) (hmd : d'.metadata = d.metadata) :
    TailIdle C Mr d' lay := by
  have e : segRecs C Mr d' lay.cuts = segRecs C Mr d lay.cuts := by
    simp [segRecs, histM, hH, hmd]
  refine ⟨h.1, ?_, h.2.2⟩
  unfold segStream; rw [e]; exact h.2.1

/-- **Every WAL no handle has registered is idle** (`walTailsRes`'s third part; W3/W5 fifteenth session,
the coordinator's `WalTailIdle`): established by a crash (`CrashStart`: `wr = so = z0 = |stream|`), by
`Create`'s commit, and by a handle's unregistration (`Close`, W10's obligation); kept by every step (the
steps that change a WAL's layout or history are on registered WALs). -/
def WalTailIdle {G : Type} (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (T : GMap GoString G) : Prop :=
  ∀ dir d lay, T !! dir = none → s.wal !! dir = some d → Ls !! dir = some lay → TailIdle C Mr d lay

/-- **`WalTailIdle` as a registered WAL changes** (its tail's steps, its appends, its cut): nothing
changes elsewhere. -/
theorem WalTailIdle.of_reg {G : Type} {C : WalCodec} {Mr : WalMarshal} {s s' : AbsDiskState}
    {Ls Ls' : GMap GoString WalLay} {T : GMap GoString G} (dir : GoString) (hT : T !! dir ≠ none)
    (hs : ∀ k, k ≠ dir → s'.wal !! k = s.wal !! k) (hL : ∀ k, k ≠ dir → Ls' !! k = Ls !! k)
    (h : WalTailIdle C Mr s Ls T) : WalTailIdle C Mr s' Ls' T := by
  intro k d lay hk hd hl
  have hkd : k ≠ dir := by rintro rfl; exact hT hk
  rw [hs k hkd] at hd; rw [hL k hkd] at hl
  exact h k d lay hk hd hl

/-- **`WalTailIdle` as the WALs' states change but not their histories and metadata.** -/
theorem WalTailIdle.mono {G : Type} {C : WalCodec} {Mr : WalMarshal} {s s' : AbsDiskState}
    {Ls : GMap GoString WalLay} {T : GMap GoString G}
    (hs : ∀ dir d', s'.wal !! dir = some d' →
      ∃ d, s.wal !! dir = some d ∧ d'.H = d.H ∧ d'.metadata = d.metadata)
    (h : WalTailIdle C Mr s Ls T) : WalTailIdle C Mr s' Ls T := by
  intro k d' lay hk hd hl
  obtain ⟨d, hd0, hH, hmd⟩ := hs k d' hd
  exact (h k d lay hk hd0 hl).congr hH hmd

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

/-- **The open handles' tails** (W6): the invariant's half of the tails' authority, a change in
flight only on a registered tail (`TailsOnly`), and for each directory with an open handle, its WAL
and layout, the last segment, F-Z, the record boundary (`TailBound`), and the invariant's half of the
tail; every other WAL idle (`WalTailIdle`). -/
def walTailsRes (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) : IProp GF :=
  letI := walAllG (W := W)
  iprop(∃ T : GMap GoString GName, walTailsAuth (W := W) T ∗ ⌜TailsOnly T Ls F⌝ ∗
    ⌜WalTailIdle C Mr s Ls T⌝ ∗
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
      ∃ d', s'.wal !! dir = some d' ∧ d'.H = d.H ∧ d'.metadata = d.metadata)
    (h' : ∀ dir d', s'.wal !! dir = some d' →
      ∃ d, s.wal !! dir = some d ∧ d'.H = d.H ∧ d'.metadata = d.metadata) :
    walTailsRes (W := W) C Mr s Ls F ⊢ walTailsRes (W := W) C Mr s' Ls F := by
  unfold walTailsRes
  letI := walAllG (W := W)
  iintro ⟨%T, Ha, %Ho, %Hi, Hm⟩
  iexists T
  iframe Ha
  isplitr
  · ipureintro; exact Ho
  isplitr
  · ipureintro; exact Hi.mono h'
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

/-- **No change in flight while no tail is registered** (the program's half of the tails' authority
empty: the lock token's, or a holder's of what is out with no tail record). -/
theorem walTailsRes_none (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) ∅ -∗
      ⌜∀ i, F !! i = none⌝ ∗ walTailsRes (W := W) C Mr s Ls F ∗ walTailsFrag (W := W) ∅ := by
  unfold walTailsRes
  iintro ⟨%T, Ha, %Ho, %Hi, Hm⟩ Hf
  icases walTails_agree (W := W) T ∅ $$ Ha Hf with %hT
  subst hT
  iframe Hf
  isplitr
  · ipureintro; exact Ho.none_of_empty
  iexists ∅
  iframe Ha Hm
  ipureintro; exact ⟨Ho, Hi⟩

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

theorem walOsSpine_timeless (j : Ino) (cs : List GoString) (dq : DFrac) (j' : Ino) :
    Timeless (osSpine (L := L) j cs dq j') := by
  induction cs generalizing j with
  | nil => rw [osSpine_nil]; infer_instance
  | cons c cs ih =>
    rw [osSpine_cons]
    haveI := fun J => ih J
    haveI : ∀ (h : NamesH), Timeless (osNames (L := L) j (.only [c]) dq h) := fun _ => by
      unfold osNames; split <;> infer_instance
    infer_instance

instance walOsPathS_timeless (R : Roots) (p : GoString) (dq : DFrac) (j : Ino) :
    Timeless (osPathS (L := L) R p dq j) := by
  unfold osPathS
  haveI := walOsSpine_timeless (L := L)
  infer_instance

/-- **A registered WAL name's claim, as the invariant keeps it** (G-spine; W1 log, thirteenth session):
a fraction `q` of the program's half of the claim `(jr, .only [nm], hn)` on the WAL's name alone (the
invariant holds its other half among its claims, `osClaims`), the name valid for the system calls
(`NameOk`), a WAL name, and holding the WAL's directory (`lay.j` of the layout named `nm`). The rest of
the program's half is lent out, in paths to the WAL's directory, never returned: the claim never changes
again in the generation (a registered WAL's name is renamed onto or away by no WAL function; a change
needs the whole claim), so `hn` is fixed and its holders need not give it back. -/
def nameShare (jr : Ino) (Ls : GMap GoString WalLay) (nm : GoString) : IProp GF :=
  iprop(∃ (q : Qp) (hn : NamesH), osNames (L := L) jr (.only [nm]) (DFrac.own q) hn ∗
    ⌜NameOk nm ∧ walNameOk nm ∧
      ∀ dir lay, Ls !! dir = some lay → lay.nm = nm → hn.cur !! nm = some (.dir lay.j)⌝)

/-- **The WALs' name claims** (G-spine, framed; W1 log, thirteenth session). A path to a WAL directory
`dir = r/nm` is a spine through a fraction of a claim on `nm` alone (`osPathS_child`), so each WAL's name
is **registered** (in `Wn`): split out of the area claim into its own claim `(jr, .only [nm], hn)`, the
invariant's half among its claims, a fraction of the program's half here (`nameShare`), lent by halves
to whoever asks with the WAL's key (`walDirKey`: the handle's `walDirH`, the file pipeline,
`OpenDir(w.dir)`, `ReadDir(dir)`; `NameClaims.lean`), and never returned. Every present WAL is registered
but the one `Create` has committed and not yet registered (`o`: `walNamesAuth o`, the other half the lock
token's, `none`, or that `Create`'s, `some dir`; until it registers, `Create` holds the whole program
half, which its cleanup's rename needs). Each registered name is a present WAL's (`walSplitAuth Wn`: the
other half is `walAreaRes`'s, whose area claim holds every WAL name but these). And a fraction of the
area's spine, lent by halves with the name's: a handle keeps its path past the call that opened it,
whose caller gets its own spine back whole. Independent of the claims list (a step changing other
claims leaves it as it is). -/
def walNamesRes (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay) : IProp GF :=
  iprop(∃ (o : Option GoString) (Wn : List GoString),
    walNamesAuth (W := W) o ∗ walSplitAuth (W := W) Wn ∗
    ⌜(∀ nm ∈ Wn, ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm) ∧
      ∀ dir lay, Ls !! dir = some lay → o ≠ some dir → lay.nm ∈ Wn⌝ ∗
    (∃ q : Qp, osPathS (L := L) R r (DFrac.own q) jr) ∗
    [∗list] nm ∈ Wn, nameShare (L := L) jr Ls nm)

instance walNamesRes_timeless (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay) :
    Timeless (walNamesRes (L := L) (W := W) R jr r Ls) := by
  haveI : ∀ (j : Ino) (N : NameSet) (q : DFrac) (h : NamesH), Timeless (osNames (L := L) j N q h) :=
    fun _ _ _ _ => by unfold osNames; split <;> infer_instance
  haveI : ∀ nm, Timeless (nameShare (L := L) jr Ls nm) := fun _ => by
    unfold nameShare; infer_instance
  unfold walNamesRes; infer_instance

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
    ⌜WalsAt jr Ls cl⌝ ∗ walNamesRes (L := L) (W := W) R jr r Ls ∗ ⌜WalsBounded s⌝)

instance walInvBody_timeless (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) : Timeless (walInvBody (L := L) (W := W) C Mr R jr r s) := by
  haveI := walNamesRes_timeless (L := L) (W := W) R jr r
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

/-- **The metadata bound read off the invariant** (`WalsBounded`; `ReadAll`'s). -/
theorem walInvBody_bounded (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) :
    walInvBody (L := L) (W := W) C Mr R jr r s ⊢
      ⌜WalsBounded s⌝ ∗ walInvBody (L := L) (W := W) C Mr R jr r s := by
  iintro Hb
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Har, Hcl, Hcm, Hlays, Hok, Hco, HCR, Htl, Hab, Hnm, Hpk, Hdk,
    HAt, Hnms, %Hbd⟩
  isplitr
  · ipureintro; exact Hbd
  iexists Ls, cl, n, F
  iframe
  ipureintro; exact Hbd

/-- A name's share under a change of layouts keeping every layout of its name's directory. -/
theorem nameShare_mono (jr : Ino) (Ls Ls' : GMap GoString WalLay) (nm : GoString)
    (h : ∀ dir lay', Ls' !! dir = some lay' → lay'.nm = nm → ∃ lay, Ls !! dir = some lay ∧
      lay.nm = nm ∧ lay.j = lay'.j) :
    nameShare (L := L) jr Ls nm ⊢ nameShare (L := L) jr Ls' nm := by
  unfold nameShare
  iintro ⟨%q, %hn, H, %hf⟩
  iexists q, hn
  iframe H
  ipureintro
  refine ⟨hf.1, hf.2.1, fun dir lay' hl' he => ?_⟩
  obtain ⟨lay, hl, hnm, hj⟩ := h dir lay' hl' he
  rw [← hj]; exact hf.2.2 dir lay hl hnm

/-- **A new WAL, committed by `Create`** (its rename; the lock taken, `walNamesFrag none`): its name not
yet registered (the pending registration set to `dir`, until `Create` registers it); no other layout has
its name. -/
theorem walNamesRes_addWal (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (dir : GoString) (lay : WalLay) (hLd : Ls !! dir = none)
    (hnew : ∀ dir' lay', Ls !! dir' = some lay' → lay'.nm ≠ lay.nm) :
    ⊢ walNamesRes (L := L) (W := W) R jr r Ls -∗ walNamesFrag (W := W) none ==∗
      walNamesRes (L := L) (W := W) R jr r (<[dir := lay]> Ls) ∗ walNamesFrag (W := W) (some dir) := by
  unfold walNamesRes
  iintro ⟨%o, %Wn, Ha, Hs, %hf, Hsp, Hl⟩ Hf
  icases walNames_agree (W := W) o none $$ Ha Hf with %ho
  subst ho
  imod walNames_set (W := W) none none (some dir) $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Hf
  iexists some dir, Wn
  iframe Ha Hs Hsp
  isplitr
  · ipureintro
    refine ⟨fun nm hm => ?_, fun dir' l hl' ho => ?_⟩
    · obtain ⟨d', l, hl', rfl⟩ := hf.1 nm hm
      have e : d' ≠ dir := by rintro rfl; rw [hLd] at hl'; cases hl'
      exact ⟨d', l, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl', rfl⟩
    · have e : dir' ≠ dir := fun e => ho (by rw [e])
      rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact hf.2 dir' l hl' (by simp)
  iapply BigSepL.bigSepL_mono (fun {k nm} hk => ?_) $$ Hl
  refine nameShare_mono jr Ls _ nm (fun d' l' hl' he => ?_)
  by_cases e : d' = dir
  · subst e
    rw [GMap.lookup_insert_eq] at hl'; cases hl'
    obtain ⟨d2, l2, hl2, hn2⟩ := hf.1 nm (List.mem_of_getElem? hk)
    exact absurd (hn2.trans he.symm) (hnew d2 l2 hl2)
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
    exact ⟨l', hl', he, rfl⟩

/-- **`walNamesRes` with a layout replaced by one of the same name and directory** (the tail's steps,
a cut). -/
theorem walNamesRes_insert (R : Roots) (jr : Ino) (r : GoString) (Ls : GMap GoString WalLay)
    (dir : GoString) (lay lay' : WalLay) (hl : Ls !! dir = some lay)
    (hnm : lay'.nm = lay.nm) (hj : lay'.j = lay.j) :
    walNamesRes (L := L) (W := W) R jr r Ls ⊢ walNamesRes (L := L) (W := W) R jr r (<[dir := lay']> Ls) := by
  unfold walNamesRes
  iintro ⟨%o, %Wn, Ha, Hs, %hf, Hsp, Hl⟩
  iexists o, Wn
  iframe Ha Hs Hsp
  isplitr
  · ipureintro
    refine ⟨fun nm hm => ?_, fun dir' l hl' ho => ?_⟩
    · obtain ⟨d', l, hl', rfl⟩ := hf.1 nm hm
      by_cases e : d' = dir
      · subst e; rw [hl] at hl'; cases hl'
        exact ⟨d', lay', GMap.lookup_insert_eq _ _ _, hnm⟩
      · exact ⟨d', l, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl', rfl⟩
    · by_cases e : dir' = dir
      · subst e; rw [GMap.lookup_insert_eq] at hl'; cases hl'
        rw [hnm]; exact hf.2 dir' lay hl ho
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
        exact hf.2 dir' l hl' ho
  iapply BigSepL.bigSepL_mono_of_forall (fun {k nm} => ?_) $$ Hl
  refine nameShare_mono jr Ls _ nm (fun d' l' hl' he => ?_)
  by_cases e : d' = dir
  · subst e
    rw [GMap.lookup_insert_eq] at hl'; cases hl'
    exact ⟨lay, hl, hnm ▸ he, hj.symm⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
    exact ⟨l', hl', he, rfl⟩

end inv

end WalFs
end EtcdGrove
end Perennial

end
