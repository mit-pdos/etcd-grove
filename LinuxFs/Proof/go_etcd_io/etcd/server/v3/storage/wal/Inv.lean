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

/-- **A write in flight on a segment** (W6): its token `t`, offset `off`, data and change number
`n` (`wp_osPWriteStart`'s), and the segment's `OsMeta` `m` and bytes `bs` before it. -/
structure SegFl where
  t : Nat
  off : Nat
  data : List w8
  n : Nat
  m : OsMeta
  bs : List ByteG

instance SegFl.countable : Pos.Countable SegFl :=
  Pos.Countable.ofInjective
    (fun fl => Pos.Countable.encode (fl.t, fl.off, fl.data, fl.n, fl.m, fl.bs))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; subst h1 h2 h3 h4 h5 h6; rfl)

/-- **The segment `g` as the write in flight `fl` announced it**: the write inside the segment
(the WAL writes its tail inside the preallocated file), not empty; `g`'s `OsMeta` the token's
(`cfMeta`), its bytes `fl.bs` with the data's candidates added to the written range (`pwAnn`). -/
def SegFl.Ok (fl : SegFl) (g : SegG) : Prop :=
  fl.off + fl.data.length ≤ fl.m.size ∧ fl.data ≠ [] ∧ fl.bs.length = fl.m.size ∧
  fl.m.cut = none ∧ g.om = cfMeta fl.m fl.off fl.data.length ∧
  g.bs = fl.bs.take (cfLo fl.m fl.off) ++
    pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length) ++
    fl.bs.drop (cfHi fl.m fl.off fl.data.length)

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

/-- **The WALs being created are renamed in claims the invariant holds** (W4, framed): each entry
`dir ↦ (N, h)` of the creating map is a claim `(jr, N, h)` of the area directory among `cl`,
coherent, and no other claim of `jr` among `cl` holds one of its names (what the file system's
shared invariant says of claims, `NamesCoh.disj`, recorded where the token is made: the rename's
commit, inside an `os` call's update, cannot open that invariant). -/
def CreatingOk (jr : Ino) (cl : List Claim) (CR : GMap GoString (NameSet × NamesH)) : Prop :=
  ∀ dir N h, CR !! dir = some (N, h) → (jr, N, h) ∈ cl ∧ ClaimCoh h jr N ∧
    ∀ c ∈ cl, c ≠ (jr, N, h) → c.1 = jr → ∀ b, N.Mem b → ¬ c.2.1.Mem b

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

/-- **The invariant's part of a segment, a write maybe in flight on it** (`F` by inode): idle, its
halves (`segRes`); with a write in flight, the write's token and the halves of the bytes around it,
the layout holding the segment as the write announced it (`SegFl.Ok`). -/
def segResF (F : GMap Ino SegFl) (g : SegG) : IProp GF :=
  match F !! g.ino with
  | none => segRes (L := L) g
  | some fl => iprop(pwTok (L := L) fl.t g.ino fl.off fl.data fl.m
        (cfRange fl.m fl.bs fl.off fl.data.length) fl.n ∗
      osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) (fl.bs.take (cfLo fl.m fl.off)) ∗
      osBytes (L := L) g.ino (cfHi fl.m fl.off fl.data.length) (DFrac.own (1 : Qp).half)
        (fl.bs.drop (cfHi fl.m fl.off fl.data.length)) ∗ ⌜fl.Ok g⌝)

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
  unfold segResF segRes pwTok osTok osMeta; split <;> infer_instance

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

/-- **The WAL invariant's contents**, the real WAL state being `s`. -/
def walInvBody (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) : IProp GF :=
  iprop(∃ (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (F : GMap Ino SegFl),
    walGhost (W := W) s ∗ ⌜s.area = r⌝ ∗
    osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗ osCommitLb (L := L) n ∗
    laysResF (L := L) F Ls ∗ ⌜WalsOk C Mr R jr s Ls cl n⌝ ∗ ⌜WalsCreateOk jr cl⌝ ∗
    (∃ CR, walCreatingAuth (W := W) CR ∗ ⌜CreatingOk jr cl CR⌝) ∗ walTailsRes (W := W) C Mr s Ls F ∗
    ⌜AbsentNone s jr cl n ∧ DirsAvoid R jr s⌝)

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
