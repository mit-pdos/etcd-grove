/- Lean-first (no Rocq counterpart).

# The WAL's crash lemma over `fsExt` (`notes/wal-fsext-plan.md`, §2.2; W1)

`walInv_crash`: what a client's crash obligation (at `⊤`, `goose_crash_adequacy`) gets of the WAL
from the old generation's invariant (`walInv`, opened with the generation's crash token, so that it
stays closed with the token), the generation's `crashRest` (the tree untaken) and W1 (the crash
premise `Q` implies it): a fresh generation of the WAL's ghost names, the crash view
(`walCrashWal`: the old ghost authorities at the old real state `s`, the new program's map at the
crashed state `s'`, `walStCrash s s'`: each WAL a `walCrash` of its old state, which is no longer a
trusted relation), the new generation's start (`walStart`: its ghost authorities, every segment's
whole resources from the crash's `fileStart`, the layouts' static relation over the crashed tree),
the new lock and crash tokens, and `crashRest` back with the segments taken.

The `_keep` lemmas (`walDiskAt_crash_keep`, `walDiskAt_crash_any_keep`, `walDiskAt_crash_any_keep0`,
`walAbsent_crash_keep`, `dirDurable_crash_keep`, `walArea_crash_keep`) are `AbsDisk/Specs.lean`'s, with
the same conclusions, over `walCrashWal`: what the tester's `tester_crash` uses.

`walInv_alloc`: the new generation's invariant from its start, once the tree is in shared mode and
the WAL's names are claimed (`wp_osShare`, `osNames_split`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **What a generation's start says of the WALs** (pure), the tree being `m` (nothing logged):
each WAL of `s` has a layout whose directory is at its name in the area, with the static relation
over the directory's entries, every segment's bytes durable and nothing appended; a directory of
the area with no WAL holds no `.wal` file; every durable directory resolves. -/
def WalsStart (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (m : Tree) : Prop :=
  (∀ dir d, s.wal !! dir = some d → ∃ lay nm, Ls !! dir = some lay ∧ InArea s.area dir nm ∧
    lay.jr = jr ∧ lay.nm = nm ∧ m.entry jr nm = some (.dir lay.j) ∧
    WalAbsD C Mr d lay (entsOf m lay.j) ∧
    RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)) ∧
    lay.wr = lay.so ∧ lay.wr = lay.z0 ∧ lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length ∧
    (∀ g, lay.segs.getLast? = some g → g.bs = lay.old.map durB)) ∧
  (∀ dir, s.wal !! dir = none → Ls !! dir = none) ∧
  (∀ dir nm, InArea s.area dir nm → s.wal !! dir = none → ∀ J, m.entry jr nm = some (.dir J) →
    walInos (entsOf m J) = []) ∧
  (∀ dd, s.dirs !! dd = some () → ∃ J, lookupH R (m, []) dd = some (.dir J))

end pure

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- Every named segment's whole resources (its `OsMeta` and all its bytes), generation `L`. -/
def laysFull (L : GooseLocalGS GF) (Ls : GMap GoString WalLay) : IProp GF :=
  iprop([∗map] _dir ↦ lay ∈ Ls, [∗list] g ∈ lay.segs,
    osMeta (L := L) g.ino (DFrac.own 1) g.om ∗ osBytes (L := L) g.ino 0 (DFrac.own 1) g.bs)

/-- **The WAL's start in the generation `(L, W)`**, the WAL state being `s` and the tree `m`: the
ghost authorities; the files `is`, each with its start resources (as a crash's `fileStart` gives
them: `fo`); the layouts (`WalsStart`), every segment one of `is`, its `OsMeta` and bytes those of its
file on disk. -/
def walStart (L : GooseLocalGS GF) (W : WalGS GF) (C : WalCodec) (Mr : WalMarshal) (R : Roots)
    (jr : Ino) (r : GoString) (s : AbsDiskState) (m : Tree) : IProp GF :=
  iprop(∃ (Ls : GMap GoString WalLay) (is : List Ino) (fo : Ino → Option Fs.OsFile),
    walGhost (W := W) s ∗ ⌜s.area = r⌝ ∗ ([∗list] i ∈ is, osFileStartO (L := L) i (fo i)) ∗
    ⌜is.Nodup ∧ WalsStart C Mr R jr s Ls m ∧ ∀ dir lay, Ls !! dir = some lay → ∀ g ∈ lay.segs,
      g.ino ∈ is ∧ ∃ f, fo g.ino = some f ∧ g.om = initMeta f ∧ g.bs = f.contents.map durB⌝)

/-- **The crash view** (as `absDiskCrashWal`): the old generation's ghost authorities at the old
real state `s`, the new generation's program map at the crashed state `s'` and its fact. -/
def walCrashWal (W W' : WalGS GF) : IProp GF :=
  iprop(∃ s s' : AbsDiskState, ⌜walStCrash s s'⌝ ∗ walGhost (W := W) s ∗
    walOwn (W := W') s'.wal ∗ walPast (W := W') s')

/-- **The crashed state's files, all at once** (an I3 gap, `notes/wal-fsext-plan.md` W1 log): for
the files `gs` (inodes not taken, with halves of their `OsMeta` and runs), one crashed state `st'`
for all of them, the crash premise `Q` of it, its tree the new history's, each file as
`FileCrashedR` of its halves and its candidates the state's (no sync cut), each new file's start
resources. `crashRest_take_runs_keep` gives each file its own existential state, which a premise
over several files (W1) cannot use. Belongs in `GooseLang/Ext/Fs/CrashTok.lean`. -/
theorem crashRest_take_files (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (gs : List SegG)
    (hD : ∀ g ∈ gs, g.ino ∉ D) (hnd : (gs.map (·.ino)).Nodup) (hcut : ∀ g ∈ gs, g.om.cut = none) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      ([∗list] g ∈ gs, segRes (L := L) g) -∗
      ∃ (st st' : Fs.OsState), ⌜Q st st' ∧ st'.fs.treeDur = V'.now ∧
          ∀ g ∈ gs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (st'.fs.files !! g.ino) ∧
            (Named V'.now g.ino → (st'.fs.files !! g.ino).isSome) ∧
            ∃ f, st.fs.files !! g.ino = some f ∧ ∀ b (y : ByteG), g.bs[b]? = some y → f.cand b = y.2⌝ ∗
        ([∗list] i ∈ gs.map (·.ino), osFileStartO (L := L') i (st'.fs.files !! i)) ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (gs.map (·.ino) ++ D) tt V' ∗
        ([∗list] g ∈ gs, segRes (L := L) g) := by
  sorry

/-- **The crash's pure core** (plan §2.2): from what the invariant says of the WALs, what a crash of
the claims allows of the tree (`m'`), what the crash did to each segment (`FileCrashedR` of its
halves, its candidates the state's) and W1: the crashed WAL state `s'` (`walStCrash s s'`) and its
layouts over `m'` and the crashed files. Each WAL's crash condition gives its `CrashTo` (W1 over the
ghost candidates, `W1G`, from W1 over the state's); the new layout keeps the cuts, the kept segments
with their files' start resources, the last file's image as the bytes under its stream. -/
theorem walCrash_pure (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (m' : Tree)
    (st st' : Fs.OsState) (hok : WalsOk C Mr R jr s Ls cl n) (hk : walKeysInArea s)
    (hreg : RegionCrashed cl n m') (htree : st'.fs.treeDur = m') (hw1 : W1 C st st')
    (hfiles : ∀ g ∈ segsAll Ls,
      FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (st'.fs.files !! g.ino) ∧
      (Named m' g.ino → (st'.fs.files !! g.ino).isSome) ∧
      ∃ f, st.fs.files !! g.ino = some f ∧ ∀ b (y : ByteG), g.bs[b]? = some y → f.cand b = y.2) :
    ∃ (s' : AbsDiskState) (Ls' : GMap GoString WalLay), walStCrash s s' ∧ s'.area = s.area ∧
      walKeysInArea s' ∧ WalsStart C Mr R jr s' Ls' m' ∧
      ∀ dir lay, Ls' !! dir = some lay → ∀ g ∈ lay.segs, g.ino ∈ (segsAll Ls).map (·.ino) ∧
        ∃ f, st'.fs.files !! g.ino = some f ∧ g.om = initMeta f ∧ g.bs = f.contents.map durB := by
  sorry

theorem walsOk_nodup {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (h : WalsOk C Mr R jr s Ls cl n) :
    ((segsAll Ls).map (·.ino)).Nodup := h.2.2.1

theorem walsOk_cut {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (h : WalsOk C Mr R jr s Ls cl n) :
    ∀ g ∈ segsAll Ls, g.om.cut = none := by
  sorry

/-- **The WAL's crash** (plan §2.2): from the old generation's invariant, its crash token, the shared
mode's invariant, the generation's `crashRest` (the tree untaken) and W1 (`hQ`): a new generation of
the WAL's names, the crash view, the new generation's start over the crashed tree, its lock and crash
tokens, and `crashRest` back (the segments taken, the tree not). -/
theorem walInv_crash (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (Q : Fs.OsState → Fs.OsState → Prop)
    (hQ : ∀ st st', Q st st' → W1 C st st') (hPre : AbsDiskGpreS GF) (L L' : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (V' : Hist) (E : CoPset)
    (hE : ↑walN ⊆ E) (hE' : ↑osShN ⊆ E) (hdisj : walN ## osShN) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ walCrashTok (W := W) -∗ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) [] false V' ={E}=∗
      ∃ (W' : WalGS GF) (s' : AbsDiskState) (D : List Ino),
        walCrashWal W W' ∗ ⌜s'.area = r⌝ ∗ walStart L' W' C Mr R jr r s' V'.now ∗
        walPast (W := W') s' ∗ walUnlockedTok (W := W') ∗ walCrashTok (W := W') ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' := by
  iintro #Hinv Htok #Hsh Hcr
  -- open the old invariant and close it with the crash token
  unfold walInv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (Hb | >Ht)
  rotate_left
  · iexfalso; iapply walCrashTok_excl $$ Htok Ht
  imod Hclose $$ [Htok] with -
  · inext; iright; iexact Htok
  icases Hb with ⟨%s, >Hb⟩
  iunfold walInvBody at Hb
  icases Hb with ⟨%Ls, %cl, %n, Hg, %Har, Hcl, #Hcm, Hlays, %Hok⟩
  icases walGhost_keys_keep (W := W) s $$ Hg with ⟨Hg, %hk⟩
  -- the tree: what the claims allow
  imod crashRest_region Q L L' [] false V' R (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) n E
    hE' $$ Hsh Hcr Hcl Hcm with ⟨%Hreg, Hcr, -⟩
  have hcl : ∀ l : List Claim, (l.map (fun c => (c, DFrac.own (1 : Qp).half))).map (·.1) = l :=
    fun l => by
      induction l with
      | nil => rfl
      | cons c l ih => simp only [List.map_cons]; rw [ih]
  rw [hcl cl] at Hreg
  -- the segments
  icases (laysRes_list (L := L) Ls).1 $$ Hlays with Hlays
  icases crashRest_take_files Q L L' [] false V' (segsAll Ls) (by simp) (walsOk_nodup Hok)
    (walsOk_cut Hok) $$ Hcr Hlays with ⟨%st, %st', %Hfs, Hstarts, Hcr, -⟩
  obtain ⟨hQs, htree, hfiles⟩ := Hfs
  obtain ⟨s', Ls', hcrash, harea', hk', hstart, hsegs⟩ :=
    walCrash_pure C hC Mr R jr s Ls cl n V'.now st st' Hok hk Hreg htree (hQ _ _ hQs) hfiles
  -- the new generation's ghost state
  imod walGhost_init hPre s' hk' with ⟨%W', Hg', HM', #Hp', Hu', Hc'⟩
  imodintro
  iexists W', s', ((segsAll Ls).map (·.ino) ++ [])
  iframe Hu' Hc' Hcr Hp'
  isplitl [Hg HM']
  · unfold walCrashWal
    iexists s, s'
    iframe Hg HM' Hp'
    ipureintro; exact hcrash
  isplitr
  · ipureintro; rw [harea', Har]
  unfold walStart
  iexists Ls', (segsAll Ls).map (·.ino), (fun i => st'.fs.files !! i)
  iframe Hg' Hstarts
  ipureintro
  exact ⟨by rw [harea', Har], walsOk_nodup Hok, hstart, hsegs⟩

/-- **The new generation's invariant**, in the tree's shared mode, from the WAL's start: the
claims `cl` (whole) on each WAL directory's names and on the area's names of the WALs, as the
shared mode's boot history `V` (nothing logged) has them; the invariant takes half of each, the
program the other halves, the commit bound 0. -/
theorem walInv_alloc (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (L : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState) (V : Hist)
    (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (hcov : ∀ lay ∈ (cl.map (·.1)), True) (E : CoPset) :
    ⊢ osSharedInv (L := L) R -∗ walStart L W C Mr R jr r s V.now -∗
      osClaims L (cl.map (fun c => (c, DFrac.own 1))) ={E}=∗
      walInv (L := L) (W := W) C Mr R jr r ∗
      osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) := by
  sorry

/-! ## The `_keep` lemmas (as `AbsDisk/Specs.lean`'s, over `walCrashWal`) -/

variable (W W' : WalGS GF)

/-- **The crash view, keeping the old program's map.** -/
theorem walCrash_view_keep (M : GMap GoString WalDur) :
    ⊢@{IProp GF} walCrashWal W W' -∗ walOwn (W := W) M -∗ walOwn (W := W) M ∗
      ∃ s s' : AbsDiskState, ⌜walStCrash s s' ∧ walMapLe M s.wal⌝ ∗
        walGhost (W := W) s ∗ walOwn (W := W') s'.wal ∗ walPast (W := W') s' := by
  sorry

theorem walDiskAt_crash_keep (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAt (W := W) dir d -∗ walSyncedLb (W := W) dir n -∗ walNamed (W := W) dir -∗
      walDiskAt (W := W) dir d ∗ ∃ (I : List (WalOpG WalEnt)) (k : Nat),
        ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
        walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗
        walSyncedLb (W := W') dir n ∗ walNamed (W := W') dir := by
  sorry

theorem walDiskAt_crash_any_keep (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAt (W := W) dir d -∗ walSyncedLb (W := W) dir n -∗
      walDiskAt (W := W) dir d ∗ ((walAbsent (W := W') dir ∗ ⌜d.named = false⌝) ∨
        ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
          walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗ walSyncedLb (W := W') dir n) := by
  sorry

theorem walDiskAt_crash_any_keep0 (dir : GoString) (d : WalDur) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAt (W := W) dir d -∗
      walDiskAt (W := W) dir d ∗ ((walAbsent (W := W') dir ∗ ⌜d.named = false⌝) ∨
        ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H 0 I ∧ k ≤ min d.pur I.length⌝ ∗
          walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }) := by
  sorry

theorem walAbsent_crash_keep (dir : GoString) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walAbsent (W := W) dir -∗ walAbsent (W := W) dir ∗ walAbsent (W := W') dir := by
  sorry

theorem dirDurable_crash_keep (d : GoString) :
    ⊢@{IProp GF} walCrashWal W W' -∗ dirDurable (W := W) d -∗
      walCrashWal W W' ∗ dirDurable (W := W') d := by
  sorry

theorem walArea_crash_keep (r : GoString) :
    ⊢@{IProp GF} walCrashWal W W' -∗ walArea (W := W) r -∗
      walCrashWal W W' ∗ walArea (W := W') r := by
  sorry

end crash

end WalFs
end EtcdGrove
end Perennial

end
