/- Lean-first (no Rocq counterpart).

# The WAL's crash lemma over `fsExt` (`notes/wal-fsext-plan.md`, §2.2; W1)

`walInv_crash`: what a client's crash obligation (at `⊤`, `goose_crash_adequacy`) gets of the WAL
from the old generation's invariant (`walInv`, opened with the generation's `crashed`, which the
crash adequacy theorem gives, and the WAL's crash token, so that it stays closed with them), the
generation's `crashRest` (the tree untaken) and W1 (the crash premise `Q` implies it): a fresh generation of the WAL's ghost names, the crash view
(`walCrashWal`: the old ghost authorities at the old real state `s`, the new program's map at the
crashed state `s'`, `walStCrash s s'`: each WAL a `walCrash` of its old state, which is no longer a
trusted relation), the new generation's start (`walStart`: its ghost authorities, every segment's
whole resources from the crash's `fileStart`, the layouts' static relation over the crashed tree),
the new lock and crash tokens, and `crashRest` back with the segments taken.

The `_keep` lemmas (`walDiskAt_crash_keep`, `walDiskAt_crash_any_keep`, `walDiskAt_crash_any_keep0`,
`walAbsent_crash_keep`, `dirDurable_crash_keep`, `walArea_crash_keep`) are `AbsDisk/Specs.lean`'s, with
the same conclusions, over `walCrashWal`: what the tester's `tester_crash` uses.

`walInv_alloc`: the new generation's invariant from its start, once the WAL's names are claimed in
the tree's shared view (`osShared`, `osNames_split`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashStart
public import GooseLang.Ext.Fs.CrashTakeFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashTakeSeg
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootCrashPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashTakeNamed

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

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
them: `fo`, each the tree names on disk); the layouts (`WalsStart`), every segment one of `is`, its `OsMeta` and bytes those of its
file on disk, the segments' inodes distinct. -/
def walStart (L : GooseLocalGS GF) (W : WalGS GF) (C : WalCodec) (Mr : WalMarshal) (R : Roots)
    (jr : Ino) (r : GoString) (s : AbsDiskState) (m : Tree) : IProp GF :=
  iprop(∃ (Ls : GMap GoString WalLay) (is : List Ino) (fo : Ino → Option Fs.OsFile),
    walGhost (W := W) s ∗ walCreatingAuth (W := W) ∅ ∗ walTailsAuth (W := W) ∅ ∗
    walParkAuth (W := W) true ∗ walDirKeysAuth (W := W) ∅ ∗ walCutAuth (W := W) none ∗
    walOutAuth (W := W) WalOut.empty ∗ walNamesAuth (W := W) none ∗ walSplitAuth (W := W) [] ∗
    walSplitFrag (W := W) [] ∗ walLentAuth (W := W) ∅ ∗ ⌜s.area = r⌝ ∗
    ([∗list] i ∈ is, osFileStartO (L := L) i (fo i)) ∗
    ⌜is.Nodup ∧ (∀ i ∈ is, Named m i → (fo i).isSome) ∧
      ((segsAll Ls).map (·.ino)).Nodup ∧ WalsStart C Mr R jr s Ls m ∧
      ∀ dir lay, Ls !! dir = some lay → ∀ g ∈ lay.segs,
      g.ino ∈ is ∧ ∃ f, fo g.ino = some f ∧ g.om = initMeta f ∧ g.bs = f.contents.map durB⌝)

/-- **The crash view** (as `absDiskCrashWal`): the old generation's ghost authorities at the old
real state `s`, the new generation's program map at the crashed state `s'` and its fact. -/
def walCrashWal (W W' : WalGS GF) : IProp GF :=
  iprop(∃ s s' : AbsDiskState, ⌜walStCrash s s'⌝ ∗ walGhost (W := W) s ∗
    walOwn (W := W') s'.wal ∗ walPast (W := W') s')

/-- **A crash keeps the WALs' step bound**: each history becomes an image of it, no longer
(`walImg_length_le`); no WAL appears. -/
theorem walsStepped_crash {s s' : AbsDiskState} {n : Nat} (hc : walStCrash s s')
    (h : WalsStepped s n) : WalsStepped s' n := by
  intro dir d' hd'
  cases hd : s.wal !! dir with
  | none => rw [hc.2.2.2 dir hd] at hd'; cases hd'
  | some d =>
    rcases hc.2.2.1 dir d hd with ⟨-, h0⟩ | ⟨I, k, hI, -, h1⟩
    · rw [h0] at hd'; cases hd'
    · rw [h1] at hd'; cases hd'; exact Nat.le_trans (walImg_length_le hI) (h dir d hd)

theorem walsOk_nodup {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (h : WalsOk C Mr R jr s Ls cl n) :
    ((segsAll Ls).map (·.ino)).Nodup := h.2.2.1

theorem walsOk_cut {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (h : WalsOk C Mr R jr s Ls cl n) :
    ∀ g ∈ segsAll Ls, g.om.cut = none := h.2.2.2.1

/-- **A file a crash kept is held whole once taken** (`osFileStart`, as a generation's `fileStart`
gives it: `initMeta`, its bytes durable): `trFile i False`. What the boot program gives of a leftover
file the WAL's temporary names hold: a pipeline's `N.tmp` (`walTmpsRes`'s `tmpEnt`) and a temporary
directory's `.touch` (`walAreaRes`'s `tmpClTouch`, `wal-leaf5`: the area's establishment, C6, takes each
such file from the crash's `crashRest`). -/
theorem osFileStart_trFile (L : GooseLocalGS GF) (i : Ino) (f : Fs.OsFile) :
    osFileStart (L := L) i f ⊢ trFile (hG := ⟨G, L⟩) i False := by
  unfold osFileStart trFile
  iintro ⟨Hm, Hb⟩
  iexists initMeta f, f.contents.map durB
  iframe Hm Hb
  isplitl []
  · unfold mcellsAny
    exact BigSepM.bigSepM_empty.2
  ipureintro
  refine ⟨by simp [initMeta, contents_length], fun h => h.elim, rfl, rfl, Nat.le_refl _,
    ⟨pageEnd f.size, rfl, le_pageEnd _⟩, fun h => h.elim⟩

/-- **A file of the crashed tree is named in a directory under the area** (an entry of `jr` names its
directory): the files the crash lemma takes are such. -/
def InAreaDir (m : Tree) (jr i : Ino) : Prop :=
  ∃ J b a, m.entry J b = some (.file i) ∧ m.entry jr a = some (.dir J)

/-- **After a crash, every WAL directory at a WAL name of the area holds no directory but at the
pipeline's names** (pure; the crash boot's `BootFo`, its WAL-directory part off the pipeline names): the
directory at the name is a new layout's (`WalsStart`), an old layout's directory (`walCrash_pure`), whose
claim on every name but the pipeline's (`DirKeysOk`'s `DirClaimExcl`: `.except walTmps`) leaves no
directory a crash may keep (`WalsNamed`'s `HistFoN`). -/
theorem crash_noDirX {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s s' : AbsDiskState}
    {Ls Ls' : GMap GoString WalLay} {cl : List Claim} {n : Nat} {K : GMap GoString (Ino × List GoString)}
    {cp : Option GoString} {m' : Tree} (hnm : WalsNamed Ls cl n) (hDK : DirKeysOk C Mr jr s Ls cl n K cp)
    (hreg : RegionCrashed cl n m') (hst : WalsStart C Mr R jr s' Ls' m')
    (hLL : ∀ dir lay', Ls' !! dir = some lay' → ∃ lay, Ls !! dir = some lay ∧ lay'.j = lay.j) :
    ∀ nm J, walNameOk nm → m'.entry jr nm = some (.dir J) → NoDirX (entsOf m' J) := by
  intro nm J hw he b J' hb hd
  have hin : InArea s'.area (s'.area ++ go!"/" ++ nm) nm := ⟨hw, rfl⟩
  cases hs : s'.wal !! (s'.area ++ go!"/" ++ nm) with
  | none => rw [hst.2.2.1 _ nm hin hs] at he; cases he
  | some d =>
    obtain ⟨lay', nm', hl', hin', -, -, he', -⟩ := hst.1 _ d hs
    rw [← inArea_name hin hin', he] at he'
    cases he'
    obtain ⟨lay, hl, hj⟩ := hLL _ lay' hl'
    obtain ⟨X2, hj2, hD2, hx2⟩ := hDK.2.2 _ lay hl
    have hX2 : X2 = walTmps := hx2.1
    subst hX2
    have hmem : (lay.j, NameSet.except walTmps, hj2) ∈ cl := by
      obtain ⟨l1, l2, hcl, -, -⟩ := hD2.2.2.1; rw [hcl]; simp
    have hf := (hnm _ lay hl).2.2 _ _ hmem
    rw [entsOf_lookup, hj] at hd
    exact HistFoP.crash hreg hmem hf hb hb J' hd

/-- **After a crash, every WAL directory at a WAL name of the area holds no directory at the
pipeline's names** (pure; `BootFoRest`'s first part): the directory at the name is a new layout's
(`WalsStart`), an old layout's directory (`walCrash_pure`), whose pipeline names' invariant quarters
(`walTmpHalves`, `Jh`) leave no directory a crash may keep (`hT`, from `tmpHalvesL_crash`). -/
theorem crash_tmpNoDir {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s' : AbsDiskState}
    {Ls Ls' : GMap GoString WalLay} {m' : Tree} {Jh : GMap GoString Ino}
    (hst : WalsStart C Mr R jr s' Ls' m')
    (hLL : ∀ dir lay', Ls' !! dir = some lay' → ∃ lay, Ls !! dir = some lay ∧ lay'.j = lay.j)
    (hJh : ∀ dir lay, Ls !! dir = some lay → Jh !! dir = some lay.j)
    (hT : ∀ dir J, Jh !! dir = some J → ∀ b ∈ walTmps, ∀ J', m'.entry J b ≠ some (.dir J')) :
    ∀ nm J, walNameOk nm → m'.entry jr nm = some (.dir J) → ∀ b ∈ walTmps, ∀ J',
      entsOf m' J !! b ≠ some (.dir J') := by
  intro nm J hw he b hb J'
  rw [entsOf_lookup]
  have hin : InArea s'.area (s'.area ++ go!"/" ++ nm) nm := ⟨hw, rfl⟩
  cases hs : s'.wal !! (s'.area ++ go!"/" ++ nm) with
  | none => rw [hst.2.2.1 _ nm hin hs] at he; cases he
  | some d =>
    obtain ⟨lay', nm', hl', hin', -, -, he', -⟩ := hst.1 _ d hs
    rw [← inArea_name hin hin', he] at he'
    cases he'
    obtain ⟨lay, hl, hj⟩ := hLL _ lay' hl'
    rw [hj]
    exact hT _ _ (hJh _ lay hl) b hb J'

/-- **A pipeline name's invariant quarter after a crash**: the name holds no directory. -/
theorem tmpHalf_crash (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) (J : Ino) (b : GoString) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      tmpHalf (hG := ⟨G, L⟩) J b ={E}=∗
      ⌜∀ J', V'.now.entry J b ≠ some (.dir J')⌝ ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' := by
  iintro #Hsh Hcr Hh
  unfold tmpHalf
  icases Hh with ⟨%h, %n0, Hn, #Hlb, %hf⟩
  imod crashRest_region Q L L' D tt V' R [((J, NameSet.only [b], h), DFrac.own qTmpI)] n0 E hE
    $$ Hsh Hcr [Hn] Hlb with ⟨%Hreg, Hcr, -⟩
  · unfold osClaims
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Hn
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imodintro
  iframe Hcr
  ipureintro
  intro J'
  exact HistFoP.crash (c := (J, NameSet.only [b], h)) Hreg (by simp) hf (by simp [NameSet.Mem]) trivial J'

/-- **The pipeline names' invariant quarters of a list of directories after a crash.** -/
theorem tmpHalvesL_crash (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) (l : List (GoString × Ino)) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      ([∗list] kv ∈ l, walTmpsHalf (hG := ⟨G, L⟩) kv.2) ={E}=∗
      ⌜∀ kv ∈ l, ∀ b ∈ walTmps, ∀ J', V'.now.entry kv.2 b ≠ some (.dir J')⌝ ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' := by
  induction l with
  | nil =>
    iintro #Hsh Hcr -
    imodintro
    iframe Hcr
    ipureintro; intro kv hkv; cases hkv
  | cons kv l ih =>
    iintro #Hsh Hcr Hl
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hl with ⟨Hk, Hl⟩
    iunfold walTmpsHalf at Hk
    iunfold walTmps at Hk
    icases Hk with ⟨H0, H1, -⟩
    imod tmpHalf_crash Q L L' D tt V' R E hE kv.2 _ $$ Hsh Hcr H0 with ⟨%h0, Hcr⟩
    imod tmpHalf_crash Q L L' D tt V' R E hE kv.2 _ $$ Hsh Hcr H1 with ⟨%h1, Hcr⟩
    imod ih $$ Hsh Hcr Hl with ⟨%hl, Hcr⟩
    imodintro
    iframe Hcr
    ipureintro
    intro kv' hkv' b hb
    rcases List.mem_cons.1 hkv' with rfl | hkv'
    · simp only [walTmps, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact h0
      · exact h1
    · exact hl kv' hkv' b hb

/-- **The WAL directories' pipeline names after a crash** (`walTmpHalves`' map). -/
theorem tmpHalvesM_crash (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) (Jh : GMap GoString Ino) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      ([∗map] _dir ↦ J ∈ Jh, walTmpsHalf (hG := ⟨G, L⟩) J) ={E}=∗
      ⌜∀ dir J, Jh !! dir = some J → ∀ b ∈ walTmps, ∀ J', V'.now.entry J b ≠ some (.dir J')⌝ ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' := by
  iintro #Hsh Hcr Hm
  ihave Hl := (BigSepM.bigSepM_toList (Φ := fun (_ : GoString) (J : Ino) =>
    walTmpsHalf (hG := ⟨G, L⟩) J)).1 $$ Hm
  imod tmpHalvesL_crash Q L L' D tt V' R E hE (toList Jh) $$ Hsh Hcr Hl with ⟨%hl, Hcr⟩
  imodintro
  iframe Hcr
  ipureintro
  intro dir J hd
  exact hl (dir, J) (toList_get.2 hd)

/-- **The WAL's crash** (plan §2.2): from the old generation's invariant, its `crashed` (from the
crash adequacy theorem) and the WAL's crash token, the shared mode's invariant, the generation's
`crashRest` (with the files `D` another client's crash lemma took already, none named in a directory
under the area, `hD`) and W1 (`hQ`): a new generation of the WAL's names, the crash view,
the new generation's start over the crashed tree, its lock and crash tokens, the crash boot's
non-segment files whole (`bootFiles`: a WAL directory's files at its non-`.wal` names, a temporary
directory's `.touch`; distinct by the crashed tree's unique naming, `crashRest_treeWf`, each from an old segment's
start if it was one, else from `crashRest`), the crashed tree well formed (for the crash boot,
`walBootCrash`), and `crashRest` back with the files `D'` taken: only files named in a directory under
the area (`InAreaDir`: the boot files, and the old segments named there; an old segment named
elsewhere or nowhere is not taken, only its crash learnt), so that another client's crash lemma can be
called after this one (its files are elsewhere) or before it (`hD`). -/
theorem walInv_crash (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (Q : Fs.OsState → Fs.OsState → Prop)
    (hQ : ∀ st st', Q st st' → W1 C st st') (hPre : AbsDiskGpreS GF) (L L' : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (V' : Hist) (D : List Ino)
    (hD : ∀ i ∈ D, ¬ InAreaDir V'.now jr i) (E : CoPset)
    (hE : ↑walN ⊆ E) (hE' : ↑osShN ⊆ E) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ crashed (hC := L.goose_crashGS) -∗
      walCrashTok (W := W) -∗ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' ={E}=∗
      ∃ (W' : WalGS GF) (s' : AbsDiskState) (D' : List Ino),
        walCrashWal W W' ∗
        ⌜W'.roots = R ∧ s'.area = r ∧ DirsAvoid R jr s' ∧ WalsBounded s' ∧ DirsRoots R s' ∧ TreeWf R V'.now ∧
          (∀ nm J, walNameOk nm → V'.now.entry jr nm = some (.dir J) → NoDirX (entsOf V'.now J)) ∧
          (∀ nm J, walNameOk nm → V'.now.entry jr nm = some (.dir J) → ∀ b ∈ walTmps, ∀ J',
            entsOf V'.now J !! b ≠ some (.dir J')) ∧
          ∀ i ∈ D', InAreaDir V'.now jr i⌝ ∗
        walStart L' W' C Mr R jr r s' V'.now ∗
        walPast (W := W') s' ∗ walUnlockedTok (W := W') ∗ walCrashTok (W := W') ∗
        ([∗list] i ∈ bootFiles V'.now jr, trFile (hG := ⟨G, L'⟩) i False) ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (D' ++ D) false V' := by
  classical
  iintro #Hinv #Hcrd Htok #Hsh Hcr
  -- the crashed tree is well formed (`crashRest_treeWf`): its names unique
  imod crashRest_treeWf Q L L' D false V' R E hE' $$ Hsh Hcr with ⟨%hwf, Hcr⟩
  have hu : UniqNames V'.now := uniqNames_of_wf hwf
  -- open the old invariant and close it with the crash tokens
  unfold walInv
  icases Hinv with ⟨-, #Hinv⟩
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (Hb | ⟨-, >Ht⟩)
  rotate_left
  · iexfalso; iapply walCrashTok_excl $$ Htok Ht
  imod Hclose $$ [Htok] with -
  · inext; iright; iframe Hcrd Htok
  icases Hb with ⟨%s, >Hb⟩
  iunfold walInvBody at Hb
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, #Hcm, Hlays, %Hok, -, -, -, %Han, %Hnm, Hpk,
    ⟨%K, %cp, -, -, %HDK⟩, %HAt, -, %Hbd⟩
  -- the pipeline names' invariant quarters: no directory there after the crash
  iunfold walParked at Hpk
  icases Hpk with ⟨%-, %-, -, -, %-, -, -, Htp, -⟩
  iunfold walTmpParked at Htp
  icases Htp with ⟨-, Htp⟩
  iunfold walTmpHalves at Htp
  icases Htp with ⟨%Jh, %hJh, Htp⟩
  imod tmpHalvesM_crash Q L L' D false V' R E hE' Jh $$ Hsh Hcr Htp with ⟨%hTd, Hcr⟩
  icases walGhost_keys_keep (W := W) s $$ Hg with ⟨Hg, %hk⟩
  icases walGhost_steps (W := W) s $$ Hg with ⟨Hg, #Hst⟩
  -- the tree: what the claims allow
  imod crashRest_region Q L L' D false V' R (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) n E
    hE' $$ Hsh Hcr Hcl Hcm with ⟨%Hreg, Hcr, -⟩
  have hcl : ∀ l : List Claim, (l.map (fun c => (c, DFrac.own (1 : Qp).half))).map (·.1) = l :=
    fun l => by
      induction l with
      | nil => rfl
      | cons c l ih => simp only [List.map_cons]; rw [ih]
  rw [hcl cl] at Hreg
  -- the segments: those named under the area taken, every one's crash learnt
  let tk : SegG → Bool := fun g => decide (InAreaDir V'.now jr g.ino)
  iunfold laysResF at Hlays
  icases crashRest_take_segs Q L L' D false V' F (segsAll Ls) tk
    (fun g _ ht hgD => hD g.ino hgD (of_decide_eq_true ht)) (walsOk_nodup Hok)
    (walsOk_cut Hok) $$ Hcr Hlays with ⟨%st, %st', %Hfs, Hstarts, Hcr, -⟩
  obtain ⟨hQs, htree, hfiles⟩ := Hfs
  obtain ⟨s', Ls', hcrash, harea', hk', hstart, hnd', hsegs, hLL⟩ :=
    walCrash_pure C hC Mr R jr s Ls cl n V'.now st st' Hok Han.1 Hnm hk (fun _ _ hl => HAt.ne hl) Hreg htree (hQ _ _ hQs) hfiles
  -- the taken segments' starts
  have hT : ([∗list] g ∈ segsAll Ls, if tk g then
        osFileStartO (L := L') g.ino (st'.fs.files !! g.ino) else emp) ⊢
      [∗list] i ∈ ((segsAll Ls).filter tk).map (·.ino), osFileStartO (L := L') i (st'.fs.files !! i) := by
    refine (BigSepL.bigSepL_perm (Φ := fun g => if tk g then
        osFileStartO (L := L') g.ino (st'.fs.files !! g.ino) else emp)
      (List.filter_append_perm tk (segsAll Ls)).symm).1.trans ?_
    refine BigSepL.bigSepL_append.1.trans (sep_elim_left.trans ?_)
    rw [BigSepL.bigSepL_map]
    refine BigSepL.bigSepL_mono (fun {k g} hk => ?_)
    have hg := (List.mem_filter.1 (List.mem_of_getElem? hk)).2
    show (if tk g then _ else _) ⊢ _
    rw [if_pos hg]
  ihave Hstarts := hT $$ Hstarts
  -- the crash boot's files (`bootFiles`): among the taken segments' starts, or not yet taken
  have hBn : (bootFiles V'.now jr).Nodup := bootFiles_nodup hu jr
  have hsegN : (((segsAll Ls).filter tk).map (·.ino)).Nodup :=
    (walsOk_nodup Hok).sublist (List.Sublist.map _ List.filter_sublist)
  have hnamedB : ∀ i ∈ (bootFiles V'.now jr), Named V'.now i := fun i hi => by
    obtain ⟨a, J, b, -, hb, -⟩ := mem_bootFiles.1 hi
    exact ⟨J, b, hb⟩
  have hareaB : ∀ i ∈ (bootFiles V'.now jr), InAreaDir V'.now jr i := fun i hi => by
    obtain ⟨a, J, b, ha, hb, -⟩ := mem_bootFiles.1 hi
    exact ⟨J, b, a, hb, ha⟩
  have hsegT : ∀ i ∈ ((segsAll Ls).filter tk).map (·.ino),
      i ∈ (segsAll Ls).map (·.ino) ∧ InAreaDir V'.now jr i := fun i hi => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hi
    obtain ⟨hg, ht⟩ := List.mem_filter.1 hg
    exact ⟨List.mem_map_of_mem hg, of_decide_eq_true ht⟩
  have hsome : ∀ i ∈ ((segsAll Ls).filter tk).map (·.ino), Named V'.now i →
      (st'.fs.files !! i).isSome := fun i hi hn => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (hsegT i hi).1
    exact (hfiles g hg).2.1 hn
  generalize hsT : ((segsAll Ls).filter tk).map (·.ino) = segT at hsegN hsegT hsome ⊢
  ihave Hstarts := (BigSepL.bigSepL_perm (Φ := fun i => osFileStartO (L := L') i (st'.fs.files !! i))
    (List.filter_append_perm (fun i => decide (i ∈ (bootFiles V'.now jr))) segT).symm).1 $$ Hstarts
  icases BigSepL.bigSepL_append.1 $$ Hstarts with ⟨HB1, Hstarts⟩
  have hB1 : ([∗list] i ∈ segT.filter (fun i => decide (i ∈ (bootFiles V'.now jr))),
      osFileStartO (L := L') i (st'.fs.files !! i)) ⊢
      [∗list] i ∈ segT.filter (fun i => decide (i ∈ (bootFiles V'.now jr))), trFile (hG := ⟨G, L'⟩) i False := by
    refine BigSepL.bigSepL_mono (fun {k i} hk => ?_)
    have hi := List.mem_filter.1 (List.mem_of_getElem? hk)
    have hiB : i ∈ (bootFiles V'.now jr) := of_decide_eq_true hi.2
    have h := hsome i hi.1 (hnamedB i hiB)
    cases e : st'.fs.files !! i with
    | none => rw [e] at h; cases h
    | some f => exact osFileStart_trFile L' i f
  ihave HB1 := hB1 $$ HB1
  icases crashRest_take_named (gooseOsGS (L := L)) (gooseOsGS (L := L')) Q (segT ++ D) false V'
    ((bootFiles V'.now jr).filter (fun i => decide (i ∉ segT)))
    (fun i hi hD' => by
      have hi' := List.mem_filter.1 hi
      rcases List.mem_append.1 hD' with h | h
      · exact of_decide_eq_true hi'.2 h
      · exact hD i h (hareaB i hi'.1))
    (hBn.filter _) (fun i hi => hnamedB i (List.mem_filter.1 hi).1) $$ Hcr with ⟨HB2, Hcr⟩
  have hB2 : ([∗list] i ∈ ((bootFiles V'.now jr).filter (fun i => decide (i ∉ segT))), ∃ f, fileStart (gooseOsGS (L := L')) i f) ⊢
      [∗list] i ∈ ((bootFiles V'.now jr).filter (fun i => decide (i ∉ segT))), trFile (hG := ⟨G, L'⟩) i False := by
    refine BigSepL.bigSepL_mono (fun {k i} _ => ?_)
    iintro ⟨%f, H⟩
    iapply osFileStart_trFile L' i f
    iapply (Fs.fileStart_eq (L := L') i f).1 $$ H
  ihave HB2 := hB2 $$ HB2
  have hperm : (segT.filter (fun i => decide (i ∈ (bootFiles V'.now jr))) ++ ((bootFiles V'.now jr).filter (fun i => decide (i ∉ segT)))).Perm (bootFiles V'.now jr) := by
    refine List.Perm.trans ?_ (List.filter_append_perm (fun i => decide (i ∈ segT)) (bootFiles V'.now jr))
    refine List.Perm.append ?_ (List.Perm.of_eq (List.filter_congr (fun i _ => by rw [decide_not])))
    refine (List.perm_ext_iff_of_nodup (hsegN.filter _) (hBn.filter _)).2 (fun i => ?_)
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  ihave HB : [∗list] i ∈ (bootFiles V'.now jr), trFile (hG := ⟨G, L'⟩) i False $$ [HB1 HB2]
  · iapply (BigSepL.bigSepL_perm (Φ := fun i => trFile (hG := ⟨G, L'⟩) i False) hperm).1
    iapply BigSepL.bigSepL_append.2
    iframe HB1 HB2
  -- the new layouts' segments are no crash boot file (they are at `.wal` names), and are named under
  -- the area (so taken)
  have hsegB : ∀ dir lay, Ls' !! dir = some lay → ∀ g ∈ lay.segs, g.ino ∉ (bootFiles V'.now jr) := by
    intro dir lay hl g hg hB
    obtain ⟨a, J, b, -, hb, ht⟩ := mem_bootFiles.1 hB
    obtain ⟨hw, he⟩ := (hstart.2.2.2.2.1 dir lay hl).1 g hg
    rw [entsOf_lookup] at he
    have e := (hu _ _ _ _ _ hb he).2
    subst e
    rw [bootTake_not_wal ht] at hw
    cases hw
  have hsegA : ∀ dir lay, Ls' !! dir = some lay → ∀ g ∈ lay.segs, InAreaDir V'.now jr g.ino := by
    intro dir lay hl g hg
    obtain ⟨-, he⟩ := (hstart.2.2.2.2.1 dir lay hl).1 g hg
    rw [entsOf_lookup] at he
    obtain ⟨d, hd⟩ : ∃ d, s'.wal !! dir = some d := by
      cases h : s'.wal !! dir with
      | none => rw [hstart.2.1 dir h] at hl; cases hl
      | some d => exact ⟨d, rfl⟩
    obtain ⟨lay', nm, hl', -, -, -, hj, -⟩ := hstart.1 dir d hd
    rw [hl] at hl'; cases hl'
    exact ⟨lay.j, g.name, nm, he, hj⟩
  -- the new generation's ghost state
  ihave #Hst' := walStepsLb_mono s s' (fun _ hn => walsStepped_crash hcrash hn) $$ Hst
  imod walGhost_init hPre R s' hk' $$ Hst' with
    ⟨%W', %hWR', Hg', HM', #Hp', Hu', Hc', Hcr', Ht', Hpk', Hdk', Hcp', Hpo', Hnm', Hnw', Hnwf', Hlt'⟩
  imodintro
  iexists W', s', (((bootFiles V'.now jr).filter (fun i => decide (i ∉ segT))) ++ segT)
  rw [List.append_assoc]
  iframe Hu' Hc' Hcr Hp' HB
  isplitl [Hg HM']
  · unfold walCrashWal
    iexists s, s'
    iframe Hg HM' Hp'
    ipureintro; exact hcrash
  isplitr
  · ipureintro
    refine ⟨hWR', by rw [harea', Har], fun dd hdd => Han.2 dd ?_, walsBounded_crash hcrash Hbd.1,
      dirsRoots_crash hcrash Hbd.2, hwf, crash_noDirX Hnm HDK Hreg hstart hLL,
      crash_tmpNoDir hstart hLL hJh hTd, fun i hi => ?_⟩
    · rw [← hcrash.2.1]; exact hdd
    · rcases List.mem_append.1 hi with h | h
      · exact hareaB i (List.mem_filter.1 h).1
      · exact (hsegT i h).2
  unfold walStart
  iexists Ls', segT.filter (fun i => !decide (i ∈ (bootFiles V'.now jr))), (fun i => st'.fs.files !! i)
  iframe Hg' Hstarts Hcr' Ht' Hpk' Hdk' Hcp' Hpo' Hnm' Hnw' Hnwf' Hlt'
  ipureintro
  refine ⟨by rw [harea', Har], hsegN.filter _, fun i hi hn => hsome i (List.mem_filter.1 hi).1 hn,
    hnd', hstart, fun dir lay hl g hg => ?_⟩
  obtain ⟨h1, h2⟩ := hsegs dir lay hl g hg
  refine ⟨List.mem_filter.2 ⟨?_, ?_⟩, h2⟩
  · rw [← hsT]
    obtain ⟨g', hg', e⟩ := List.mem_map.1 h1
    rw [← e]
    refine List.mem_map_of_mem (List.mem_filter.2 ⟨hg', decide_eq_true ?_⟩)
    rw [e]; exact hsegA dir lay hl g hg
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact hsegB dir lay hl g hg

/-- Every name of a set. -/
theorem restrictN_all (e : Ents) : restrictN (.except []) e = e := by
  apply GMap.ext; intro b
  exact restrictN_lookup _ _ _ (by simp [NameSet.Mem])

/-- A claim of a history with nothing logged: its names as the tree has them. -/
theorem namesOf_nil {V : Hist} (hV : V.2 = []) (j : Ino) (N : NameSet) :
    namesOf V j N = ⟨restrictN N (entsOf V.now j), [], restrictN N (entsOf V.now j)⟩ := by
  have hnow : V.now = V.1 := by simp [Hist.now, Hist.ops, hV, replay]
  unfold namesOf
  simp [hV, hnow]

/-- A claim of the area holding a WAL name, as the boot history has it (`walInv_alloc`'s `harea`:
every WAL name in a claim of the area, the area claim's or a present WAL's own, G-spine). -/
theorem areaClaim_boot {jr : Ino} {V : Hist} {cl : List Claim} (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1) (harea : WalsCreateOk jr cl) (nm : GoString)
    (hnm : walNameOk nm) :
    ∃ N hN, (jr, N, hN) ∈ cl ∧ N.Mem nm ∧ hN.boot = restrictN N (entsOf V.now jr) ∧ hN.ents = [] := by
  obtain ⟨N, hN, hNm, hNall⟩ := harea nm hnm
  have h := hcl _ hNm
  simp only at h
  rw [namesOf_nil hV] at h
  exact ⟨N, hN, hNm, hNall, by rw [h], by rw [h]⟩

/-- **Strong absence at the start** (pure): the boot tree has no entry at a WAL-less name of the
area (`WalsStart`), the claims as the boot history has them, one of them on the area's WAL names. -/
theorem absentNone_start (s : AbsDiskState) (jr : Ino) (V : Hist) (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (harea : WalsCreateOk jr cl)
    (habs : ∀ dir nm, InArea s.area dir nm → s.wal !! dir = none → V.now.entry jr nm = none) :
    AbsentNone s jr cl 0 := by
  intro dir nm hin hnone
  have he := habs dir nm hin hnone
  refine ⟨fun N h hc hN => ?_, fun m' hreg => ?_⟩
  · have h1 := hcl _ hc
    simp only at h1
    rw [h1, namesOf_nil hV]
    show restrictN N (entsOf V.now jr) !! nm = none
    rw [restrictN_lookup _ _ _ hN, entsOf_lookup]; exact he
  · obtain ⟨N, h, hc, hN⟩ := harea nm hin.1
    have h1 := hcl _ hc
    simp only at h1
    rw [namesOf_nil hV] at h1
    obtain ⟨K, -, -, hval⟩ := hreg
    rw [hval _ hc nm hN, valAfter_nil (by rw [h1])]
    show h.boot !! nm = none
    rw [h1]
    show restrictN N (entsOf V.now jr) !! nm = none
    rw [restrictN_lookup _ _ _ hN, entsOf_lookup]; exact he

/-- A `.wal` name is in a WAL directory's claim at the start (all names but the pipeline's). -/
theorem walTmps_mem_wal {b : GoString} (hb : walNameP b = true) : (NameSet.except walTmps).Mem b :=
  fun hm => by rw [walTmps_not_wal b hm] at hb; cases hb

/-- **A WAL directory's `.wal` entries after a crash, at the start**: as the boot tree has them (its
claim, on all names but the pipeline's, with nothing logged). -/
theorem start_walEnt {V : Hist} (hV : V.2 = []) {cl : List Claim}
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1) {J : Ino} {h : NamesH}
    (hjm : (J, NameSet.except walTmps, h) ∈ cl) {n : Nat} {m' : Tree} (hreg : RegionCrashed cl n m')
    (b : GoString) (hb : walNameP b = true) : entsOf m' J !! b = entsOf V.now J !! b := by
  obtain ⟨K, -, -, hval⟩ := hreg
  have e1 := hcl _ hjm
  simp only at e1
  rw [namesOf_nil hV] at e1
  rw [entsOf_lookup, entsOf_lookup, hval _ hjm b (walTmps_mem_wal hb), valAfter_nil (by rw [e1]), e1]
  show restrictN (.except walTmps) (entsOf V.now J) !! b = _
  rw [restrictN_lookup _ _ _ (walTmps_mem_wal hb), entsOf_lookup]

/-- The static relation over a WAL directory's claim at the start (all names but the pipeline's). -/
theorem walAbsD_restrictTmps {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {e : Ents} (h : WalAbsD C Mr d lay e) : WalAbsD C Mr d lay (restrictN (.except walTmps) e) := by
  have hw : walInos e = walInos (restrictN (.except walTmps) e) :=
    walInos_congr (fun b hb => (restrictN_lookup _ _ _ (walTmps_mem_wal hb)).symm)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨hw ▸ h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **What the invariant says of the WALs, at the start** (pure): from the start's static relation,
claims with nothing logged on each WAL's area names (`harea`) and wholly on every directory at such
a name (`hdirs`), and the durable directories' resolution (`hdok`). -/
theorem walsOk_start (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (V : Hist) (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (harea : WalsCreateOk jr cl)
    (hdirs : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (J, NameSet.except walTmps, h) ∈ cl)
    (hdok : DirsOk R s cl 0) (hst : WalsStart C Mr R jr s Ls V.now)
    (hnd : ((segsAll Ls).map (·.ino)).Nodup) (hcut : ∀ g ∈ segsAll Ls, g.om.cut = none) :
    WalsOk C Mr R jr s Ls cl 0 := by
  have hc : ∀ c ∈ cl, c.2.2 = ⟨restrictN c.2.1 (entsOf V.now c.1), [],
      restrictN c.2.1 (entsOf V.now c.1)⟩ := fun c h => by rw [hcl c h, namesOf_nil hV]
  have hlog : ∀ c ∈ cl, c.2.2.ents = [] := fun c h => by rw [hc c h]
  -- the area's WAL names, after a crash the claims allow, are as at the start
  have harea' : ∀ m', RegionCrashed cl 0 m' → ∀ nm, walNameOk nm →
      m'.entry jr nm = V.now.entry jr nm := by
    intro m' hreg nm hnm
    obtain ⟨N, hN, hNm, hNall, hNb, -⟩ := areaClaim_boot hV hcl harea nm hnm
    obtain ⟨K, -, -, hval⟩ := hreg
    rw [hval _ hNm nm hNall, valAfter_nil (hlog _ hNm), hNb,
      restrictN_lookup _ _ _ hNall, entsOf_lookup]
  refine ⟨fun dir d hd => ?_, hst.2.1, hnd, hcut, fun dir nm hin hnone m' hreg J hJ => ?_, hdok⟩
  · obtain ⟨lay, nm, hL, hin, hjr, hnm, he, habs, hfit, h1, h2, h3, hlast⟩ := hst.1 dir d hd
    obtain ⟨hj, hjm⟩ := hdirs nm lay.j hin.1 he
    have hjc := hc _ hjm
    simp only at hjc
    refine ⟨lay, nm, hj, hL, hin, hjr, hnm, ⟨walTmps, walTmps_not_wal, hjm, ?_⟩, ?_,
      walFullOk_of_nil (hst.2.2.2.2.2 dir lay hL).2.1 habs
        ((hst.2.2.2.2.2 dir lay hL).2.2.mono (fun g hg => (List.dropLast_sublist _).subset hg))
        (crashOkW_of_crashOk ?_)⟩
    · exact claimCoh_init _ _ _ (by rw [hjc]) (fun b _ => by rw [hjc])
    · rw [hjc]; exact walAbsD_restrictTmps habs
    · refine walAbs_crashOk_start C hC Mr d lay cl 0 (entsOf V.now lay.j) habs hfit hlog
        (fun m' hreg => walInos_congr (start_walEnt hV hcl hjm hreg)) ?_ ⟨h1, h2, h3⟩ hlast
      rw [hjr, hnm]
      obtain ⟨N, hN, hNm, hNall, hNb, -⟩ := areaClaim_boot hV hcl harea nm hin.1
      refine ⟨N, hN, hNm, hNall, ?_⟩
      rw [hNb, restrictN_lookup _ _ _ hNall, entsOf_lookup]
      exact he
  · rw [harea' m' hreg nm hin.1, hst.2.2.1 dir nm hin hnone] at hJ
    cases hJ

/-- **No WAL has an alternative layout at the start** (`DirKeysOk`'s crash clause; pure): as
`walsOk_start`'s crash conditions. -/
theorem crashOk_start (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (V : Hist) (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (harea : WalsCreateOk jr cl)
    (hdirs : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (J, NameSet.except walTmps, h) ∈ cl)
    (hst : WalsStart C Mr R jr s Ls V.now) :
    ∀ dir d lay, s.wal !! dir = some d → Ls !! dir = some lay →
      CrashOkA C Mr (walFullD d lay.pg lay) (unpurge lay.pg lay) none cl 0 := by
  have hc : ∀ c ∈ cl, c.2.2 = ⟨restrictN c.2.1 (entsOf V.now c.1), [],
      restrictN c.2.1 (entsOf V.now c.1)⟩ := fun c h => by rw [hcl c h, namesOf_nil hV]
  have hlog : ∀ c ∈ cl, c.2.2.ents = [] := fun c h => by rw [hc c h]
  intro dir d lay0 hd hL0
  obtain ⟨lay, nm, hL, hin, hjr, hnm, he, habs, hfit, h1, h2, h3, hlast⟩ := hst.1 dir d hd
  rw [show lay0 = lay from Option.some.inj (hL0.symm.trans hL)]
  have hpg := (hst.2.2.2.2.2 dir lay hL).2.1
  rw [hpg, unpurge_nil hpg, walFullD_nil habs.cut.1]
  obtain ⟨hj, hjm⟩ := hdirs nm lay.j hin.1 he
  have hjc := hc _ hjm
  simp only at hjc
  refine (crashOkA_none_iff C Mr d lay cl 0).2 ?_
  refine walAbs_crashOk_start C hC Mr d lay cl 0 (entsOf V.now lay.j) habs hfit hlog
    (fun m' hreg => walInos_congr (start_walEnt hV hcl hjm hreg)) ?_ ⟨h1, h2, h3⟩ hlast
  rw [hjr, hnm]
  obtain ⟨N, hN, hNm, hNall, hNb, -⟩ := areaClaim_boot hV hcl harea nm hin.1
  refine ⟨N, hN, hNm, hNall, ?_⟩
  rw [hNb, restrictN_lookup _ _ _ hNall, entsOf_lookup]
  exact he

/-- **The segments are at their names, at the start** (pure): from the start's (`WalsStart`), the
claims as the boot history has them, every directory at a WAL name claimed wholly (`hdirs`). -/
theorem walsNamed_start (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (V : Hist) (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (hdirs : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (J, NameSet.except walTmps, h) ∈ cl)
    (hst : WalsStart C Mr R jr s Ls V.now)
    (hfo : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) → NoDirX (entsOf V.now J)) :
    WalsNamed Ls cl 0 := by
  have hc : ∀ c ∈ cl, c.2.2 = ⟨restrictN c.2.1 (entsOf V.now c.1), [],
      restrictN c.2.1 (entsOf V.now c.1)⟩ := fun c h => by rw [hcl c h, namesOf_nil hV]
  intro dir lay hL
  have hn := hst.2.2.2.2.1 dir lay hL
  -- the layout's WAL, its directory claimed wholly
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [hst.2.1 dir h] at hL; cases hL
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay', nm, hL', hin, -, -, he, ha, -⟩ := hst.1 dir d hd
  rw [hL] at hL'; cases hL'
  obtain ⟨h, hjm⟩ := hdirs nm lay.j hin.1 he
  rw [(hst.2.2.2.2.2 dir lay hL).2.1, List.nil_append]
  refine ⟨fun hj ⟨X, hX, hm, _⟩ => ?_, fun m' hreg => ?_, fun N hj hm => ?_⟩
  rotate_left 2
  · have e := hc _ hm
    simp only at e
    refine HistFoP.of_boot (by rw [e]) (fun b hbN hP J hd => ?_)
    rw [e] at hd
    simp only at hd
    rw [restrictN_lookup _ _ _ hbN] at hd
    exact hfo nm lay.j hin.1 he b J hP hd
  · have e := hc _ hm
    simp only at e
    rw [e]
    exact hn.restrict hX
  · have e := start_walEnt hV hcl hjm hreg
    have hw : walInos (entsOf m' lay.j) = walInos (entsOf V.now lay.j) := walInos_congr e
    refine ⟨fun g hg => ⟨(hn.1 g hg).1, fun _ => by rw [e _ (hn.1 g hg).1]; exact (hn.1 g hg).2⟩,
      fun b x hb hx => hn.2 b x hb (by rw [← e b hb]; exact hx), fun i hi => ?_⟩
    rw [hw, ha.names.1] at hi; exact hi

/-- **Every WAL's directory at its name, at the start** (pure): the boot tree has it there
(`WalsStart`), and every claim of the area holds it as the boot history has it. -/
theorem walsAt_start (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (V : Hist) (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (hst : WalsStart C Mr R jr s Ls V.now) : WalsAtS jr Ls cl := by
  intro dir lay hL
  refine ⟨(hst.2.2.2.2.2 dir lay hL).1, fun N h hm hN => ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [hst.2.1 dir h] at hL; cases hL
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay', nm, hL', -, -, hnm, he, -⟩ := hst.1 dir d hd
  rw [hL] at hL'; cases hL'
  have e1 := hcl _ hm
  simp only at e1
  rw [e1, namesOf_nil hV]
  show restrictN N (entsOf V.now jr) !! lay.nm = _
  rw [restrictN_lookup _ _ _ hN, entsOf_lookup, hnm]; exact he

/-- **Every WAL's directory claim once and exclusive, at the start** (pure; gap C): the boot program
claims every directory at a WAL name wholly (`hdirs`), once, and no other of its claims of that
directory holds one of its names (`hdirs1`). -/
theorem dirClaimsOk_start (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (V : Hist) (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (hdirs : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (J, NameSet.except walTmps, h) ∈ cl)
    (hdirs1 : ∀ nm J h, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      (J, NameSet.except walTmps, h) ∈ cl → ClaimOnce (J, NameSet.except walTmps, h) cl ∧
        ∀ c' ∈ cl, c' ≠ (J, NameSet.except walTmps, h) → c'.1 = J →
          ∀ b, (NameSet.except walTmps).Mem b → ¬ c'.2.1.Mem b)
    (hst : WalsStart C Mr R jr s Ls V.now) : DirClaimsOk jr Ls cl := by
  intro dir lay hL
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [hst.2.1 dir h] at hL; cases hL
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay', nm, hL', hin, -, -, he, -⟩ := hst.1 dir d hd
  rw [hL] at hL'; cases hL'
  obtain ⟨h, hjm⟩ := hdirs nm lay.j hin.1 he
  obtain ⟨honce, hex⟩ := hdirs1 nm lay.j h hin.1 he hjm
  have hjc := hcl _ hjm
  simp only at hjc
  refine ⟨walTmps, h, ⟨(hst.2.2.2.2.2 dir lay hL).1, walTmps_not_wal, honce, ?_,
    fun c' hc' hne hcj b hb => hex c' hc' hne hcj b (fun hbX => by
      rw [walTmps_not_wal b hbX] at hb; cases hb)⟩, rfl, hex⟩
  exact claimCoh_init _ _ _ (by rw [hjc, namesOf_nil hV])
    (fun b _ => by rw [hjc, namesOf_nil hV])

/-- A segment's start resources, its `OsMeta` and bytes those of the file, are its two halves. -/
theorem segStart_halves (L : GooseLocalGS GF) (g : SegG) (f : Fs.OsFile) (hom : g.om = initMeta f)
    (hbs : g.bs = f.contents.map durB) :
    osFileStart (L := L) g.ino f ⊢ segRes (L := L) g ∗ segRes (L := L) g := by
  unfold osFileStart segRes
  rw [← hom, ← hbs]
  have hm := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm g.ino (1 : Qp).half
    (1 : Qp).half g.om
  rw [Qp.half_add_half] at hm
  have hb : osBytes (L := L) g.ino 0 (DFrac.own 1) g.bs ⊢
      osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs := by
    unfold osBytes bytesG
    refine (BigSepL.bigSepL_mono_of_forall ?_).trans BigSepL.bigSepL_sep_eqv.1
    intro k x
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (g.ino, 0 + k)
      (1 : Qp).half (1 : Qp).half x
    rw [Qp.half_add_half] at h
    exact h.1
  unfold osMeta
  iintro ⟨Hm, Hb⟩
  icases hm.1 $$ Hm with ⟨Hm1, Hm2⟩
  icases hb $$ Hb with ⟨Hb1, Hb2⟩
  isplitl [Hm1 Hb1]
  · iframe
  · iframe

/-- **A claim of the area on one present WAL's name alone** (G-spine; `walInv_alloc`'s output and the
name claims it registers). -/
def NameClaimOf (jr : Ino) (Ls : GMap GoString WalLay) (c : Claim) : Prop :=
  c.1 = jr ∧ ∃ dir lay, Ls !! dir = some lay ∧ c.2.1 = NameSet.only [lay.nm]

noncomputable instance NameClaimOf.dec (jr : Ino) (Ls : GMap GoString WalLay) (c : Claim) :
    Decidable (NameClaimOf jr Ls c) := Classical.propDecidable _

/-- The name of a claim on one name. -/
def claimName (c : Claim) : GoString :=
  match c.2.1 with
  | .only [b] => b
  | _ => []

/-- The names of the name claims of `cl`. -/
def nameClaimsOf (jr : Ino) (Ls : GMap GoString WalLay) (cl : List Claim) : List GoString :=
  cl.filterMap (fun c => if NameClaimOf jr Ls c then some (claimName c) else none)

theorem mem_nameClaimsOf {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} {nm : GoString} :
    nm ∈ nameClaimsOf jr Ls cl ↔ ∃ c ∈ cl, NameClaimOf jr Ls c ∧ claimName c = nm := by
  unfold nameClaimsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, he⟩
    by_cases h : NameClaimOf jr Ls c
    · rw [if_pos h] at he; cases he; exact ⟨c, hc, h, rfl⟩
    · rw [if_neg h] at he; cases he
  · rintro ⟨c, hc, h, rfl⟩
    exact ⟨c, hc, by rw [if_pos h]⟩

/-- **The program's halves of the present WALs' name claims, out of the rest** (`walInv_alloc`). -/
theorem names_split_start (jr : Ino) (Ls : GMap GoString WalLay) (cl : List Claim)
    (hok : ∀ b h, (jr, NameSet.only [b], h) ∈ cl → NameOk b)
    (hwn : ∀ dir lay, Ls !! dir = some lay → walNameOk lay.nm) (hA : WalsAtS jr Ls cl) :
    ([∗list] c ∈ cl, if WalDirClaimOf Ls c then emp else
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2) ⊢
      ([∗list] nm ∈ nameClaimsOf jr Ls cl, nameShare (L := L) jr Ls nm) ∗
      ([∗list] c ∈ cl, if WalDirClaimOf Ls c ∨ NameClaimOf jr Ls c then emp else
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2) := by
  unfold nameClaimsOf
  rw [BigSepL.bigSepL_filterMap]
  refine (BigSepL.bigSepL_mono (fun {k c} hk => ?_)).trans BigSepL.bigSepL_sep_eqv.1
  have hc := List.mem_of_getElem? hk
  by_cases hn : NameClaimOf jr Ls c
  · obtain ⟨hj, dir, lay, hl, hN⟩ := hn
    have hW : ¬ WalDirClaimOf Ls c := by
      rintro ⟨-, -, -, -, X, hX, -⟩
      rw [hN] at hX; cases hX
    obtain ⟨j, N, h⟩ := c
    simp only at hj hN
    subst hj hN
    have hn' : NameClaimOf j Ls (j, NameSet.only [lay.nm], h) := ⟨rfl, dir, lay, hl, rfl⟩
    rw [if_pos hn', if_neg hW, if_pos (Or.inr hn')]
    simp only [Option.elim, claimName]
    iintro H
    isplitl
    · unfold nameShare
      iexists (1 : Qp).half, h
      iframe H
      ipureintro
      exact ⟨hok _ _ hc, hwn dir lay hl, fun d' l' hl' he => he ▸ (hA d' l' hl').2 _ _ hc (by rw [he]; simp [NameSet.Mem])⟩
    · iempintro
  · rw [if_neg hn]
    simp only [Option.elim]
    by_cases hW : WalDirClaimOf Ls c
    · rw [if_pos hW, if_pos (Or.inl hW)]
      iintro -; isplitl <;> iempintro
    · rw [if_neg hW, if_neg (fun h => h.elim hW hn)]
      iintro H; isplitr
      · iempintro
      · iexact H

/-- **The new generation's invariant**, in the tree's shared mode, from the WAL's start (`walStart`
over the shared mode's boot tree `V.now`, nothing logged): the claims `cl` (whole) as the boot
history has them, among them one on the area's WAL names (`harea`) and one on all names of every
directory at such a name (`hdirs`: every WAL directory wholly), and the durable directories' resolution
after any crash they allow (`hdok`), through no WAL slot of the area (`hav`; the crash keeps it); the invariant takes half of each claim, the commit bound 0 and
half of each segment's resources; the program keeps the other halves, with the layouts. -/
theorem walInv_alloc (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (L : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState) (V : Hist)
    (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (harea : WalsCreateOk jr cl)
    (hdirs : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (J, NameSet.except walTmps, h) ∈ cl)
    (hdirs1 : ∀ nm J h, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      (J, NameSet.except walTmps, h) ∈ cl → ClaimOnce (J, NameSet.except walTmps, h) cl ∧
        ∀ c' ∈ cl, c' ≠ (J, NameSet.except walTmps, h) → c'.1 = J →
          ∀ b, (NameSet.except walTmps).Mem b → ¬ c'.2.1.Mem b)
    (hWR : W.roots = R) (hdok : DirsOk R s cl 0) (hav : DirsAvoid R jr s) (Jm : GMap GoString Ino)
    (hJm : ∀ dir nm J, InArea r dir nm → V.now.entry jr nm = some (.dir J) → Jm !! dir = some J)
    (hnames : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (jr, NameSet.only [nm], h) ∈ cl)
    (hnok : ∀ b h, (jr, NameSet.only [b], h) ∈ cl → NameOk b) (hbd : WalsBounded s)
    (hdr : DirsRoots R s)
    (hfo : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) → NoDirX (entsOf V.now J)) (qs : Qp)
    (E : CoPset) :
    ⊢ walStart L W C Mr R jr r s V.now -∗
      osClaims L (cl.map (fun c => (c, DFrac.own 1))) -∗
      ([∗map] _dir ↦ J ∈ Jm, walTmpsRes (hG := ⟨G, L⟩) J ∗ walTmpsHalf (hG := ⟨G, L⟩) J) -∗
      osPathS (L := L) R r (DFrac.own qs) jr -∗
      (∀ Ls, ⌜WalsStart C Mr R jr s Ls V.now⌝ -∗ walOthersL (L := L) Ls [] cl) ={E}=∗
      walInv (L := L) (W := W) C Mr R jr r ∗
      ∃ Ls, ⌜WalsStart C Mr R jr s Ls V.now⌝ ∗
        walSplitFrag (W := W) (nameClaimsOf jr Ls cl) ∗
        ⌜∀ nm, nm ∈ nameClaimsOf jr Ls cl ↔ ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm⌝ ∗
        [∗list] c ∈ cl, if WalDirClaimOf Ls c ∨ NameClaimOf jr Ls c then emp else
          osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 := by
  iintro Hst Hcl Htmp Hsp Hoth
  unfold walStart
  icases Hst with ⟨%Ls, %is, %fo, Hg, Hcr, Htl, Hpk, Hdk, Hcp, Hpo, Hnm, Hnw, Hnwf, Hlt, %Har, Hfs, %Hp⟩
  obtain ⟨-, -, hnd, hstart, hsegs⟩ := Hp
  have hpg0 : ∀ dir lay, Ls !! dir = some lay → lay.pg = [] := fun dir lay hl =>
    (hstart.2.2.2.2.2 dir lay hl).2.1
  ihave Hoth := Hoth $$ %Ls %hstart
  -- the segments' start resources, halved
  have hsub : ((segsAll Ls).map (·.ino)) ⊆ is := fun i hi => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hi
    obtain ⟨dir, lay, hl, hg'⟩ := segsAll_mem_nil hpg0 hg
    exact (hsegs dir lay hl g hg').1
  obtain ⟨l0, hp0, hs0⟩ := List.subperm_of_subset hnd hsub
  obtain ⟨rest, hrest⟩ := hs0.exists_perm_append
  have hperm : (((segsAll Ls).map (·.ino)) ++ rest).Perm is :=
    (hp0.symm.append_right rest).trans hrest.symm
  have hres : ([∗list] i ∈ is, osFileStartO (L := L) i (fo i)) ⊢
      ([∗list] g ∈ segsAll Ls, segRes (L := L) g) ∗ ([∗list] g ∈ segsAll Ls, segRes (L := L) g) := by
    refine (BigSepL.bigSepL_submseteq hperm).trans ?_
    rw [BigSepL.bigSepL_map]
    refine (BigSepL.bigSepL_mono (fun {k g} hk => ?_)).trans BigSepL.bigSepL_sep_eqv.1
    obtain ⟨dir, lay, hl, hg'⟩ := segsAll_mem_nil hpg0 (List.mem_of_getElem? hk)
    obtain ⟨-, f, hf, hom, hbs⟩ := hsegs dir lay hl g hg'
    rw [hf]
    exact segStart_halves L g f hom hbs
  have hcut : ∀ g ∈ segsAll Ls, g.om.cut = none := by
    intro g hg
    obtain ⟨dir, lay, hl, hg'⟩ := segsAll_mem_nil hpg0 hg
    obtain ⟨-, f, -, hom, -⟩ := hsegs dir lay hl g hg'
    rw [hom]; rfl
  -- the claims, halved
  have hclh : osClaims L (cl.map (fun c => (c, DFrac.own 1))) ⊢
      osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗
        osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) := by
    unfold osClaims
    rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
    refine (BigSepL.bigSepL_mono_of_forall ?_).trans BigSepL.bigSepL_sep_eqv.1
    intro k c
    have h := osNames_frac (L := L) c.1 c.2.1 (1 : Qp).half (1 : Qp).half c.2.2
    rw [Qp.half_add_half] at h
    exact h.1
  icases hres $$ Hfs with ⟨Hi, Hp⟩
  icases hclh $$ Hcl with ⟨Hc1, Hc2⟩
  -- the program's halves of the WAL directories' claims, to park
  have hpark : osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ⊢
      ([∗list] c ∈ cl, if ParkedClaim Ls [] c then
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp) ∗
      ([∗list] c ∈ cl, if WalDirClaimOf Ls c then emp else
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2) := by
    unfold osClaims
    rw [BigSepL.bigSepL_map]
    refine (BigSepL.bigSepL_mono_of_forall ?_).trans BigSepL.bigSepL_sep_eqv.1
    intro k c
    by_cases hP : WalDirClaimOf Ls c
    · rw [if_pos ⟨hP, List.not_mem_nil⟩, if_pos hP]
      iintro H; iframe H
    · rw [if_neg (fun h => hP h.1), if_neg hP]
      iintro H; iframe H
  icases hpark $$ Hc2 with ⟨Hc2, Hc3⟩
  have hwn : ∀ dir lay, Ls !! dir = some lay → walNameOk lay.nm := by
    intro dir lay hl
    obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
      cases h : s.wal !! dir with
      | none => rw [hstart.2.1 dir h] at hl; cases hl
      | some d => exact ⟨d, rfl⟩
    obtain ⟨lay', nm, hL', hin, -, hnm, -⟩ := hstart.1 dir d hd
    rw [hl] at hL'; cases hL'
    rw [hnm]; exact hin.1
  icases names_split_start jr Ls cl hnok hwn (walsAt_start C Mr R jr s Ls V cl hV hcl hstart) $$ Hc3 with
    ⟨Hns, Hc3⟩
  imod walSplit_set (W := W) [] [] (nameClaimsOf jr Ls cl) $$ Hnw Hnwf with ⟨Hnw, Hnwf⟩
  -- the registered names: every present WAL's
  have hW : ∀ nm, nm ∈ nameClaimsOf jr Ls cl ↔ ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm := by
    intro nm
    rw [mem_nameClaimsOf]
    constructor
    · rintro ⟨c, -, ⟨-, dir, lay, hl, hN⟩, rfl⟩
      refine ⟨dir, lay, hl, ?_⟩
      simp only [claimName, hN]
    · rintro ⟨dir, lay, hl, rfl⟩
      obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
        cases h : s.wal !! dir with
        | none => rw [hstart.2.1 dir h] at hl; cases hl
        | some d => exact ⟨d, rfl⟩
      obtain ⟨lay', nm, hL', hin, -, hnm, he, -⟩ := hstart.1 dir d hd
      rw [hl] at hL'; cases hL'
      obtain ⟨h, hc⟩ := hnames nm lay.j hin.1 he
      refine ⟨(jr, NameSet.only [nm], h), hc, ⟨rfl, dir, lay, hl, by rw [hnm]⟩, ?_⟩
      simp only [claimName, hnm]
  have hcm0 : ⊢ |==> osCommitLb (L := L) 0 := by
    unfold osCommitLb gCommitLb
    letI := (gooseOsGS (L := L)).osAllG
    exact monoNatLbOwn_0 _
  imod hcm0 with #Hcm
  imod inv_alloc walN E (iprop((∃ s : AbsDiskState, walInvBody (L := L) (W := W) C Mr R jr r s) ∨
      (crashed (hC := L.goose_crashGS) ∗ walCrashTok (W := W)))) $$
      [Hg Hc1 Hi Hcr Htl Hpk Hpo Hp Hc2 Hdk Hcp Htmp Hnm Hnw Hsp Hns Hlt Hoth]
      with #Hinv
  · inext; ileft; iexists s
    unfold walInvBody
    iexists Ls, cl, 0, ∅
    iframe Hg Hc1 Hcm
    isplitr
    · ipureintro; exact Har
    isplitl [Hi]
    · iapply (laysResF_empty (L := L) Ls).2
      iapply (laysRes_list (L := L) Ls).2 $$ Hi
    isplitr
    · ipureintro
      exact walsOk_start C hC Mr R jr s Ls V cl hV hcl harea hdirs hdok hstart hnd hcut
    isplitr
    · ipureintro; exact harea
    isplitl [Hcr]
    · iexists ∅
      iframe Hcr
      ipureintro
      intro dir N h J hd
      simp at hd
    isplitl [Htl Hlt]
    · unfold walTailsRes
      iexists ∅
      ihave Hlt := walLentRes_init (W := W) ∅ Ls (fun _ _ h _ => (h (GMap.lookup_empty _)).elim)
        (fun dir lay _ hl => by
          cases hd : s.wal !! dir with
          | none => rw [hstart.2.1 dir hd] at hl; cases hl
          | some d =>
            obtain ⟨lay', nm, hl', -, -, -, -, -, -, -, hwz, -⟩ := hstart.1 dir d hd
            rw [hl] at hl'; cases hl'; exact Or.inr hwz) $$ Hlt
      iframe Htl Hlt
      isplitr
      · ipureintro; intro i hi; exact absurd (GMap.lookup_empty (K := Ino) (V := SegFl) i) hi
      isplitr
      · ipureintro
        intro dir d lay _ hd hl
        obtain ⟨lay', nm, hl', -, -, -, -, -, -, hws, hwz, hzS, hlast⟩ := hstart.1 dir d hd
        rw [hl] at hl'; cases hl'
        refine ⟨fun g hg => (hlast g hg).2, hwz.trans hzS, fun g hg => ⟨?_, ?_⟩, hws.symm,
          fun g hg => by
            obtain ⟨-, f, -, hom, -⟩ := hsegs dir lay hl g (List.mem_of_getLast? hg)
            rw [hom]; rfl⟩
        · rw [(hlast g hg).1]; intro y hy
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
        · obtain ⟨-, f, -, hom, hbs⟩ := hsegs dir lay hl g (List.mem_of_getLast? hg)
          intro z hz
          rw [hom] at hz; simp only [initMeta, Option.some.injEq] at hz
          rw [hbs, List.length_map, contents_length, ← hz]; exact le_pageEnd _
      iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · ipureintro
      exact ⟨absentNone_start s jr V cl hV hcl harea hstart.2.2.1, hav⟩
    isplitr
    · ipureintro
      exact walsNamed_start C Mr R jr s Ls V cl hV hcl hdirs hstart hfo
    isplitl [Hpk Hpo Hc2 Hp Htmp Hoth]
    · unfold walParked
      iexists true, WalOut.empty
      dsimp only [WalOut.empty]
      iframe Hpk Hpo Hc2
      isplitr
      · ipureintro; intro i hi; simp at hi
      have hpk : ∀ (k : Nat) (g : SegG), segRes (L := L) g ⊢
          (if g.ino ∈ ([] : List Ino) then emp else segResP (L := L) g) := fun _ g => by
        rw [if_neg List.not_mem_nil]; exact segRes_segResP g
      isplitl [Hp]
      · iapply BigSepL.bigSepL_mono_of_forall (fun {k} {g} => hpk k g) $$ Hp
      isplitl [Htmp]
      rotate_left
      · iexact Hoth
      have hJmL : ∀ dir lay, Ls !! dir = some lay → Jm !! dir = some lay.j := by
        intro dir lay hl
        obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
          cases h : s.wal !! dir with
          | none => rw [hstart.2.1 dir h] at hl; cases hl
          | some d => exact ⟨d, rfl⟩
        obtain ⟨lay', nm, hL', hin, -, -, he, -⟩ := hstart.1 dir d hd
        rw [hl] at hL'; cases hL'
        exact hJm dir nm lay.j (Har ▸ hin) he
      have hsep : ([∗map] _dir ↦ J ∈ Jm, walTmpsRes (hG := ⟨G, L⟩) J ∗ walTmpsHalf (hG := ⟨G, L⟩) J) ⊢
          ([∗map] _dir ↦ J ∈ Jm, walTmpsRes (hG := ⟨G, L⟩) J) ∗
            [∗map] _dir ↦ J ∈ Jm, walTmpsHalf (hG := ⟨G, L⟩) J := by
        rw [BigSepM.bigSepM_sep_eq]
      icases hsep $$ Htmp with ⟨Htmp, Hthv⟩
      unfold walTmpParked walTmpParked0
      isplitr [Hthv]
      rotate_left
      · unfold walTmpHalves
        iexists Jm
        iframe Hthv
        ipureintro; exact hJmL
      iexists Jm
      isplitr
      · ipureintro; exact hJmL
      have hpt : ∀ (dir : GoString) (J : Ino), walTmpsRes (hG := ⟨G, L⟩) J ⊢
          (if dir ∈ ([] : List GoString) then emp else walTmpsRes (hG := ⟨G, L⟩) J) := fun _ _ => by
        rw [if_neg List.not_mem_nil]
      iapply BigSepM.bigSepM_mono (fun {k J} _ => hpt k J) $$ Htmp
    isplitl [Hdk Hcp]
    · iexists ∅, none
      iframe Hdk Hcp
      ipureintro
      refine ⟨fun dir j X hk => by simp at hk, fun dir d lay hd hl _ => ?_,
        dirClaimsOk_start C Mr R jr s Ls V cl hV hcl hdirs hdirs1 hstart⟩
      exact crashOk_start C hC Mr R jr s Ls V cl hV hcl harea hdirs hstart dir d lay hd hl
    isplitr
    · ipureintro
      exact (walsAt_start C Mr R jr s Ls V cl hV hcl hstart).weak
    isplitl [Hnm Hnw Hns Hsp]
    · unfold walNamesRes
      iexists none, nameClaimsOf jr Ls cl
      iframe Hnm Hnw Hns
      isplitr
      · ipureintro
        exact ⟨fun nm hnm => (hW nm).1 hnm, fun dir lay hl _ => (hW lay.nm).2 ⟨dir, lay, hl, rfl⟩⟩
      isplitr
      · ipureintro; intro dir d ho; cases ho
      iexists qs; iexact Hsp
    ipureintro; exact ⟨hbd, hdr⟩
  imodintro
  unfold walInv
  iframe Hinv
  isplitr
  · ipureintro; exact hWR
  iexists Ls
  iframe Hc3 Hnwf
  ipureintro; exact ⟨hstart, hW⟩

/-! ## The `_keep` lemmas (as `AbsDisk/Specs.lean`'s, over `walCrashWal`) -/

variable (W W' : WalGS GF)

/-- The program's copy of the WAL in `dir` is below a real one. -/
theorem walDiskAt_crash_real {M : GMap GoString WalDur} {s : AbsDiskState} {dir : GoString}
    {d : WalDur} (HMd : walOptLe (some d) (M !! dir)) (HMs : walMapLe M s.wal) :
    ∃ dr, s.wal !! dir = some dr ∧ walDurLe d dr := by
  obtain ⟨dg, hdg, hle1⟩ := (walOptLe_some_iff d _).1 HMd
  have h2 := HMs dir
  rw [hdg] at h2
  obtain ⟨dr, hdr, hle2⟩ := (walOptLe_some_iff dg _).1 h2
  exact ⟨dr, hdr, walDurLe_trans hle1 hle2⟩

/-- A crash's new WAL is above the program's copy with the crash's fields. -/
theorem walDurLe_crash {d dr : WalDur} {I : List (WalOpG WalEnt)} {k : Nat} (hle : walDurLe d dr) :
    walDurLe { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }
      { dr with H := I, cut := k, unl := min dr.unl I.length, pur := min dr.pur I.length } :=
  ⟨rfl, by simp only [hle.2.1], by simp only [hle.2.2.1], rfl, hle.2.2.2.2.1, hle.2.2.2.2.2.1,
    hle.2.2.2.2.2.2.1, hle.2.2.2.2.2.2.2⟩

/-- **The crash view, keeping the old program's map.** -/
theorem walCrash_view_keep (M : GMap GoString WalDur) :
    ⊢@{IProp GF} walCrashWal W W' -∗ walOwn (W := W) M -∗ walOwn (W := W) M ∗
      ∃ s s' : AbsDiskState, ⌜walStCrash s s' ∧ walMapLe M s.wal⌝ ∗
        walGhost (W := W) s ∗ walOwn (W := W') s'.wal ∗ walPast (W := W') s' := by
  unfold walCrashWal
  iintro ⟨%s, %s', %hc, Hg, HM', Hp'⟩ HM
  icases walOwn_agree (W := W) s M $$ Hg HM with %HMs
  iframe HM
  iexists s, s'
  iframe Hg HM' Hp'
  ipureintro; exact ⟨hc, HMs⟩

theorem walDiskAt_crash_keep (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAt (W := W) dir d -∗ walSyncedLb (W := W) dir n -∗ walNamed (W := W) dir -∗
      walDiskAt (W := W) dir d ∗ ∃ (I : List (WalOpG WalEnt)) (k : Nat),
        ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
        walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗
        walSyncedLb (W := W') dir n ∗ walNamed (W := W') dir := by
  unfold walDiskAt walDirIs walSyncedLb walNamed
  iintro Hcs ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩ ⟨%q, %dq, Hq, %Hdq⟩
  icases walCrash_view_keep W W' M $$ Hcs HM with ⟨HM, %s, %s', ⟨%hc, %HMs⟩, HP, HM', #Hp'⟩
  obtain ⟨dr, hdr, hle⟩ := walDiskAt_crash_real HMd HMs
  icases walPast_ghost_le (W := W) s p $$ HP Hp with %Hlp
  icases walPast_ghost_le (W := W) s q $$ HP Hq with %Hlq
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2.2 dir dp Hdp.1
  obtain ⟨d2, h2, -, -, hn2⟩ := Hlq.2.2 dir dq Hdq.1
  rw [hdr] at h1 h2; cases h1; cases h2
  have hn : n ≤ dr.m := Nat.le_trans Hdp.2 hm1
  have hnamed : dr.named = true := hn2 Hdq.2
  obtain ⟨-, -, hcw, -⟩ := hc
  rcases hcw dir dr hdr with ⟨hnf, -⟩ | ⟨I, k, hI, hk, hs'⟩
  · rw [hnamed] at hnf; cases hnf
  obtain ⟨j, hj1, hj2, hj3⟩ := hI
  isplitl [HM]
  · iexists M; iframe HM; ipureintro; exact HMd
  iexists I, k
  isplitr
  · ipureintro
    refine ⟨⟨j, Nat.le_trans hn hj1, ?_, ?_⟩, ?_⟩
    · rw [hle.1]; exact hj2
    · rw [hle.1]; exact hj3
    · rw [hle.2.2.1]; exact hk
  isplitl [HM']
  · iexists s'.wal; iframe HM'; ipureintro; rw [hs']; exact walDurLe_crash hle
  isplitr
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hn⟩
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hnamed⟩

theorem walDiskAt_crash_any_keep (dir : GoString) (d : WalDur) (n : Nat) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAt (W := W) dir d -∗ walSyncedLb (W := W) dir n -∗
      walDiskAt (W := W) dir d ∗ ((walAbsent (W := W') dir ∗ ⌜d.named = false⌝) ∨
        ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H n I ∧ k ≤ min d.pur I.length⌝ ∗
          walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length } ∗ walSyncedLb (W := W') dir n) := by
  unfold walDiskAt walAbsent walDirIs walSyncedLb
  iintro Hcs ⟨%M, HM, %HMd⟩ ⟨%p, %dp, Hp, %Hdp⟩
  icases walCrash_view_keep W W' M $$ Hcs HM with ⟨HM, %s, %s', ⟨%hc, %HMs⟩, HP, HM', #Hp'⟩
  obtain ⟨dr, hdr, hle⟩ := walDiskAt_crash_real HMd HMs
  icases walPast_ghost_le (W := W) s p $$ HP Hp with %Hlp
  obtain ⟨d1, h1, hm1, -, -⟩ := Hlp.2.2 dir dp Hdp.1
  rw [hdr] at h1; cases h1
  have hn : n ≤ dr.m := Nat.le_trans Hdp.2 hm1
  obtain ⟨-, -, hcw, -⟩ := hc
  isplitl [HM]
  · iexists M; iframe HM; ipureintro; exact HMd
  rcases hcw dir dr hdr with ⟨hnf, hnone⟩ | ⟨I, k, hI, hk, hs'⟩
  · ileft
    isplitl [HM']
    · iexists s'.wal; iframe HM'; ipureintro; rw [hnone]; trivial
    · ipureintro
      cases hdn : d.named
      · rfl
      · rw [hle.2.2.2.2.2.2.2 hdn] at hnf; cases hnf
  obtain ⟨j, hj1, hj2, hj3⟩ := hI
  iright
  iexists I, k
  isplitr
  · ipureintro
    refine ⟨⟨j, Nat.le_trans hn hj1, ?_, ?_⟩, ?_⟩
    · rw [hle.1]; exact hj2
    · rw [hle.1]; exact hj3
    · rw [hle.2.2.1]; exact hk
  isplitl [HM']
  · iexists s'.wal; iframe HM'; ipureintro; rw [hs']; exact walDurLe_crash hle
  · iexists s', _; iframe Hp'; ipureintro; exact ⟨hs', hn⟩

theorem walDiskAt_crash_any_keep0 (dir : GoString) (d : WalDur) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAt (W := W) dir d -∗
      walDiskAt (W := W) dir d ∗ ((walAbsent (W := W') dir ∗ ⌜d.named = false⌝) ∨
        ∃ (I : List (WalOpG WalEnt)) (k : Nat), ⌜walImg d.H 0 I ∧ k ≤ min d.pur I.length⌝ ∗
          walDiskAt (W := W') dir { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }) := by
  unfold walDiskAt walAbsent walDirIs
  iintro Hcs ⟨%M, HM, %HMd⟩
  icases walCrash_view_keep W W' M $$ Hcs HM with ⟨HM, %s, %s', ⟨%hc, %HMs⟩, -, HM', -⟩
  obtain ⟨dr, hdr, hle⟩ := walDiskAt_crash_real HMd HMs
  obtain ⟨-, -, hcw, -⟩ := hc
  isplitl [HM]
  · iexists M; iframe HM; ipureintro; exact HMd
  rcases hcw dir dr hdr with ⟨hnf, hnone⟩ | ⟨I, k, hI, hk, hs'⟩
  · ileft
    isplitl [HM']
    · iexists s'.wal; iframe HM'; ipureintro; rw [hnone]; trivial
    · ipureintro
      cases hdn : d.named
      · rfl
      · rw [hle.2.2.2.2.2.2.2 hdn] at hnf; cases hnf
  obtain ⟨j, -, hj2, hj3⟩ := hI
  iright
  iexists I, k
  isplitr
  · ipureintro
    refine ⟨⟨j, Nat.zero_le _, ?_, ?_⟩, ?_⟩
    · rw [hle.1]; exact hj2
    · rw [hle.1]; exact hj3
    · rw [hle.2.2.1]; exact hk
  iexists s'.wal; iframe HM'; ipureintro; rw [hs']; exact walDurLe_crash hle

theorem walAbsent_crash_keep (dir : GoString) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walAbsent (W := W) dir -∗ walAbsent (W := W) dir ∗ walAbsent (W := W') dir := by
  unfold walAbsent walDirIs
  iintro Hcs ⟨%M, HM, %HMd⟩
  icases walCrash_view_keep W W' M $$ Hcs HM with ⟨HM, %s, %s', ⟨%hc, %HMs⟩, -, HM', -⟩
  have hs : s.wal !! dir = none := by
    have h := HMs dir
    rw [(walOptLe_none_iff _).1 HMd] at h
    exact (walOptLe_none_iff _).1 h
  isplitl [HM]
  · iexists M; iframe HM; ipureintro; exact HMd
  iexists s'.wal; iframe HM'; ipureintro; rw [hc.2.2.2 dir hs]; trivial

theorem dirDurable_crash_keep (d : GoString) :
    ⊢@{IProp GF} walCrashWal W W' -∗ dirDurable (W := W) d -∗
      walCrashWal W W' ∗ dirDurable (W := W') d := by
  unfold walCrashWal dirDurable
  iintro ⟨%s, %s', %hc, HG, HM', #Hp'⟩ ⟨%p, Hp, %Hd⟩
  icases walPast_ghost_le (W := W) s p $$ HG Hp with %Hlp
  isplitl [HG HM']
  · iexists s, s'; iframe HG HM' Hp'; ipureintro; exact hc
  · iexists s'; iframe Hp'; ipureintro; rw [hc.2.1]; exact Hlp.2.1 d Hd

theorem walArea_crash_keep (r : GoString) :
    ⊢@{IProp GF} walCrashWal W W' -∗ walArea (W := W) r -∗
      walCrashWal W W' ∗ walArea (W := W') r := by
  unfold walCrashWal walArea
  iintro ⟨%s, %s', %hc, HG, HM', #Hp'⟩ ⟨%p, Hp, %Hr⟩
  icases walPast_ghost_le (W := W) s p $$ HG Hp with %Hlp
  isplitl [HG HM']
  · iexists s, s'; iframe HG HM' Hp'; ipureintro; exact hc
  · iexists s'; iframe Hp'; ipureintro; rw [hc.1, Hlp.1, Hr]

end crash

end WalFs
end EtcdGrove
end Perennial

end
