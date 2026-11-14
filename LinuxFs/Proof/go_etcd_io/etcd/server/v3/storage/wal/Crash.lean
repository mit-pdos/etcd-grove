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

`walInv_alloc`: the new generation's invariant from its start, once the tree is in shared mode and
the WAL's names are claimed (`wp_osShare`, `osNames_split`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashStart
public import GooseLang.Ext.Fs.CrashTakeFiles
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashTakeSeg
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced

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
them: `fo`); the layouts (`WalsStart`), every segment one of `is`, its `OsMeta` and bytes those of its
file on disk, the segments' inodes distinct. -/
def walStart (L : GooseLocalGS GF) (W : WalGS GF) (C : WalCodec) (Mr : WalMarshal) (R : Roots)
    (jr : Ino) (r : GoString) (s : AbsDiskState) (m : Tree) : IProp GF :=
  iprop(∃ (Ls : GMap GoString WalLay) (is : List Ino) (fo : Ino → Option Fs.OsFile),
    walGhost (W := W) s ∗ walCreatingAuth (W := W) ∅ ∗ walTailsAuth (W := W) ∅ ∗
    walParkAuth (W := W) true ∗ walDirKeysAuth (W := W) ∅ ∗ walCutAuth (W := W) none ∗
    walOutAuth (W := W) WalOut.empty ∗ walNamesAuth (W := W) none ∗ walSplitAuth (W := W) [] ∗
    walSplitFrag (W := W) [] ∗ walOldsAuth (W := W) ∅ ∗ ⌜s.area = r⌝ ∗
    ([∗list] i ∈ is, osFileStartO (L := L) i (fo i)) ∗
    ⌜is.Nodup ∧ ((segsAll Ls).map (·.ino)).Nodup ∧ WalsStart C Mr R jr s Ls m ∧
      ∀ dir lay, Ls !! dir = some lay → ∀ g ∈ lay.segs,
      g.ino ∈ is ∧ ∃ f, fo g.ino = some f ∧ g.om = initMeta f ∧ g.bs = f.contents.map durB⌝)

/-- **The crash view** (as `absDiskCrashWal`): the old generation's ghost authorities at the old
real state `s`, the new generation's program map at the crashed state `s'` and its fact. -/
def walCrashWal (W W' : WalGS GF) : IProp GF :=
  iprop(∃ s s' : AbsDiskState, ⌜walStCrash s s'⌝ ∗ walGhost (W := W) s ∗
    walOwn (W := W') s'.wal ∗ walPast (W := W') s')

theorem walsOk_nodup {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (h : WalsOk C Mr R jr s Ls cl n) :
    ((segsAll Ls).map (·.ino)).Nodup := h.2.2.1

theorem walsOk_cut {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (h : WalsOk C Mr R jr s Ls cl n) :
    ∀ g ∈ segsAll Ls, g.om.cut = none := h.2.2.2.1

/-- **The WAL's crash** (plan §2.2): from the old generation's invariant, its `crashed` (from the
crash adequacy theorem) and the WAL's crash token, the shared mode's invariant, the generation's
`crashRest` (the tree untaken) and W1 (`hQ`): a new generation of the WAL's names, the crash view,
the new generation's start over the crashed tree, its lock and crash tokens, and `crashRest` back
(the segments taken, the tree not). -/
theorem walInv_crash (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (Q : Fs.OsState → Fs.OsState → Prop)
    (hQ : ∀ st st', Q st st' → W1 C st st') (hPre : AbsDiskGpreS GF) (L L' : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (V' : Hist) (E : CoPset)
    (hE : ↑walN ⊆ E) (hE' : ↑osShN ⊆ E) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ crashed (hC := L.goose_crashGS) -∗
      walCrashTok (W := W) -∗ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) [] false V' ={E}=∗
      ∃ (W' : WalGS GF) (s' : AbsDiskState) (D : List Ino),
        walCrashWal W W' ∗ ⌜s'.area = r ∧ DirsAvoid R jr s'⌝ ∗ walStart L' W' C Mr R jr r s' V'.now ∗
        walPast (W := W') s' ∗ walUnlockedTok (W := W') ∗ walCrashTok (W := W') ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' := by
  iintro #Hinv #Hcrd Htok #Hsh Hcr
  -- open the old invariant and close it with the crash tokens
  unfold walInv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (Hb | ⟨-, >Ht⟩)
  rotate_left
  · iexfalso; iapply walCrashTok_excl $$ Htok Ht
  imod Hclose $$ [Htok] with -
  · inext; iright; iframe Hcrd Htok
  icases Hb with ⟨%s, >Hb⟩
  iunfold walInvBody at Hb
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, #Hcm, Hlays, %Hok, -, -, -, %Han, %Hnm, -, -, %HAt, -, %Hbd⟩
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
  iunfold laysResF at Hlays
  icases crashRest_take_segs Q L L' [] false V' F (segsAll Ls) (by simp) (walsOk_nodup Hok)
    (walsOk_cut Hok) $$ Hcr Hlays with ⟨%st, %st', %Hfs, Hstarts, Hcr, -⟩
  obtain ⟨hQs, htree, hfiles⟩ := Hfs
  obtain ⟨s', Ls', hcrash, harea', hk', hstart, hnd', hsegs⟩ :=
    walCrash_pure C hC Mr R jr s Ls cl n V'.now st st' Hok Han.1 Hnm hk (fun _ _ hl => HAt.ne hl) Hreg htree (hQ _ _ hQs) hfiles
  -- the new generation's ghost state
  imod walGhost_init hPre s' hk' with
    ⟨%W', Hg', HM', #Hp', Hu', Hc', Hcr', Ht', Hpk', Hdk', Hcp', Hpo', Hnm', Hnw', Hnwf', Ho'⟩
  imodintro
  iexists W', s', ((segsAll Ls).map (·.ino) ++ [])
  iframe Hu' Hc' Hcr Hp'
  isplitl [Hg HM']
  · unfold walCrashWal
    iexists s, s'
    iframe Hg HM' Hp'
    ipureintro; exact hcrash
  isplitr
  · ipureintro
    refine ⟨by rw [harea', Har], fun dd hdd => Han.2 dd ?_⟩
    rw [← hcrash.2.1]; exact hdd
  unfold walStart
  iexists Ls', (segsAll Ls).map (·.ino), (fun i => st'.fs.files !! i)
  iframe Hg' Hstarts Hcr' Ht' Hpk' Hdk' Hcp' Hpo' Hnm' Hnw' Hnwf' Ho'
  ipureintro
  exact ⟨by rw [harea', Har], walsOk_nodup Hok, hnd', hstart, hsegs⟩

/-- Every name of a set. -/
theorem restrictN_all (e : Ents) : restrictN (.except []) e = e := by
  apply GMap.ext; intro b
  exact restrictN_lookup _ _ _ (by simp [NameSet.Mem])

theorem entsOf_lookup (m : Tree) (j : Ino) (b : GoString) : entsOf m j !! b = m.entry j b := by
  unfold entsOf Tree.entry
  cases m !! j <;> rfl

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
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨hw ▸ h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

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
      crashOkW_of_crashOk ?_⟩
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
    ∀ dir d lay, s.wal !! dir = some d → Ls !! dir = some lay → CrashOkA C Mr d lay none cl 0 := by
  have hc : ∀ c ∈ cl, c.2.2 = ⟨restrictN c.2.1 (entsOf V.now c.1), [],
      restrictN c.2.1 (entsOf V.now c.1)⟩ := fun c h => by rw [hcl c h, namesOf_nil hV]
  have hlog : ∀ c ∈ cl, c.2.2.ents = [] := fun c h => by rw [hc c h]
  intro dir d lay0 hd hL0
  obtain ⟨lay, nm, hL, hin, hjr, hnm, he, habs, hfit, h1, h2, h3, hlast⟩ := hst.1 dir d hd
  rw [show lay0 = lay from Option.some.inj (hL0.symm.trans hL)]
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
    (hst : WalsStart C Mr R jr s Ls V.now) : WalsNamed Ls cl 0 := by
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
  refine ⟨fun hj ⟨X, hX, hm, _⟩ => ?_, fun m' hreg => ?_⟩
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
    (hst : WalsStart C Mr R jr s Ls V.now) : WalsAt jr Ls cl := by
  intro dir lay hL
  refine ⟨hst.2.2.2.2.2 dir lay hL, fun N h hm hN => ?_⟩
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
  refine ⟨walTmps, h, ⟨hst.2.2.2.2.2 dir lay hL, walTmps_not_wal, honce, ?_,
    fun c' hc' hne hcj b hb => hex c' hc' hne hcj b (fun hbX => by
      rw [walTmps_not_wal b hbX] at hb; cases hb)⟩, walTmps_not_broken, hex⟩
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
    (hwn : ∀ dir lay, Ls !! dir = some lay → walNameOk lay.nm) (hA : WalsAt jr Ls cl) :
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
      exact ⟨hok _ _ hc, hwn dir lay hl, fun d' l' hl' he => he ▸ hA.at hl' hc (by rw [he]; simp [NameSet.Mem])⟩
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
    (hdok : DirsOk R s cl 0) (hav : DirsAvoid R jr s) (Jm : GMap GoString Ino)
    (hJm : ∀ dir nm J, InArea r dir nm → V.now.entry jr nm = some (.dir J) → Jm !! dir = some J)
    (hnames : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (jr, NameSet.only [nm], h) ∈ cl)
    (hnok : ∀ b h, (jr, NameSet.only [b], h) ∈ cl → NameOk b) (hbd : WalsBounded s) (qs : Qp)
    (E : CoPset) :
    ⊢ walStart L W C Mr R jr r s V.now -∗
      osClaims L (cl.map (fun c => (c, DFrac.own 1))) -∗
      ([∗map] _dir ↦ J ∈ Jm, walTmpsRes (hG := ⟨G, L⟩) J) -∗
      osPathS (L := L) R r (DFrac.own qs) jr ={E}=∗
      walInv (L := L) (W := W) C Mr R jr r ∗
      ∃ Ls, ⌜WalsStart C Mr R jr s Ls V.now⌝ ∗
        walSplitFrag (W := W) (nameClaimsOf jr Ls cl) ∗
        ⌜∀ nm, nm ∈ nameClaimsOf jr Ls cl ↔ ∃ dir lay, Ls !! dir = some lay ∧ lay.nm = nm⌝ ∗
        [∗list] c ∈ cl, if WalDirClaimOf Ls c ∨ NameClaimOf jr Ls c then emp else
          osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 := by
  iintro Hst Hcl Htmp Hsp
  unfold walStart
  icases Hst with ⟨%Ls, %is, %fo, Hg, Hcr, Htl, Hpk, Hdk, Hcp, Hpo, Hnm, Hnw, Hnwf, Ho, %Har, Hfs, %Hp⟩
  obtain ⟨-, hnd, hstart, hsegs⟩ := Hp
  -- the segments' start resources, halved
  have hsub : ((segsAll Ls).map (·.ino)) ⊆ is := fun i hi => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hi
    obtain ⟨dir, lay, hl, hg'⟩ := segsAll_mem hg
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
    obtain ⟨dir, lay, hl, hg'⟩ := segsAll_mem (List.mem_of_getElem? hk)
    obtain ⟨-, f, hf, hom, hbs⟩ := hsegs dir lay hl g hg'
    rw [hf]
    exact segStart_halves L g f hom hbs
  have hcut : ∀ g ∈ segsAll Ls, g.om.cut = none := by
    intro g hg
    obtain ⟨dir, lay, hl, hg'⟩ := segsAll_mem hg
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
      [Hg Hc1 Hi Hcr Htl Hpk Hpo Hp Hc2 Hdk Hcp Htmp Hnm Hnw Hsp Hns Ho]
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
    isplitl [Htl Ho]
    · unfold walTailsRes
      ihave Ho := walOldsRes_init (W := W) Ls $$ Ho
      iexists ∅
      iframe Htl Ho
      isplitr
      · ipureintro; intro i hi; exact absurd (GMap.lookup_empty (K := Ino) (V := SegFl) i) hi
      isplitr
      · ipureintro
        intro dir d lay _ hd hl
        obtain ⟨lay', nm, hl', -, -, -, -, -, -, -, hwz, hzS, hlast⟩ := hstart.1 dir d hd
        rw [hl] at hl'; cases hl'
        refine ⟨fun g hg => (hlast g hg).2, hwz.trans hzS, fun g hg => ⟨?_, ?_⟩⟩
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
      exact walsNamed_start C Mr R jr s Ls V cl hV hcl hdirs hstart
    isplitl [Hpk Hpo Hc2 Hp Htmp]
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
      unfold walTmpParked
      iexists Jm
      isplitr
      · ipureintro
        intro dir lay hl
        obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
          cases h : s.wal !! dir with
          | none => rw [hstart.2.1 dir h] at hl; cases hl
          | some d => exact ⟨d, rfl⟩
        obtain ⟨lay', nm, hL', hin, -, -, he, -⟩ := hstart.1 dir d hd
        rw [hl] at hL'; cases hL'
        exact hJm dir nm lay.j (Har ▸ hin) he
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
      exact walsAt_start C Mr R jr s Ls V cl hV hcl hstart
    isplitl [Hnm Hnw Hns Hsp]
    · unfold walNamesRes
      iexists none, nameClaimsOf jr Ls cl
      iframe Hnm Hnw Hns
      isplitr
      · ipureintro
        exact ⟨fun nm hnm => (hW nm).1 hnm, fun dir lay hl _ => (hW lay.nm).2 ⟨dir, lay, hl, rfl⟩⟩
      iexists qs; iexact Hsp
    ipureintro; exact hbd
  imodintro
  unfold walInv
  iframe Hinv
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
