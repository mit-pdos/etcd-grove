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
    walGhost (W := W) s ∗ ⌜s.area = r⌝ ∗ ([∗list] i ∈ is, osFileStartO (L := L) i (fo i)) ∗
    ⌜is.Nodup ∧ ((segsAll Ls).map (·.ino)).Nodup ∧ WalsStart C Mr R jr s Ls m ∧
      ∀ dir lay, Ls !! dir = some lay → ∀ g ∈ lay.segs,
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
  let xOf : SegG → Ino × DFrac × OsMeta × List (Nat × DFrac × List ByteG) :=
    fun g => (g.ino, DFrac.own (1 : Qp).half, g.om, [(0, DFrac.own (1 : Qp).half, g.bs)])
  have hsr : ∀ g, segRes (L := L) g ⊣⊢ fileOld (gooseOsGS (L := L)) (xOf g) := by
    intro g
    unfold segRes fileOld osMeta osBytes
    simp only [xOf]
    have hs := BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ (r : Nat × DFrac × List ByteG) => bytesG (gooseOsGS (L := L)) g.ino r.1 r.2.1 r.2.2) (x := (0, DFrac.own (1 : Qp).half, g.bs))
    exact ⟨sep_mono_right hs.2, sep_mono_right hs.1⟩
  have e1 : ([∗list] g ∈ gs, segRes (L := L) g) ⊣⊢
      [∗list] x ∈ gs.map xOf, fileOld (gooseOsGS (L := L)) x := by
    rw [BigSepL.bigSepL_map]
    exact ⟨BigSepL.bigSepL_mono_of_forall (fun {_ x} => (hsr x).1),
      BigSepL.bigSepL_mono_of_forall (fun {_ x} => (hsr x).2)⟩
  have e2 : (gs.map xOf).map (·.1) = gs.map (·.ino) := by simp [xOf]
  have hstarts : ∀ st' : Fs.OsState, ([∗list] x ∈ gs.map xOf, fileStartO (gooseOsGS (L := L')) x.1
      (st'.fs.files !! x.1)) ⊢ [∗list] i ∈ gs.map (·.ino), osFileStartO (L := L') i (st'.fs.files !! i) := by
    intro st'
    rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
    exact BigSepL.bigSepL_mono_of_forall (fun {_ x} => (fileStartO_eq (L := L') x.ino _).1)
  have hD' : ∀ x ∈ gs.map xOf, x.1 ∉ D := by
    intro x hx; obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx; exact hD g hg
  have hnd' : ((gs.map xOf).map (·.1)).Nodup := by rw [e2]; exact hnd
  iintro Hr Hs
  icases e1.1 $$ Hs with Hs
  have H := crashRest_take_list (gooseOsGS (L := L)) Q (gooseOsGS (L := L')) D tt V' (gs.map xOf)
    hD' hnd'
  rw [e2] at H
  icases H $$ Hr Hs with ⟨%st, %st', %h, Hf, Hr, Hs⟩
  iexists st, st'
  iframe Hr
  isplitr
  · ipureintro
    refine ⟨h.1, h.2.1, fun g hg => ?_⟩
    obtain ⟨h1, h2, f, hf, h3⟩ := h.2.2 (xOf g) (List.mem_map_of_mem hg)
    refine ⟨h1, h2, f, hf, fun b y hb => ?_⟩
    have hbl : b < g.bs.length := by
      rcases Nat.lt_or_ge b g.bs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hb; cases hb
    have := h3 (hcut g hg) _ (List.mem_singleton_self _) b hbl
    rw [List.getElem?_eq_getElem hbl] at hb
    cases hb
    simpa using this
  isplitl [Hf]
  · iapply hstarts st' $$ Hf
  iapply e1.2 $$ Hs

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
        walCrashWal W W' ∗ ⌜s'.area = r⌝ ∗ walStart L' W' C Mr R jr r s' V'.now ∗
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
  icases Hb with ⟨%Ls, %cl, %n, Hg, %Har, Hcl, #Hcm, Hlays, %Hok, -⟩
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
  obtain ⟨s', Ls', hcrash, harea', hk', hstart, hnd', hsegs⟩ :=
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

/-- **What the invariant says of the WALs, at the start** (pure): from the start's static relation,
claims with nothing logged on each WAL's area names (`harea`) and wholly on every directory at such
a name (`hdirs`), and the durable directories' resolution (`hdok`). -/
theorem walsOk_start (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (V : Hist) (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (harea : ∃ N h, (jr, N, h) ∈ cl ∧ ∀ nm, walNameOk nm → N.Mem nm)
    (hdirs : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (J, NameSet.except [], h) ∈ cl)
    (hdok : DirsOk R s cl 0) (hst : WalsStart C Mr R jr s Ls V.now)
    (hnd : ((segsAll Ls).map (·.ino)).Nodup) (hcut : ∀ g ∈ segsAll Ls, g.om.cut = none) :
    WalsOk C Mr R jr s Ls cl 0 := by
  have hc : ∀ c ∈ cl, c.2.2 = ⟨restrictN c.2.1 (entsOf V.now c.1), [],
      restrictN c.2.1 (entsOf V.now c.1)⟩ := fun c h => by rw [hcl c h, namesOf_nil hV]
  have hlog : ∀ c ∈ cl, c.2.2.ents = [] := fun c h => by rw [hc c h]
  obtain ⟨N, hN, hNm, hNall⟩ := harea
  have hNb : hN.boot = restrictN N (entsOf V.now jr) := by
    have h := hc _ hNm; simp only at h; rw [h]
  -- the area's WAL names, after a crash the claims allow, are as at the start
  have harea' : ∀ m', RegionCrashed cl 0 m' → ∀ nm, walNameOk nm →
      m'.entry jr nm = V.now.entry jr nm := by
    intro m' hreg nm hnm
    obtain ⟨K, -, -, hval⟩ := hreg
    rw [hval _ hNm nm (hNall nm hnm), valAfter_nil (hlog _ hNm), hNb,
      restrictN_lookup _ _ _ (hNall nm hnm), entsOf_lookup]
  -- a directory at such a name, wholly claimed, keeps its entries
  have hdir' : ∀ m', RegionCrashed cl 0 m' → ∀ J h, (J, NameSet.except [], h) ∈ cl →
      entsOf m' J = entsOf V.now J := by
    intro m' hreg J h hJ
    obtain ⟨K, -, -, hval⟩ := hreg
    apply entsOf_eq_of_entry
    intro b
    rw [hval _ hJ b (by simp [NameSet.Mem]), valAfter_nil (hlog _ hJ)]
    show h.boot !! b = _
    rw [show h = _ from hc _ hJ]
    simp only [restrictN_all]
  refine ⟨fun dir d hd => ?_, hst.2.1, hnd, hcut, fun dir nm hin hnone m' hreg J hJ => ?_, hdok⟩
  · obtain ⟨lay, nm, hL, hin, hjr, hnm, he, habs, hfit, h1, h2, h3, hlast⟩ := hst.1 dir d hd
    obtain ⟨hj, hjm⟩ := hdirs nm lay.j hin.1 he
    have hjc := hc _ hjm
    simp only at hjc
    refine ⟨lay, nm, hj, hL, hin, hjr, hnm, ⟨[], by simp, hjm, ?_⟩, ?_, crashOkW_of_crashOk ?_⟩
    · exact claimCoh_init _ _ _ (by rw [hjc]) (fun b _ => by rw [hjc])
    · rw [hjc]; simp only [restrictN_all]; exact habs
    · refine walAbs_crashOk_start C hC Mr d lay cl 0 (entsOf V.now lay.j) habs hfit hlog
        ⟨hj, hjm, by rw [hjc]; simp only [restrictN_all]⟩ ?_ ⟨h1, h2, h3⟩ hlast
      rw [hjr, hnm]
      refine ⟨N, hN, hNm, hNall nm hin.1, ?_⟩
      rw [hNb, restrictN_lookup _ _ _ (hNall nm hin.1), entsOf_lookup]
      exact he
  · rw [harea' m' hreg nm hin.1] at hJ
    obtain ⟨hJc, hJm⟩ := hdirs nm J hin.1 hJ
    rw [hdir' m' hreg J hJc hJm]
    exact hst.2.2.1 dir nm hin hnone J hJ

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

/-- **The new generation's invariant**, in the tree's shared mode, from the WAL's start (`walStart`
over the shared mode's boot tree `V.now`, nothing logged): the claims `cl` (whole) as the boot
history has them, among them one on the area's WAL names (`harea`) and one on all names of every
directory at such a name (`hdirs`: every WAL directory wholly), and the durable directories' resolution
after any crash they allow (`hdok`); the invariant takes half of each claim, the commit bound 0 and
half of each segment's resources; the program keeps the other halves, with the layouts. -/
theorem walInv_alloc (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (L : GooseLocalGS GF)
    (W : WalGS GF) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState) (V : Hist)
    (cl : List Claim) (hV : V.2 = [])
    (hcl : ∀ c ∈ cl, c.2.2 = namesOf V c.1 c.2.1)
    (harea : ∃ N h, (jr, N, h) ∈ cl ∧ ∀ nm, walNameOk nm → N.Mem nm)
    (hdirs : ∀ nm J, walNameOk nm → V.now.entry jr nm = some (.dir J) →
      ∃ h, (J, NameSet.except [], h) ∈ cl)
    (hdok : DirsOk R s cl 0) (E : CoPset) :
    ⊢ walStart L W C Mr R jr r s V.now -∗
      osClaims L (cl.map (fun c => (c, DFrac.own 1))) ={E}=∗
      walInv (L := L) (W := W) C Mr R jr r ∗
      osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗
      ∃ Ls, ⌜WalsStart C Mr R jr s Ls V.now⌝ ∗ laysRes (L := L) Ls := by
  iintro Hst Hcl
  unfold walStart
  icases Hst with ⟨%Ls, %is, %fo, Hg, %Har, Hfs, %Hp⟩
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
  have hcm0 : ⊢ |==> osCommitLb (L := L) 0 := by
    unfold osCommitLb gCommitLb
    letI := (gooseOsGS (L := L)).osAllG
    exact monoNatLbOwn_0 _
  imod hcm0 with #Hcm
  imod inv_alloc walN E (iprop((∃ s : AbsDiskState, walInvBody (L := L) (W := W) C Mr R jr r s) ∨
      (crashed (hC := L.goose_crashGS) ∗ walCrashTok (W := W)))) $$ [Hg Hc1 Hi] with #Hinv
  · inext; ileft; iexists s
    unfold walInvBody
    iexists Ls, cl, 0
    iframe Hg Hc1 Hcm
    isplitr
    · ipureintro; exact Har
    isplitl [Hi]
    · iapply (laysRes_list (L := L) Ls).2 $$ Hi
    isplitr
    · ipureintro
      exact walsOk_start C hC Mr R jr s Ls V cl hV hcl harea hdirs hdok hstart hnd hcut
    ipureintro
    intro nm hnm
    obtain ⟨N, h, hc, hN⟩ := harea
    exact ⟨N, h, hc, hN nm hnm⟩
  imodintro
  unfold walInv
  iframe Hinv Hc2
  iexists Ls
  isplitr
  · ipureintro; exact hstart
  iapply (laysRes_list (L := L) Ls).2 $$ Hp

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
