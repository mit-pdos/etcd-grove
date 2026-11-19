/- Lean-first (no Rocq counterpart).

# The members' WAL areas, allocated at adequacy (wal-link P2, 2026-11-19)

`notes/wal-link-scope.md` §3.4 P2 (approved by the user 2026-11-17): each member's WAL is in a
dedicated WAL directory (`srvWalDirOf dd`, `WalLayout.lean`), the `wal` of an area of its own, a root
of the Linux file extension (`walAreaOf dd`) that exists at start and holds nothing a WAL function may
touch (`etcdWalAreasInit`, the closed theorems' premise, `WalAreasInit.lean`). Before the program's first step its proof
switches the file extension to the shared mode (`wp_osShareE`) and allocates each area's WAL invariant
(`walBoot0`, `Proof/.../storage/wal/Boot0.lean`), from which it builds each member's `walAreaFresh`
(what `bootstrap`'s contract takes for the WAL, `wal.bootRes`): `walAreasFresh_boot`, `wp_walAreas`.
Untrusted, but for `etcdWalAreasInit`, a premise of the closed theorems (a world premise, as
`dataDirsAbsent`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Boot0
public import GooseLang.Ext.Fs.TreeSharedSwitchE
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode


/-! ## Pure facts -/

/-- A root's path is a clean absolute path (`RootForm`'s names are path elements). -/
theorem cleanAbsPath_of_rootForm {r : GoString} (h : Fs.RootForm r) : cleanAbsPath r := by
  obtain ⟨cs, hne, hok, rfl⟩ := h
  refine ⟨cs, hne, fun c hc => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := hok c hc
    exact ⟨h1, h4, h2, h3⟩
  · simp only [joinPath, List.nil_append, List.flatMap_def]
    congr 1

/-- The areas of distinct data directories are distinct paths. -/
theorem walAreaOf_inj {d d' : GoString} (h : walAreaOf d = walAreaOf d') : d = d' := by
  unfold walAreaOf at h
  exact List.append_cancel_left h

/-- A root's directory names one root. -/
theorem root_ino_inj {R : Fs.Roots} (hR : Fs.RootsOk R) {r r' : GoString} {j : Fs.Ino}
    (h : (r, j) ∈ R) (h' : (r', j) ∈ R) : r = r' := by
  have := Fs.eq_of_nodup_map hR.2.1 h h' rfl
  simpa using congrArg Prod.fst this

/-! ## The allocation -/

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
  [HasExt Fs.fsExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]

/-- **The WAL area `r` (the directory `j` under the roots `R`) with the WAL directory `dir`**, over the
program's file system instances, at the WAL ghost state `W`, every inode in the no-I/O-error set. -/
abbrev etcdWalArea (W : WalFs.WalGS GF) (hsat : Fs.FsStepSat (Fs.NoIoErr allIo)) (R : Fs.Roots)
    (j : Fs.Ino) (r dir : GoString) : WalA GF where
  ext := inferInstance
  semOk := inferInstance
  has := inferInstance
  W := W
  Sio := allIo
  sat := hsat
  cov := fun _ _ => trivial
  R := R
  jr := j
  r := r
  dir := dir

/-- The area is durable at the first boot (as WalTester's `dirDurable_boot0`). -/
theorem walDirDurable_boot0 [W : WalFs.WalGS GF] (r : GoString) :
    ⊢@{IProp GF} WalFs.walPast (W := W) (WalFs.walBoot0St r) -∗ WalFs.dirDurable (W := W) r := by
  iintro #Hp
  unfold WalFs.dirDurable
  iexists WalFs.walBoot0St r
  iframe Hp
  ipureintro
  simp [WalFs.walBoot0St]

/-- **The members' WAL areas, one ghost generation each** (`walBoot0` for each area in turn; see the
file header): from the shared mode's resources, the whole claims of the directories `Js` (the areas'
among them) and the whole call permissions of the keys of `M` (the areas' roots among them), each data
directory `d` of `Ds` gives its `walAreaFresh (srvWalDirOf d)`. -/
theorem walAreasFresh_boot [go.BasicIntoValInj] (hPre : AbsDiskGpreS GF)
    (hsat : Fs.FsStepSat (Fs.NoIoErr allIo)) (R : Fs.Roots) (V : Fs.Hist) (hV : V.2 = [])
    (hR : Fs.RootsOk R) (hrb : ReceiptBoundLe GF (2 ^ 62)) :
    ∀ (Ds : List GoString) (Js : List Fs.Ino) (M : GMap GoString Unit), Ds.Nodup →
      (∀ d ∈ Ds, ∃ j, (walAreaOf d, j) ∈ R ∧ j ∈ Js ∧
        ∀ b, WalFs.AreaSlot b → V.now.entry j b = none) →
      (∀ d ∈ Ds, M !! walAreaOf d = some ()) →
    ⊢ Fs.osInv (L := hG.goose_localGS) -∗ Fs.osSharedInv (L := hG.goose_localGS) R -∗
      Fs.osAboveInv (L := hG.goose_localGS) -∗
      ([∗list] j ∈ Js, Fs.osNames (L := hG.goose_localGS) j (.except []) (DFrac.own 1)
        (Fs.namesOf V j (.except []))) -∗
      ([∗map] r ↦ _u ∈ M, Fs.osCallPerm (L := hG.goose_localGS) r 1) ={⊤}=∗
      [∗list] d ∈ Ds, walAreaFresh (GF := GF) (srvWalDirOf d) := by
  intro Ds
  induction Ds with
  | nil =>
    intro _ _ _ _ _
    iintro _ _ _ _ _
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons d Ds ih =>
    intro Js M hnd hJ hM
    obtain ⟨j, hrj, hjJ, hsl⟩ := hJ d List.mem_cons_self
    have hnd' := (List.nodup_cons.1 hnd)
    have hJ' : ∀ d' ∈ Ds, ∃ j', (walAreaOf d', j') ∈ R ∧ j' ∈ Js.erase j ∧
        ∀ b, WalFs.AreaSlot b → V.now.entry j' b = none := by
      intro d' hd'
      obtain ⟨j', hrj', hj'J, hsl'⟩ := hJ d' (List.mem_cons_of_mem _ hd')
      refine ⟨j', hrj', ?_, hsl'⟩
      have hne : j' ≠ j := by
        rintro rfl
        have := walAreaOf_inj (root_ino_inj hR hrj' hrj)
        subst this
        exact hnd'.1 hd'
      exact (List.mem_erase_of_ne hne).2 hj'J
    have hM' : ∀ d' ∈ Ds, GMap.delete (walAreaOf d) M !! walAreaOf d' = some () := by
      intro d' hd'
      have hne : walAreaOf d ≠ walAreaOf d' := by
        intro h
        have := walAreaOf_inj h
        subst this
        exact hnd'.1 hd'
      rw [GMap.lookup_delete_ne _ hne]
      exact hM d' (List.mem_cons_of_mem _ hd')
    iintro #Hos #Hsh #Hab Hall Hperms
    imod WalFs.walBoot0 hPre walCodec walCodec_ok walSrvMr hG.goose_localGS R j (walAreaOf d) V hV hR
      hrj Js hjJ hsl hrb walSrvMr_encState_lt ⊤ CoPset.subseteq_top $$ Hos Hsh Hab Hall
      with ⟨%W, #Hok, Hres, Hu, -, #Hp, Hown, -, Hrest⟩
    imod Fs.osPathS_root (L := hG.goose_localGS) R (walAreaOf d) j (DFrac.own 1) hrj
      CoPset.subseteq_top $$ Hsh with Hsp
    icases (BigSepM.bigSepM_delete (M := GMap GoString)
      (Φ := fun (r' : GoString) (_u : Unit) => Fs.osCallPerm (L := hG.goose_localGS) r' 1)
      (hM d List.mem_cons_self)).1 $$ Hperms with ⟨Hpd, Hperms⟩
    imod ih (Js.erase j) (GMap.delete (walAreaOf d) M) hnd'.2 hJ' hM' $$ Hos Hsh Hab Hrest Hperms with Hrest
    ihave #Hdd := walDirDurable_boot0 (W := W) (walAreaOf d) $$ Hp
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hrest
    unfold walAreaFresh
    iexists etcdWalArea W hsat R j (walAreaOf d) (srvWalDirOf d)
    isplitr
    · ipureintro
      exact ⟨rfl, srvWalDirOf_inArea d, cleanAbsPath_of_rootForm ((hR.2.2 _ hrj).1)⟩
    dsimp only [etcdWalArea]
    rw [Fs.callKey_eq hR hrj (.inl rfl)]
    iframe Hok Hdd Hsp Hres Hpd Hu
    unfold WalFs.walAbsent WalFs.walDirIs
    iexists ∅
    iframe Hown
    ipureintro
    show walOptLe none ((∅ : GMap GoString WalDur) !! srvWalDirOf d)
    rw [GMap.lookup_empty]; trivial

/-- **The members' WAL areas, before the program's first step** (see the file header): over the file
extension's initial state `st` (`FsInit`, no I/O error assumed: `hsat`) with the members' areas as
`etcdWalAreasInit` says, the WP of a non-value `e` from the file extension's start resources (the
invariant of the mapped cells and the tree's whole legacy history) follows from its WP given each data
directory's `walAreaFresh`. -/
theorem wp_walAreas [go.BasicIntoValInj] (hPre : AbsDiskGpreS GF)
    (hsat : Fs.FsStepSat (Fs.NoIoErr allIo)) (st : Fs.OsState) (hfs : Fs.FsInit st)
    (Ds : List GoString) (hDs : Ds.Nodup) (hW : etcdWalAreasInit st Ds)
    (hrb : ReceiptBoundLe GF (2 ^ 62))
    (e : Expr) (he : toVal e = none) (Φ : val → IProp GF) :
    ⊢ Fs.osInv (L := hG.goose_localGS) -∗
      Fs.osTree (L := hG.goose_localGS) (DFrac.own 1) st.fs.roots (st.fs.treeDur, []) -∗
      (([∗list] d ∈ Ds, walAreaFresh (GF := GF) (srvWalDirOf d)) -∗
        WP e @ Stuckness.NotStuck; ⊤ {{ Φ }}) -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  have hR : Fs.RootsOk st.fs.roots := hfs.2.2.2.1
  have htw : Fs.TreeWf st.fs.roots st.fs.treeDur := hfs.2.2.2.2.1
  iintro #Hinv Ht Hk
  iapply Fs.wp_osShareE (L := hG.goose_localGS) st.fs.roots (st.fs.treeDur, []) e he
    CoPset.subseteq_top Φ $$ Hinv Ht
  iintro #Hsh #Hab Hperms #- Hall
  unfold Fs.osCallPerms
  imod walAreasFresh_boot hPre hsat st.fs.roots (st.fs.treeDur, []) rfl hR hrb Ds
    ((GMap.toList (Fs.Hist.now (st.fs.treeDur, []))).map (·.1)) (GMap.delete [] (Fs.permMap st.fs.roots))
    hDs
    (fun d hd => by
      obtain ⟨j, hrj, hsl⟩ := hW d hd
      refine ⟨j, hrj, ?_, hsl⟩
      have hj : j ∈ st.fs.treeDur := htw.1 j (Fs.Reach.root _ _ hrj)
      cases hl : st.fs.treeDur !! j with
      | none => have := (GMap.mem_iff _ _).1 hj; rw [hl] at this; cases this
      | some x => exact List.mem_map.2 ⟨(j, x), (GMap.mem_toList _ _ _).2 hl, rfl⟩)
    (fun d hd => by
      obtain ⟨j, hrj, -⟩ := hW d hd
      have hne : ([] : GoString) ≠ walAreaOf d := by
        obtain ⟨cs, hcs, -, hrc⟩ := (hR.2.2 _ hrj).1
        intro h0
        rw [← h0] at hrc
        cases cs with
        | nil => exact hcs rfl
        | cons c cs => simp [joinPath] at hrc
      rw [GMap.lookup_delete_ne _ hne]
      exact Fs.permMap_lookup st.fs.roots _ (.inr ⟨j, hrj⟩))
    $$ Hinv Hsh Hab Hall Hperms with Hw
  iapply Hk $$ Hw

end boot

end EtcdGrove
end Perennial
