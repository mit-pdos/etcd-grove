/- Lean-first (no Rocq counterpart).

# The members' WAL areas, allocated at adequacy (wal-link P2, 2026-11-19)

`notes/wal-link-scope.md` §3.4 P2 (approved by the user 2026-11-17): each member's WAL is in a
dedicated WAL directory (`srvWalDirOf dd`, `WalLayout.lean`), the `wal` of an area of its own, a root
of the Linux file extension (`walAreaOf dd`) that exists at start and holds nothing a WAL function may
touch (`etcdWalAreasInit`, the closed theorems' premise, `WalAreasInit.lean`). Before the program's first step its proof
takes the tree's shared view from the file extension's start (`osShared`, `etcdFs_start`) and allocates each area's WAL invariant
(`walBoot0`, `Proof/.../storage/wal/Boot0.lean`), from which it builds each member's `walAreaFresh`
(what `bootstrap`'s contract takes for the WAL, `wal.bootRes`): `walAreasFresh_boot`, `wp_walAreas`.
Untrusted, but for `etcdWalAreasInit`, a premise of the closed theorems (a world premise, as
`dataDirsAbsent`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Boot0
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Proof.go_etcd_io.etcd.server.v3.storage.WalLayoutFits

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

/-- The areas of distinct members' data directories are distinct paths. -/
theorem walAreaOf_inj {d d' : GoString} (hd : ∃ n, d = memberDataDir n) (hd' : ∃ n, d' = memberDataDir n)
    (h : walAreaOf d = walAreaOf d') : d = d' := by
  obtain ⟨n, rfl⟩ := hd; obtain ⟨n', rfl⟩ := hd'
  rw [walAreaOf_memberDataDir_inj h]

/-- No member's WAL area is a member's data directory. -/
theorem walAreaOf_ne {d d' : GoString} (hd : ∃ n, d = memberDataDir n) (hd' : ∃ n, d' = memberDataDir n) :
    walAreaOf d ≠ d' := by
  obtain ⟨n, rfl⟩ := hd; obtain ⟨n', rfl⟩ := hd'
  exact walAreaOf_ne_memberDataDir n n'

/-- A member's data directory whose WAL directory fits is shorter than `PATH_MAX`. -/
theorem memberDataDir_length_lt {d : GoString} (hd : ∃ n, d = memberDataDir n)
    (hF : Fs.DirFits (srvWalDirOf d)) : d.length < 4096 := by
  obtain ⟨n, rfl⟩ := hd
  have h := hF.1
  rw [srvWalDirOf, walAreaOf_memberDataDir] at h
  simp only [memberDataDir, List.length_append] at h ⊢
  have h1 : (go!"/tmp/etcd-grove-data/" : GoString).length = 21 := by decide
  have h2 : (go!"/tmp/etcd-grove-wal/" : GoString).length = 20 := by decide
  omega

/-- A claim on all the names of `j`, at the history's start, names what the tree has. -/
theorem namesOf_except_cur (V : Fs.Hist) (j : Fs.Ino) (b : GoString) :
    (Fs.namesOf V j (.except [])).cur !! b = V.now.entry j b := by
  unfold Fs.namesOf
  simp only
  rw [Fs.restrictN_lookup _ _ _ (by simp [Fs.NameSet.Mem]), Fs.entsOf_lookup]

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
program's file system instances, at the WAL ghost state `W`, every inode in the no-I/O-error set (and,
wal-fsfix2, the no-lock-error set), `dir` fitting. -/
abbrev etcdWalArea (W : WalFs.WalGS GF) (hsat : Fs.FsStepSat (Fs.NoIoErr allIo))
    (hsatL : Fs.FsStepSat (Fs.NoMapLockErr allIo)) (R : Fs.Roots)
    (j : Fs.Ino) (r dir : GoString) (hfits : Fs.DirFits dir) : WalA GF where
  ext := inferInstance
  semOk := inferInstance
  has := inferInstance
  W := W
  Sio := allIo
  sat := hsat
  satL := hsatL
  cov := fun _ _ => trivial
  R := R
  jr := j
  r := r
  dir := dir
  fits := hfits
  covP := fun _ => trivial

/-- The area is durable at the first boot (as WalTester's `dirDurable_boot0`). -/
theorem walDirDurable_boot0 [W : WalFs.WalGS GF] (r : GoString) :
    ⊢@{IProp GF} WalFs.walPast (W := W) (WalFs.walBoot0St r) -∗ WalFs.dirDurable (W := W) r := by
  iintro #Hp
  unfold WalFs.dirDurable
  iexists WalFs.walBoot0St r
  iframe Hp
  ipureintro
  simp [WalFs.walBoot0St]

/-- **The members' WAL areas and data directories, one ghost generation each** (`walBoot0` for each area
in turn; see the file header): from the shared mode's resources, the whole claims of the directories `Js`
(the areas' and the data directories' among them) and the whole call permissions of the keys of `M` (their
roots among them), each data directory `d` of `Ds` (a member's, `memberDataDir`) gives its
`walAreaFresh (srvWalDirOf d)` and (2026-11-19) its `dataAreaFresh d`. -/
theorem walAreasFresh_boot [go.BasicIntoValInj] (hPre : AbsDiskGpreS GF)
    (hsat : Fs.FsStepSat (Fs.NoIoErr allIo)) (hsatL : Fs.FsStepSat (Fs.NoMapLockErr allIo))
    (R : Fs.Roots) (V : Fs.Hist) (hV : V.2 = [])
    (hR : Fs.RootsOk R) (hrb : ReceiptBoundLe GF (2 ^ 62)) :
    ∀ (Ds : List GoString) (Js : List Fs.Ino) (M : GMap GoString Unit), Ds.Nodup →
      (∀ d ∈ Ds, ∃ n, d = memberDataDir n) →
      (∀ d ∈ Ds, Fs.DirFits (srvWalDirOf d)) →
      (∀ d ∈ Ds, ∃ j, (walAreaOf d, j) ∈ R ∧ j ∈ Js ∧
        ∀ b, WalFs.AreaSlot b → V.now.entry j b = none) →
      (∀ d ∈ Ds, ∃ j, (d, j) ∈ R ∧ j ∈ Js ∧ ∀ b, V.now.entry j b = none) →
      (∀ d ∈ Ds, M !! walAreaOf d = some ()) →
      (∀ d ∈ Ds, M !! d = some ()) →
    ⊢ Fs.osInv (L := hG.goose_localGS) -∗ Fs.osSharedInv (L := hG.goose_localGS) R -∗
      Fs.osAboveInv (L := hG.goose_localGS) -∗
      ([∗list] j ∈ Js, Fs.osNames (L := hG.goose_localGS) j (.except []) (DFrac.own 1)
        (Fs.namesOf V j (.except []))) -∗
      ([∗map] r ↦ _u ∈ M, Fs.osCallPerm (L := hG.goose_localGS) r 1) ={⊤}=∗
      [∗list] d ∈ Ds, memberAreasFresh (GF := GF) d := by
  intro Ds
  induction Ds with
  | nil =>
    intro _ _ _ _ _ _ _ _ _
    iintro _ _ _ _ _
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons d Ds ih =>
    intro Js M hnd hN hF hJ hJd hM hMd
    obtain ⟨j, hrj, hjJ, hsl⟩ := hJ d List.mem_cons_self
    obtain ⟨jd, hrjd, hjdJ, hemp⟩ := hJd d List.mem_cons_self
    have hnd' := (List.nodup_cons.1 hnd)
    have hNd := hN d List.mem_cons_self
    have hN' : ∀ d' ∈ Ds, ∃ n, d' = memberDataDir n := fun d' h => hN d' (List.mem_cons_of_mem _ h)
    have hF' : ∀ d' ∈ Ds, Fs.DirFits (srvWalDirOf d') := fun d' h => hF d' (List.mem_cons_of_mem _ h)
    -- the area's and the data directory's inodes differ
    have hjd : jd ≠ j := by
      rintro rfl
      exact walAreaOf_ne hNd hNd (root_ino_inj hR hrj hrjd)
    have hjd' : jd ∈ Js.erase j := (List.mem_erase_of_ne hjd).2 hjdJ
    -- the others' inodes are neither
    have hother : ∀ d' ∈ Ds, ∀ j', ((walAreaOf d', j') ∈ R ∨ (d', j') ∈ R) → j' ≠ j ∧ j' ≠ jd := by
      intro d' hd' j' hr'
      have hNd' := hN' d' hd'
      have hne : d ≠ d' := fun h => hnd'.1 (h ▸ hd')
      refine ⟨?_, ?_⟩ <;> rintro rfl
      · rcases hr' with hr' | hr'
        · exact hne (walAreaOf_inj hNd hNd' (root_ino_inj hR hrj hr'))
        · exact walAreaOf_ne hNd hNd' (root_ino_inj hR hrj hr')
      · rcases hr' with hr' | hr'
        · exact walAreaOf_ne hNd' hNd (root_ino_inj hR hr' hrjd)
        · exact hne (root_ino_inj hR hrjd hr')
    have hJ' : ∀ d' ∈ Ds, ∃ j', (walAreaOf d', j') ∈ R ∧ j' ∈ (Js.erase j).erase jd ∧
        ∀ b, WalFs.AreaSlot b → V.now.entry j' b = none := by
      intro d' hd'
      obtain ⟨j', hrj', hj'J, hsl'⟩ := hJ d' (List.mem_cons_of_mem _ hd')
      obtain ⟨h1, h2⟩ := hother d' hd' j' (.inl hrj')
      exact ⟨j', hrj', (List.mem_erase_of_ne h2).2 ((List.mem_erase_of_ne h1).2 hj'J), hsl'⟩
    have hJd' : ∀ d' ∈ Ds, ∃ j', (d', j') ∈ R ∧ j' ∈ (Js.erase j).erase jd ∧
        ∀ b, V.now.entry j' b = none := by
      intro d' hd'
      obtain ⟨j', hrj', hj'J, he'⟩ := hJd d' (List.mem_cons_of_mem _ hd')
      obtain ⟨h1, h2⟩ := hother d' hd' j' (.inr hrj')
      exact ⟨j', hrj', (List.mem_erase_of_ne h2).2 ((List.mem_erase_of_ne h1).2 hj'J), he'⟩
    have hdw : walAreaOf d ≠ d := walAreaOf_ne hNd hNd
    have hM' : ∀ d' ∈ Ds, GMap.delete d (GMap.delete (walAreaOf d) M) !! walAreaOf d' = some () := by
      intro d' hd'
      have hNd' := hN' d' hd'
      have hne1 : walAreaOf d ≠ walAreaOf d' := by
        intro h
        exact hnd'.1 ((walAreaOf_inj hNd hNd' h) ▸ hd')
      have hne2 : d ≠ walAreaOf d' := fun h => walAreaOf_ne hNd' hNd h.symm
      rw [GMap.lookup_delete_ne _ hne2, GMap.lookup_delete_ne _ hne1]
      exact hM d' (List.mem_cons_of_mem _ hd')
    have hMd' : ∀ d' ∈ Ds, GMap.delete d (GMap.delete (walAreaOf d) M) !! d' = some () := by
      intro d' hd'
      have hNd' := hN' d' hd'
      have hne1 : walAreaOf d ≠ d' := walAreaOf_ne hNd hNd'
      have hne2 : d ≠ d' := fun h => hnd'.1 (h ▸ hd')
      rw [GMap.lookup_delete_ne _ hne2, GMap.lookup_delete_ne _ hne1]
      exact hMd d' (List.mem_cons_of_mem _ hd')
    iintro #Hos #Hsh #Hab Hall Hperms
    imod WalFs.walBoot0 hPre walCodec walCodec_ok walSrvMr hG.goose_localGS R j (walAreaOf d) V hV hR
      hrj Js hjJ hsl hrb walSrvMr_encState_lt ⊤ CoPset.subseteq_top $$ Hos Hsh Hab Hall
      with ⟨%W, #Hok, Hres, Hu, -, #Hp, Hown, -, Hrest⟩
    imod Fs.osPathS_root (L := hG.goose_localGS) R (walAreaOf d) j (DFrac.own 1) hrj
      CoPset.subseteq_top $$ Hsh with Hsp
    icases (BigSepM.bigSepM_delete (M := GMap GoString)
      (Φ := fun (r' : GoString) (_u : Unit) => Fs.osCallPerm (L := hG.goose_localGS) r' 1)
      (hM d List.mem_cons_self)).1 $$ Hperms with ⟨Hpd, Hperms⟩
    -- (2026-11-19) the data directory: its spine, its root's call permission and its whole claim
    imod Fs.osPathS_root (L := hG.goose_localGS) R d jd (DFrac.own 1) hrjd
      CoPset.subseteq_top $$ Hsh with Hspd
    icases (BigSepM.bigSepM_delete (M := GMap GoString)
      (Φ := fun (r' : GoString) (_u : Unit) => Fs.osCallPerm (L := hG.goose_localGS) r' 1)
      (show GMap.delete (walAreaOf d) M !! d = some () by
        rw [GMap.lookup_delete_ne _ hdw]; exact hMd d List.mem_cons_self)).1 $$ Hperms
      with ⟨Hpdd, Hperms⟩
    ihave Hrest := (BigSepL.bigSepL_perm (Φ := fun j => Fs.osNames (L := hG.goose_localGS) j (.except [])
      (DFrac.own 1) (Fs.namesOf V j (.except []))) (List.perm_cons_erase hjd')).1 $$ Hrest
    icases Hrest with ⟨Hjd, Hrest⟩
    imod ih ((Js.erase j).erase jd) (GMap.delete d (GMap.delete (walAreaOf d) M)) hnd'.2 hN' hF' hJ' hJd'
      hM' hMd' $$ Hos Hsh Hab Hrest Hperms with Hrest
    ihave #Hdd := walDirDurable_boot0 (W := W) (walAreaOf d) $$ Hp
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hrest
    unfold memberAreasFresh
    isplitl [Hres Hu Hsp Hpd Hown]
    · unfold walAreaFresh
      iexists etcdWalArea W hsat hsatL R j (walAreaOf d) (srvWalDirOf d) (hF d List.mem_cons_self)
      isplitr
      · ipureintro
        exact ⟨rfl, srvWalDirOf_inArea d, cleanAbsPath_of_rootForm ((hR.2.2 _ hrj).1), trivial⟩
      dsimp only [etcdWalArea]
      rw [Fs.callKey_eq hR hrj (.inl rfl)]
      iframe Hok Hdd Hsp Hres Hpd Hu
      unfold WalFs.walAbsent WalFs.walDirIs
      iexists ∅
      iframe Hown
      ipureintro
      show walOptLe none ((∅ : GMap GoString WalDur) !! srvWalDirOf d)
      rw [GMap.lookup_empty]; trivial
    · unfold dataAreaFresh
      iexists inferInstance, inferInstance, inferInstance, R, jd, Fs.namesOf V jd (.except [])
      isplitr
      · ipureintro
        exact ⟨cleanAbsPath_of_rootForm ((hR.2.2 _ hrjd).1), memberDataDir_length_lt hNd
            (hF d List.mem_cons_self), fun b => by rw [namesOf_except_cur]; exact hemp b⟩
      rw [Fs.callKey_eq hR hrjd (.inl rfl)]
      iframe Hos Hsh Hab Hspd Hpdd Hjd

/-- **The members' WAL areas, before the program's first step** (see the file header): over the file
extension's initial state `st` (`FsInit`, no I/O error assumed: `hsat`) with the members' areas as
`etcdWalAreasInit` says, the WP of a non-value `e` from the file extension's start resources (the
invariant of the mapped cells and the tree's shared view, `osShared`) follows from its WP given each data
directory's `walAreaFresh` and (2026-11-19) `dataAreaFresh`. -/
theorem wp_walAreas [go.BasicIntoValInj] (hPre : AbsDiskGpreS GF)
    (hsat : Fs.FsStepSat (Fs.NoIoErr allIo)) (hsatL : Fs.FsStepSat (Fs.NoMapLockErr allIo))
    (st : Fs.OsState) (hfs : Fs.FsInit st)
    (Ds : List GoString) (hDs : Ds.Nodup) (hW : etcdWalAreasInit st Ds)
    (hF : ∀ d ∈ Ds, Fs.DirFits (srvWalDirOf d))
    (hrb : ReceiptBoundLe GF (2 ^ 62))
    (e : Expr) (he : toVal e = none) (Φ : val → IProp GF) :
    ⊢ Fs.osInv (L := hG.goose_localGS) -∗
      Fs.osShared (L := hG.goose_localGS) st.fs.roots (st.fs.treeDur, []) -∗
      (([∗list] d ∈ Ds, memberAreasFresh (GF := GF) d) -∗
        WP e @ Stuckness.NotStuck; ⊤ {{ Φ }}) -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  have hR : Fs.RootsOk st.fs.roots := hfs.2.2.2.1
  have htw : Fs.TreeWf st.fs.roots st.fs.treeDur := hfs.2.2.2.2.1
  iintro #Hinv Ht Hk
  unfold Fs.osShared
  icases Ht with ⟨#Hsh, #Hab, Hperms, #-, Hall⟩
  unfold Fs.osCallPerms
  have hmemJ : ∀ j : Fs.Ino, (∃ r, (r, j) ∈ st.fs.roots) →
      j ∈ (GMap.toList (Fs.Hist.now (st.fs.treeDur, []))).map (·.1) := by
    rintro j ⟨r, hrj⟩
    have hj : j ∈ st.fs.treeDur := htw.1 j (Fs.Reach.root _ _ hrj)
    cases hl : st.fs.treeDur !! j with
    | none => have := (GMap.mem_iff _ _).1 hj; rw [hl] at this; cases this
    | some x => exact List.mem_map.2 ⟨(j, x), (GMap.mem_toList _ _ _).2 hl, rfl⟩
  have hmemM : ∀ r j, (r, j) ∈ st.fs.roots → GMap.delete [] (Fs.permMap st.fs.roots) !! r = some () := by
    intro r j hrj
    have hne : ([] : GoString) ≠ r := by
      obtain ⟨cs, hcs, -, hrc⟩ := (hR.2.2 _ hrj).1
      intro h0
      rw [← h0] at hrc
      cases cs with
      | nil => exact hcs rfl
      | cons c cs => simp [joinPath] at hrc
    rw [GMap.lookup_delete_ne _ hne]
    exact Fs.permMap_lookup st.fs.roots _ (.inr ⟨j, hrj⟩)
  imod walAreasFresh_boot hPre hsat hsatL st.fs.roots (st.fs.treeDur, []) rfl hR hrb Ds
    ((GMap.toList (Fs.Hist.now (st.fs.treeDur, []))).map (·.1)) (GMap.delete [] (Fs.permMap st.fs.roots))
    hDs (fun d hd => (hW d hd).1) hF
    (fun d hd => by
      obtain ⟨j, hrj, hsl⟩ := (hW d hd).2.1
      exact ⟨j, hrj, hmemJ j ⟨_, hrj⟩, hsl⟩)
    (fun d hd => by
      obtain ⟨j, hrj, he⟩ := (hW d hd).2.2
      exact ⟨j, hrj, hmemJ j ⟨_, hrj⟩, he⟩)
    (fun d hd => by
      obtain ⟨j, hrj, -⟩ := (hW d hd).2.1
      exact hmemM _ j hrj)
    (fun d hd => by
      obtain ⟨j, hrj, -⟩ := (hW d hd).2.2
      exact hmemM _ j hrj)
    $$ Hinv Hsh Hab Hall Hperms with Hw
  iapply Hk $$ Hw

end boot

end EtcdGrove
end Perennial
