/-
The proofs of `examples/osfs/walfs`'s `dirswap.go` (one generation) over the shared view's claims:
the specs of `Create`, `checkDir` and `BootDir`.

The crash invariant (`dsInv`, `DSClaims.lean`) holds half of the claim on `wal` (and, once `wal` can
name a directory, of its `seg`); the program holds the other half (`dsHalf`), the whole claim on
`wal.tmp`, and what lies below `wal.tmp` (`tmpRes`). `Create` removes `wal.tmp/seg` and `wal.tmp`
(`wp_rmAny`, `wp_rmNoDir`), makes `wal.tmp` (`wp_mkAny`), creates its `seg` (`specCreateS`, a hypothesis, with the
trivial update), writes and syncs the data, deposits the file under the key (`ds_deposit`), merges
the claims on `wal` and `wal.tmp` (`ds_merge`) and renames `wal.tmp` onto `wal` (`wp_osRenameWal`).
The spine to `wal.tmp`'s directory is built from half the claim on `wal.tmp` (`osPathS_child`), and
`pathS_unchild` with `osNames_agree` gives that half back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSRename
public import Spec.os.OpenFileS
public import Proof.os.WriteFileLemmas
public import Proof.os.MkdirAllParts
public import Spec.os.File__Sync
public import Spec.os.File__WriteAt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DS

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

theorem except_inter_seg : (NameSet.except []).inter [segB] = sN := by
  simp [NameSet.inter, sN]

theorem except_seg_mem (b : GoString) :
    (NameSet.except []).Mem b ↔ sN.Mem b ∨ ((NameSet.except []).diff [segB]).Mem b := by
  simp only [NameSet.diff, NameSet.Mem, List.nil_append, List.mem_singleton, List.not_mem_nil, not_false_eq_true]
  exact iff_of_true trivial (Classical.em _)

theorem create_flag :
    OpenFlagsOk (W64 66 ||| W64 0x80000).toNat ∧ (W64 66 ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      (W64 66 ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC
  decide

theorem create_openFd (i : Ino) : openFd i (W64 66 ||| W64 0x80000) = ⟨i, true, true, none, none⟩ := rfl

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **What `Create` needs below `wal.tmp`** (`ht` the claim on `wal.tmp`): if `wal.tmp` is a
directory `T`, `T`'s whole claim and, if `T`'s `seg` is a directory, its whole claim (`subRes`). -/
def tmpRes (ht : NamesH) : IProp GF :=
  match ht.cur !! wtB with
  | some (.dir T) => iprop(∃ hT, osNames (L := L) T (.except []) (DFrac.own 1) hT ∗ subRes (L := L) segB hT)
  | _ => iprop(emp)

theorem tmpRes_dir {ht : NamesH} {T : Ino} (h : ht.cur !! wtB = some (.dir T)) :
    tmpRes (L := L) ht ⊣⊢
      ∃ hT, osNames (L := L) T (.except []) (DFrac.own 1) hT ∗ subRes (L := L) segB hT := by
  unfold tmpRes; rw [h]; exact .rfl

theorem subRes_dir {b : GoString} {h : NamesH} {T : Ino} (hd : h.cur !! b = some (.dir T)) :
    subRes (L := L) b h ⊣⊢ ∃ hT, osNames (L := L) T (.except []) (DFrac.own 1) hT := by
  unfold subRes; rw [hd]; exact .rfl

theorem subRes_noDir {b : GoString} {h : NamesH} (hd : ∀ T, h.cur !! b ≠ some (.dir T)) :
    ⊢ subRes (L := L) b h := by
  unfold subRes
  split
  · next T hT => exact absurd hT (hd T)
  · iempintro

theorem subRes_restrict (b : GoString) (h : NamesH) (j : Ino) (M : NameSet) (hb : M.Mem b) :
    subRes (L := L) b (h.restrict j M) ⊣⊢ subRes (L := L) b h := by
  unfold subRes; rw [restrict_cur _ _ _ _ hb]; exact .rfl

/-- `os.osSpine_unsnoc` (`Proof/os/MkdirAllParts.lean`), restated here without that section's
unused `os.fileStat.FieldAssumptions`. -/
theorem spine_unsnoc (cs : List GoString) (c : GoString) (j0 : Ino) (dq : DFrac) (J : Ino) :
    osSpine (L := L) j0 (cs ++ [c]) dq J ⊢ ∃ (j : Ino) (h : NamesH), osSpine (L := L) j0 cs dq j ∗
      osNames (L := L) j (.only [c]) dq h ∗ ⌜h.cur !! c = some (.dir J)⌝ := by
  induction cs generalizing j0 with
  | nil =>
    rw [List.nil_append, osSpine_cons]
    iintro ⟨%h, %J', Hn, %hJ, Hs⟩
    isimp only [osSpine_nil] at Hs
    icases Hs with %he
    subst he
    iexists j0, h
    rw [osSpine_nil]
    iframe
    isplitl [] <;> ipureintro
    · rfl
    · exact hJ
  | cons x cs ih =>
    rw [List.cons_append, osSpine_cons]
    iintro ⟨%h, %J', Hn, %hJ, Hs⟩
    icases ih J' $$ Hs with ⟨%j, %h', Hs, Hn', %hc⟩
    iexists j, h'
    rw [osSpine_cons]
    iframe
    isplitl [] <;> ipureintro
    · exact hJ
    · exact hc

/-- `pathS_unchild` (`Proof/os/MkdirAllParts.lean`), restated here without that section's
unused `os.fileStat.FieldAssumptions`: a spine to `d/b` and a spine to `d` give back a whole spine
to `d` and the claim on `b`. -/
theorem pathS_unchild (R : Roots) (d b : GoString) (j J : Ino) (e a : Qp) (hb : NameOk b) :
    osPathS (L := L) R (child d b) (DFrac.own e) J ∗ osPathS (L := L) R d (DFrac.own a) j ⊢
      ∃ h, osPathS (L := L) R d (DFrac.own (e + a)) j ∗ osNames (L := L) j (.only [b]) (DFrac.own e) h ∗
        ⌜h.cur !! b = some (.dir J)⌝ := by
  unfold osPathS
  iintro ⟨⟨%r, %j0, %cs, %hp, Hs⟩, ⟨%r', %j0', %cs', %hp', Hs'⟩⟩
  obtain ⟨hR, hm, hcs, he⟩ := hp
  obtain ⟨-, hm', hcs', rfl⟩ := hp'
  rw [← joinPath_snoc] at he
  have hcsb : ∀ x ∈ cs' ++ [b], NameOk x := by
    intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hcs' x hx
    · exact hb
  obtain ⟨hrj, rfl⟩ := root_split_unique hR hm' hm hcsb hcs he
  simp only [Prod.mk.injEq] at hrj
  obtain ⟨rfl, rfl⟩ := hrj
  icases spine_unsnoc cs' b j0' (DFrac.own e) J $$ Hs with ⟨%j'', %h, Hs, Hn, %hJ⟩
  icases osSpine_join cs' j0' e a j'' j $$ [Hs Hs'] with ⟨%hj, Hs⟩
  · isplitl [Hs]; iexact Hs; iexact Hs'
  subst hj
  iexists h
  isplitl [Hs]
  · iexists _, _, cs'
    iframe
    ipureintro; exact ⟨hR, hm', hcs', rfl⟩
  iframe
  ipureintro; exact hJ

theorem init_cur (m : Tree) (j : Ino) (N : NameSet) (b : GoString) (hb : N.Mem b) :
    (NamesH.init m j N).cur !! b = m.entry j b := by
  show restrictN N (entsOf m j) !! b = _
  rw [restrictN_lookup _ _ _ hb, entsOf_lookup]

theorem tmpRes_none {ht : NamesH} (hd : ∀ T, ht.cur !! wtB ≠ some (.dir T)) :
    ⊢ tmpRes (L := L) ht := by
  unfold tmpRes
  split
  · next T hT => exact absurd hT (hd T)
  · iempintro

/-- A fresh generation's claims below `wal.tmp` (`ds_start`) are what `Create` needs there. -/
theorem tmpRes_init (m : Tree) (j : Ino) :
    optClaim (L := L) (m, []) (dirOf m j wtB) ∗ optClaim (L := L) (m, []) (segDir m j) ⊢
      tmpRes (L := L) (NamesH.init m j (.only [wtB])) := by
  have hc : (NamesH.init m j (.only [wtB])).cur !! wtB = m.entry j wtB :=
    init_cur _ _ _ _ (by simp [NameSet.Mem])
  unfold segDir
  cases hT : dirOf m j wtB with
  | none =>
    iintro -
    iapply tmpRes_none
    intro T h
    rw [hc] at h
    unfold dirOf at hT; rw [h] at hT; cases hT
  | some T =>
    have he := dirOf_some hT
    refine Entails.trans ?_ (tmpRes_dir (L := L) (hc.trans he)).2
    have hs : (NamesH.init m T (.except [])).cur !! segB = m.entry T segB :=
      init_cur _ _ _ _ (by simp [NameSet.Mem])
    simp only [Option.bind]
    cases hK : dirOf m T segB with
    | none =>
      unfold optClaim
      dsimp only
      rw [namesOf_nil]
      iintro ⟨HT, -⟩
      iexists _
      iframe HT
      iapply subRes_noDir
      intro K h; rw [hs] at h; unfold dirOf at hK; rw [h] at hK; cases hK
    | some K =>
      unfold optClaim
      dsimp only
      rw [namesOf_nil, namesOf_nil]
      iintro ⟨HT, HK⟩
      iexists _
      iframe HT
      iapply (subRes_dir (L := L) (hs.trans (dirOf_some hK))).2
      iexists _; iexact HK

end res

/-! ## `Create` -/

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- **`os.Remove(d/wal.tmp/seg)`**, `d` the directory `j`, with the whole claim on `wal.tmp` and
`tmpRes`: what the next `os.Remove(d/wal.tmp)` needs (`subRes`). -/
theorem wp_rmTmpSeg (R : Roots) (d : GoString) (j : Ino) (ht : NamesH) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own 1) j ∗ osCallPerm (callKey R d) 1 ∗
        osNames j (.only [wtB]) (DFrac.own 1) ht ∗ tmpRes (GF := GF) ht }}
      (App (Val (@! os.Remove)) (Val #(child (child d wtB) segB)))
    {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own 1) j ∗ osCallPerm (callKey R d) 1 ∗
        osNames j (.only [wtB]) (DFrac.own 1) ht ∗ subRes (GF := GF) wtB ht }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hperm, Ht, Htmp⟩ HΦ
  by_cases hd : ∃ T, ht.cur !! wtB = some (.dir T)
  · obtain ⟨T, hT⟩ := hd
    icases (tmpRes_dir hT).1 $$ Htmp with ⟨%hT0, HT, Hsub⟩
    imod osNames_split R T (.except []) [segB] hT0 CoPset.subseteq_top $$ Hsi HT with ⟨Hs, Hr⟩
    rw [except_inter_seg]
    ihave Hsub := (subRes_restrict (GF := GF) segB hT0 T sN sN_seg).2 $$ Hsub
    -- the spine to `wal.tmp`, from half the claim on it
    rw [← Qp.half_add_half 1]
    icases (osPathS_frac R d (1 : Qp).half (1 : Qp).half j).1 $$ Hp with ⟨Hp1, Hp2⟩
    icases (osNames_frac j (.only [wtB]) (1 : Qp).half (1 : Qp).half ht).1 $$ Ht with ⟨Ht1, Ht2⟩
    ihave Hpc := osPathS_child R d wtB _ j T ht wtB_ok hT $$ Hp1 Ht1
    icases osCallPerm_child R d wtB _ _ _ $$ Hp2 Hperm with ⟨Hp2, Hperm⟩
    rw [Qp.half_add_half]
    iapply wp_fupd
    wp_apply wp_rmAny R (child d wtB) segB T _ (hT0.restrict T sN) segB_ok
      $$ [Hpc Hperm Hs Hsub] as %err Hr'
    · iframe; iframe #
    icases Hr' with ⟨Hpc, Hperm, %hs', Hs, -, -⟩
    imod osNames_merge R T sN ((NameSet.except []).diff [segB]) (.except []) hs' _ except_seg_mem
      CoPset.subseteq_top $$ Hsi Hs Hr with ⟨%hT1, HT, -⟩
    icases pathS_unchild R d wtB j T (1 : Qp).half (1 : Qp).half wtB_ok $$ [Hpc Hp2]
      with ⟨%h1, Hp, Ht1, %-⟩
    · iframe
    icases osNames_agree j (.only [wtB]) _ _ h1 ht $$ Ht1 Ht2 with %he
    subst he
    icases osCallPerm_unchild R d wtB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    imodintro
    iapply HΦ
    rw [Qp.half_add_half]
    iframe Hp Hperm
    isplitl [Ht1 Ht2]
    · iapply (osNames_join j _ _ _ h1 (Qp.half_add_half 1)).1; iframe
    iapply (subRes_dir hT).2
    iexists hT1; iexact HT
  · have hnd : ∀ T, ht.cur !! wtB ≠ some (.dir T) := fun T h => hd ⟨T, h⟩
    wp_apply wp_rmNoDir R d wtB segB j (DFrac.own 1) (DFrac.own 1) ht 1 wtB_ok segB_ok hnd
      $$ [Hp Hperm Ht] as %err ⟨Hp, Hperm, Ht⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    iapply subRes_noDir hnd

/-- `Create(dir)`, `dir` the root of `j`, `wal` absent, with the program's half of the invariant's
claims, the whole claim on `wal.tmp` and what lies below it: it does not panic. -/
theorem wp_Create (wp_CreateS : os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (wp_SyncDirS : os.File.Sync.specDirS (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (γ : GName)
    (ko : Option Ino) (hw ht : NamesH) (hA : hw.cur !! walB = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ dsInv (GF := GF) j γ ∗ osCallPerm (callKey R dir) 1 ∗
        dsHalf (GF := GF) j γ ko false hw none ∗ osNames j (.only [wtB]) (DFrac.own 1) ht ∗
        tmpRes (GF := GF) ht }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Create)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh, Ht, Htmp⟩
  imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  (try wp_auto)
  try rw [show dir ++ go!"/wal.tmp" = child dir wtB from rfl]
  try rw [show child dir wtB ++ go!"/seg" = child (child dir wtB) segB from rfl]
  -- `Remove(tmp/seg)`
  wp_apply wp_rmTmpSeg R dir j ht $$ [Hp Hperm Ht Htmp] as %err1 ⟨Hp, Hperm, Ht, Hsub⟩
  · iframe; iframe #
  (try wp_auto)
  -- `Remove(tmp)`
  wp_apply wp_rmAny R dir wtB j (DFrac.own 1) ht wtB_ok $$ [Hp Hperm Ht Hsub]
    as %err2 ⟨Hp, Hperm, %ht2, Ht, -, -⟩
  · iframe; iframe #
  (try wp_auto)
  -- `Mkdir(tmp)`
  wp_apply wp_mkAny R dir wtB j (DFrac.own 1) ht2 (W32 488) wtB_ok $$ [Hp Hperm Ht]
    as %err3 ⟨Hp, Hperm, %ht3, Ht, Hr⟩
  · iframe; iframe #
  cases err3 with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  icases Hr with (⟨%-, %hne⟩ | ⟨%T, %hT0, %hres, HT⟩)
  · exact absurd rfl hne
  obtain ⟨hT3, hT0e⟩ := hres
  (try wp_auto)
  -- `wal.tmp`'s `seg`'s claim, and the spine to `wal.tmp`
  imod osNames_split R T (.except []) [segB] hT0 CoPset.subseteq_top $$ Hsi HT with ⟨Hs, -⟩
  rw [except_inter_seg]
  have hs0n : (hT0.restrict T sN).cur !! segB = none := by
    rw [restrict_cur _ _ _ _ sN_seg, hT0e]; rfl
  rw [← Qp.half_add_half 1]
  icases (osPathS_frac R dir (1 : Qp).half (1 : Qp).half j).1 $$ Hp with ⟨Hp1, Hp2⟩
  icases (osNames_frac j (.only [wtB]) (1 : Qp).half (1 : Qp).half ht3).1 $$ Ht with ⟨Ht1, Ht2⟩
  ihave Hpc := osPathS_child R dir wtB _ j T ht3 wtB_ok hT3 $$ Hp1 Ht1
  icases osCallPerm_child R dir wtB _ _ _ $$ Hp2 Hperm with ⟨Hp2, Hperm⟩
  rw [Qp.half_add_half]
  -- `OpenFile(tmp/seg, O_RDWR|O_CREATE)`
  rw [show (W64 2 ||| W64 64) = W64 66 from by decide]
  try rw [show child dir wtB ++ go!"/seg" = child (child dir wtB) segB from rfl]
  obtain ⟨hfl, hcr, htr⟩ := create_flag
  generalize hs0e : hT0.restrict T sN = hs0 at hs0n ⊢
  icases (osNames_join T _ _ _ hs0 (Qp.half_add_half 1)).2 $$ Hs with ⟨Hs, Hsr⟩
  ihave Hau := os.osAU_triv (A := Option (Nat × Nat × Ino))
    (osNames (GF := GF) T (.only [segB]) (DFrac.own (1 : Qp).half) hs0)
    (crOut T segB hs0 (DFrac.own (1 : Qp).half)) $$ Hsr
  wp_apply wp_CreateS (child dir wtB) segB (W64 66) (W32 438) R T _ hs0
    (1 : Qp).half (1 : Qp).half 1 (crOut T segB hs0 (DFrac.own (1 : Qp).half)) hfl hcr htr segB_ok
    (fun J h => by rw [hs0n] at h; cases h) (Qp.half_add_half 1)
    $$ [$Hos $Hsi $Hpc $Hperm $Hs $Hau]
    as %f %err ⟨Hpc, Hperm, %oc, Ho1, Ho2, Hm, Hr⟩
  ihave Ho := os.crOut_join T segB hs0 oc $$ [$Ho1 $Ho2]
  rcases oc with _ | ⟨x, s0, i⟩
  · -- no effect: an error (the name was empty)
    icases Hr with (⟨%fd, %i, %hres, -, -, -⟩ | ⟨%herr, -⟩)
    · obtain ⟨-, -, hi⟩ := hres
      simp only [crIno] at hi
      rw [hs0n] at hi; cases hi
    cases err with
    | nil => exact absurd rfl herr.1
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  unfold crOut crMeta
  icases Ho with ⟨%hcr0, -, Hs⟩
  icases Hr with (⟨%fd, %i', %hres, Hf, -, Hfd⟩ | ⟨%herr, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr.1
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, hi⟩ := hres
  simp only [crIno] at hi
  subst hi
  rw [create_openFd]
  (try wp_auto)
  -- the data at 0
  wp_apply wp_newData as %sl Hsl
  (try wp_auto)
  ihave Hb0 : osBytes (GF := GF) i' (W64 0).toNat (DFrac.own 1) [] $$ []
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  ihave Hmc : mcellsAny (GF := GF) newMeta.maps (W64 0).toNat ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny; rw [show newMeta.maps = ∅ from rfl]
    iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply wp_WriteAt f fd (child (child dir wtB) segB) (DFrac.own 1) sl dataC (DFrac.own 1) (W64 0)
      (DFrac.own 1) ⟨i', true, true, none, none⟩ newMeta [] rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ [Hos Hf Hsl Hfd Hm Hb0 Hmc]
    as %n %err ⟨Hf, Hsl, Hfd, %j', %ys, %Hres, Hm, Hys, -⟩
  · iframe; iexact Hos
  obtain ⟨hj, hys, -, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne, -⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨i', true, true, none, none⟩ $$ [Hos Hf Hfd] as %e -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    itrivial
  have hys' : ys.map Prod.fst = dataC := pwOut_data hys
  have hysl : ys.length = (pwPost newMeta (W64 0).toNat dataC.length dataC.length).size := by
    rw [hys.1]; rfl
  (try wp_auto)
  -- `f.Sync()`
  wp_apply wp_Sync f fd (child (child dir wtB) segB) (DFrac.own 1) (DFrac.own 1) ⟨i', true, true, none, none⟩ _
      0 ys (OsMeta.covers_whole _ hysl) $$ [Hos Hf Hfd Hm Hys] as %err ⟨Hf, Hfd, Hr, -⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he, Hm, Hys⟩ | ⟨%he, -, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨i', true, true, none, none⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    itrivial
  subst he
  (try wp_auto)
  wp_apply wp_Close f fd (child (child dir wtB) segB) ⟨i', true, true, none, none⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
  (try wp_auto)
  -- the file, durable, goes into the invariant under the key `i'`
  icases (osMeta_halves i' _).1 $$ Hm with ⟨-, Hmi⟩
  icases (osBytes_halves i' 0 _).1 $$ Hys with ⟨-, Hysi⟩
  ihave Hk : keyRes (L := hG.goose_localGS) (some i') $$ [Hmi Hysi]
  · unfold keyRes
    iexists _, _
    iframe Hmi Hysi
    ipureintro; exact synced_good _ rfl ys hys'
  imod ds_deposit j γ ko false hw i' hA $$ Hinv Hh Hk with Hh
  -- the claim on `wal.tmp` back, merged with `wal`'s
  icases pathS_unchild R dir wtB j T (1 : Qp).half (1 : Qp).half wtB_ok $$ [Hpc Hp2]
    with ⟨%h1, Hp, Ht1, %-⟩
  · iframe
  icases osNames_agree j (.only [wtB]) _ _ h1 ht3 $$ Ht1 Ht2 with %he
  subst he
  icases osCallPerm_unchild R dir wtB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  ihave Ht := (osNames_frac j (.only [wtB]) (1 : Qp).half (1 : Qp).half h1).2 $$ [Ht1 Ht2]
  · iframe
  rw [Qp.half_add_half]
  imod ds_merge R j γ (some i') hw h1 $$ Hinv Hsi Hh Ht with ⟨%hw', Hh, %hm⟩
  obtain ⟨hmw, hmt, -⟩ := hm
  have hT' : hw'.cur !! wtB = some (.dir T) := by
    have := congrArg (fun h : NamesH => h.cur !! wtB) hmt
    rw [restrict_cur _ _ _ _ (by simp [NameSet.Mem]), restrict_cur _ _ _ _ (by simp [NameSet.Mem])]
      at this
    rw [this]; exact hT3
  have hA' : hw'.cur !! walB = none := by
    have := congrArg (fun h : NamesH => h.cur !! walB) hmw
    rw [restrict_cur _ _ _ _ wO_wal, restrict_cur _ _ _ _ wO_wal] at this
    rw [this]; exact hA
  have hseg : (hs0.log x (crEnt T segB i' s0) (<[segB := .file i']> hs0.cur)).cur !! segB =
      some (.file i') := GMap.lookup_insert _ _ _
  imod osNames_histCoh R T sN _ _ CoPset.subseteq_top $$ Hsi Hs with ⟨Hs, %hcoh⟩
  -- `Rename(tmp, dir/wal)`
  try rw [show dir ++ go!"/wal" = child dir walB from rfl]
  wp_apply wp_osRenameWal R dir j T i' hrj γ hw' _ hT' hA' hseg hcoh
    $$ [Hperm Hh Hs] as %err Hperm
  · iframe; iframe #
  cases err with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  (try wp_auto)
  -- the directory's sync
  wp_apply wp_syncDir wp_SyncDirS R dir _ j 1 $$ [Hp Hperm] as %ok -
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

/-- `checkDir(w)`, `w` the directory `J` (a spine to it), its `seg` the file `k` (a fraction of the
claim on `J`'s `seg`), with half of the file's `OsMeta` and of its data, `CheckOk`: it does not
panic. -/
theorem wp_checkDir (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (R : Roots) (w : GoString) (dq : DFrac) (J : Ino) (dqn : DFrac) (hs : NamesH) (qc : Qp) (k : Ino)
    (hk : hs.cur !! segB = some (.file k)) (m : OsMeta) (bs : List ByteG) (hok : CheckOk m bs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R w dq J ∗ osCallPerm (callKey R w) qc ∗
        osNames J sN dqn hs ∗
        osMeta (GF := GF) k (DFrac.own (1 : Qp).half) m ∗
        osBytes (GF := GF) k 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.checkDir)) (Val #w))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hm, Hb⟩
  (try wp_auto)
  wp_apply wp_readNamesS w R J dq qc sN dqn hs $$ [Hp Hperm Hn] as %sl %ok ⟨Hp, Hperm, Hn, Hr⟩
  · iframe; iframe #
  icases Hr with (%hok' | ⟨%names, %hn, Hsl⟩)
  · subst hok'
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, hmem, -⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (i : w64) (nv : GoString),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧ segB ∉ names.take (sint.nat i)⌝)
      $$ [i n]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_⟩ <;> rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hns⟩ := Hi
  wp_if_destruct
  · have Hlt : sint.nat i < names.length := by word
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    obtain ⟨b, hb⟩ : ∃ b, names[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z i) names (DFrac.own 1) b hi0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hb
    have htake : names.take (sint.nat (i + W64 1)) = names.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [List.take_add_one, hb]; rfl
    (try wp_auto)
    by_cases hbs : b = segB
    · subst hbs
      rw [decide_eq_true (show segB = go!"seg" from rfl)]
      (try wp_auto)
      wp_apply wp_check wp_ReadAt wp_Close R w dq J sN dqn hs qc k sN_seg hk m bs hok
        $$ [Hp Hn Hperm Hm Hb]
      · iframe; iframe #
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    rw [decide_eq_false (show ¬ b = go!"seg" from hbs)]
    (try wp_auto)
    wp_for_post
    iframe
    iexists i + W64 1, b
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [htake]; simp [hns, Ne.symm hbs]
  · -- the loop is done: `seg` was not among the names, which it is
    exfalso
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hns
    apply hns
    exact (hmem segB sN_seg).1 (by rw [hk]; rfl)

/-- `BootDir(dir)`, `dir` the root of `j`, in a fresh generation of the tree `m`, `SafeT` with the
invariant's key `ko`: with what `ds_start` hands out (the program's half of the invariant's claims,
the claim on `wal.tmp`, the claims of `wal.tmp`'s directory and of its `seg`'s) and the program's
half of the key's file (`segRes`), it does not panic. -/
theorem wp_BootDir (wp_CreateS : os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (wp_SyncDirS : os.File.Sync.specDirS (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (γ : GName)
    (m : Tree) (ko : Option Ino) (hs : SafeT j ko m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ dsInv (GF := GF) j γ ∗ osCallPerm (callKey R dir) 1 ∗
        dsHalf (GF := GF) j γ ko false (NamesH.init m j wO) (initSeg m j) ∗
        osNames j (.only [wtB]) (DFrac.own 1) (NamesH.init m j (.only [wtB])) ∗
        optClaim (GF := GF) (m, []) (dirOf m j wtB) ∗ optClaim (GF := GF) (m, []) (segDir m j) ∗
        segRes (GF := GF) ko }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.BootDir)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh, Ht, HT, HK, Hs⟩
  have hwc : (NamesH.init m j wO).cur !! walB = m.entry j walB := init_cur _ _ _ _ wO_wal
  imod osPathS_root R dir j (DFrac.own (1 : Qp).half) hrj CoPset.subseteq_top $$ Hsi with Hp
  unfold dsHalf
  icases Hh with ⟨Hv, Hw, Hcl⟩
  (try wp_auto)
  wp_apply wp_readNamesS dir R j _ 1 wO _ _ $$ [Hp Hperm Hw] as %sl %ok ⟨Hp, Hperm, Hw, Hr⟩
  · iframe; iframe #
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, hmem, -⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (i : w64) (nv : GoString),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧ walB ∉ names.take (sint.nat i)⌝)
      $$ [i n]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_⟩ <;> rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hns⟩ := Hi
  wp_if_destruct
  · have Hlt : sint.nat i < names.length := by word
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    obtain ⟨b, hb⟩ : ∃ b, names[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z i) names (DFrac.own 1) b hi0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hb
    have htake : names.take (sint.nat (i + W64 1)) = names.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [List.take_add_one, hb]; rfl
    (try wp_auto)
    by_cases hbs : b = walB
    · subst hbs
      rw [decide_eq_true (show walB = go!"wal" from rfl)]
      (try wp_auto)
      -- `wal` is there: a directory, its `seg` the file of the key
      have hW : (m.entry j walB).isSome := by
        rw [← hwc]; exact (hmem walB wO_wal).2 (List.mem_of_getElem? hb)
      obtain ⟨J, hWd⟩ : ∃ J, m.entry j walB = some (.dir J) := by
        cases h : m.entry j walB with
        | none => rw [h] at hW; cases hW
        | some x =>
          cases x with
          | dir J => exact ⟨J, rfl⟩
          | file k => exact absurd h (hs.1 k)
      obtain ⟨k, rfl, hk⟩ := hs.2 J hWd
      have hseg : initSeg m j = some (J, NamesH.init m J sN) := by unfold initSeg; rw [hWd]
      rw [hseg]
      unfold osClaims jcl
      icases BigSepL.bigSepL_singleton.1 $$ Hcl with Hcl
      unfold segRes
      icases Hs with ⟨%mt, %bs, Hm, Hb, %hok⟩
      -- the spine to `wal`
      icases osCallPerm_child R dir walB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
      ihave Hpc := osPathS_child R dir walB _ j J _ walB_ok (hwc.trans hWd) $$ Hp Hw
      try rw [show dir ++ go!"/wal" = child dir walB from rfl]
      wp_apply wp_checkDir wp_ReadAt wp_Close R (child dir walB) _ J _ _ 1 k
          (by rw [init_cur _ _ _ _ sN_seg]; exact hk) mt bs hok
        $$ [Hpc Hperm Hcl Hm Hb]
      · iframe; iframe #
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    rw [decide_eq_false (show ¬ b = go!"wal" from hbs)]
    (try wp_auto)
    wp_for_post
    iframe
    iexists i + W64 1, b
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [htake]; simp [hns, Ne.symm hbs]
  · -- the loop is done: no `wal`
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hns
    have hWn : m.entry j walB = none := by
      cases h : m.entry j walB with
      | none => rfl
      | some x => exact absurd ((hmem walB wO_wal).1 (by rw [hwc, h]; rfl)) hns
    have hseg : initSeg m j = none := by unfold initSeg; rw [hWn]
    rw [hseg]
    ihave Htmp := tmpRes_init (L := hG.goose_localGS) m j $$ [HT HK]
    · iframe
    (try wp_auto)
    wp_apply wp_Create wp_CreateS wp_SyncDirS wp_Close wp_WriteAt wp_Sync R dir j hrj γ ko (NamesH.init m j wO) _
        (hwc.trans hWn) $$ [Hperm Hv Hw Hcl Ht Htmp]
    · iframe; iframe #
      unfold dsHalf; iframe
    (try wp_auto)
    iapply HΦ
    itrivial

end prog

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
