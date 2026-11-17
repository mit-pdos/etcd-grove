/-
The proof of `Spec/go_etcd_io/bbolt/Open_shared.lean` (S3a): `Open`'s proof, generic in how the file is
opened (`Open.wp_proofG`, `Open.lean`), with the shared mode's open (`openFileDb_shared`):
`os.OpenFile.specCreateS` with the whole claim on the name, split in halves, the other half the
trivial update's (`os.osAU_triv`); the file the open left at the name holds `D` (`nameHolds_opened`:
the existing file's `fileHolds`, or the new file's `newMeta`, with `D = ∅`).
-/
module

public import Spec.go_etcd_io.bbolt.Open_shared
public import Proof.go_etcd_io.bbolt.Open
import all Proof.go_etcd_io.bbolt.Open
public import Proof.os.WriteFile
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]

/-- The name holds no directory. -/
private theorem nameHolds_notDir (h : NamesH) (b : GoString) (D : Data) :
    nameHolds (GF := GF) h b D ⊢ nameHolds h b D ∗ ⌜∀ J, h.cur !! b ≠ some (.dir J)⌝ := by
  unfold nameHolds
  iintro (⟨%i, %hi, H⟩ | %hn)
  · isplitl
    · ileft; iexists i; iframe H; ipureintro; exact hi
    · ipureintro; intro J hJ; rw [hi] at hJ; cases hJ
  · isplitl
    · iright; ipureintro; exact hn
    · ipureintro; intro J hJ; rw [hn.1] at hJ; cases hJ

/-- **The file the open left at the name, opened** (the existing file holding `D`, or the created
one, empty). -/
private theorem nameHolds_opened (j : Ino) (h : NamesH) (b : GoString) (D : Data)
    (o : Option (Nat × Nat × Ino)) (i : Ino) (hcr : crIno b h o i) :
    nameHolds (GF := GF) h b D ∗ crOut j b h (DFrac.own 1) o ∗ crMeta o ⊢
      crOut j b h (DFrac.own 1) o ∗ openedF i D := by
  unfold nameHolds
  cases o with
  | none =>
    dsimp only [crIno] at hcr
    dsimp only [crMeta]
    iintro ⟨(⟨%i0, %hi0, Hf⟩ | %hn), Ho, -⟩
    · rw [hcr] at hi0; cases hi0
      iframe Ho
      unfold fileHolds
      iapply fileHolds_opened $$ Hf
    · rw [hcr] at hn; exact absurd hn.1 (by simp)
  | some xsi =>
    obtain ⟨x, s, i1⟩ := xsi
    dsimp only [crIno] at hcr
    subst hcr
    dsimp only [crMeta, crOut]
    iintro ⟨(⟨%i0, %hi0, -⟩ | %hn), ⟨%hh, Hl, Hn⟩, Hm⟩
    · rw [hh.1] at hi0; cases hi0
    · obtain ⟨-, rfl⟩ := hn
      iframe Hl Hn
      isplitr
      · ipureintro; exact hh
      iapply new_opened $$ Hm

/-- `O_RDWR|O_CREATE` with `O_CLOEXEC` is a valid create, without `O_TRUNC`. -/
private theorem boltOpenFlag_create :
    OpenFlagsOk (W64 0x42 ||| W64 0x80000).toNat ∧ (W64 0x42 ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      (W64 0x42 ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC
  decide

/-- **The shared mode's open of the database file** (`os.OpenFile.specCreateS`) as
`openFileDb.spec`: the claim's halves, the trivial update, the outcome's claim back whole. -/
private theorem openFileDb_shared (hCS : os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH) (perm : w32)
    (D : Data) (hb : NameOk b) :
    openFileDb.spec (GF := GF) (hG := hG)
      iprop(osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
        osNames j (.only [b]) (DFrac.own 1) h ∗ nameHolds h b D)
      (fun oc : Option (Nat × Nat × Ino) =>
        iprop(osPathS (GF := GF) R d dq j ∗ osCallPerm qc ∗ crOut j b h (DFrac.own 1) oc))
      (fun oc i => crIno b h oc i) (child d b) perm D := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hnh⟩ HΦ
  obtain ⟨hfl, hcr, htr⟩ := boltOpenFlag_create
  icases nameHolds_notDir h b D $$ Hnh with ⟨Hnh, %hnd⟩
  icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hn, Hr⟩
  ihave Hau := os.osAU_triv (A := Option (Nat × Nat × Ino))
    (osNames (GF := GF) j (.only [b]) (DFrac.own (1 : Qp).half) h)
    (crOut j b h (DFrac.own (1 : Qp).half)) $$ Hr
  wp_apply hCS d b (W64 0x42) perm R j dq h (1 : Qp).half (1 : Qp).half qc
    (crOut j b h (DFrac.own (1 : Qp).half)) hfl hcr htr hb hnd (Qp.half_add_half 1)
    $$ [$Hos $Hsi $Hp $Hperm $Hn $Hau]
    as %f %err ⟨Hp, Hperm, %oc, Ho1, Ho2, Hm, Hr⟩
  ihave Ho := os.crOut_join j b h oc $$ [$Ho1 $Ho2]
  iapply HΦ
  iexists oc
  dsimp only
  icases Hr with (⟨%fd, %i, %hres, Hf, -, Hfd⟩ | ⟨%herr, #Hok⟩)
  · obtain ⟨rfl, hfd, hi⟩ := hres
    icases nameHolds_opened j h b D oc i hi $$ [$Hnh $Ho $Hm] with ⟨Ho, Hop⟩
    iframe Hp Hperm Ho
    isplitl [Hf Hfd Hop]
    · ileft
      iexists fd, i
      iframe Hf Hop
      isplitr
      · ipureintro; exact ⟨rfl, hfd, hi⟩
      have hofd : openFd i (W64 0x42 ||| W64 0x80000) = ⟨i, true, true, none, none⟩ := by
        have h1 : (W64 0x42 ||| W64 0x80000).toNat % 4 = 2 := by decide
        simp only [openFd, h1, O_WRONLY, O_RDONLY]; rfl
      rw [hofd] at *
      iexact Hfd
    · iapply fmtErrorOkOrNil_nil
  · iframe Hp Hperm Ho Hok
    iright; ipureintro; exact herr

set_option maxHeartbeats 4000000 in
theorem Open_shared.wp_proof [sync.Assumptions]
    (hCS : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (hName : os.File.Name.spec (GF := GF) (hG := hG))
    (hFlock : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], flock.spec (GF := GF) (hG := hG))
    (hStat : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hMZ : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.metasZero.spec_own (GF := GF) (hG := hG))
    (hInit : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.init.spec (GF := GF) (hG := hG))
    (hGPS : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.getPageSize.spec_own (GF := GF) (hG := hG))
    (hMmap : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.mmapUnlocked.spec_own (GF := GF) (hG := hG))
    (hLoad : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.loadFreelist.spec_open (GF := GF) (hG := hG))
    (hSync : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hFds : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], fdatasync.spec (GF := GF) (hG := hG))
    (hBegin : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.Begin_err.spec (GF := GF) (hG := hG))
    (hCommit : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Tx.Commit_err.spec (GF := GF) (hG := hG))
    (hClose : DB.Close.spec (GF := GF) (hG := hG))
    (hclose : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.close.spec_owned (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hOptStr : Options.String.spec (GF := GF) (hG := hG))
    (hModeStr : fs.FileMode.String.spec (GF := GF) (hG := hG)) :
    Open_shared.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ _ N R d b dq j qc h mode opts dqo o D hb
  iintro %Φ ⟨#Hpkg, #Hos, %HN, #Hsi, Hp, Hperm, Hn, Hnh, Hopts, %Hok, Hlgr⟩ HΦ
  iapply Open.wp_proofG hName hFlock hStat hSize hMZ hInit hGPS hMmap hLoad hSync hFds hBegin
    hCommit hClose hclose hLogger hOptStr hModeStr _ _ _ N (child d b) mode opts dqo o D
    (openFileDb_shared hCS R d b dq j qc h mode D hb) $$ [Hp Hperm Hn Hnh Hopts Hlgr]
  · iframe; iframe #
    ipureintro; exact ⟨HN, Hok⟩
  inext
  iintro %db %err ⟨Hopts, %oc, ⟨Hp, Hperm, Ho⟩, Hr⟩
  iapply HΦ
  iframe Hopts Hp Hperm
  iexists oc
  iframe Ho Hr

end proof

end bbolt
end EtcdGrove
end Perennial
