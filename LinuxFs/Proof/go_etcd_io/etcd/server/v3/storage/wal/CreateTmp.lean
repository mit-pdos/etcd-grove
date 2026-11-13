/- Lean-first (no Rocq counterpart).

# `Create`'s temporary directory (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", eleventh
session)

`tmpDirH j b h` (`CreateCallees.lean`): the whole claim on `b`, holding nothing or a directory of files
whose whole claim is held. What `Create` does to `nm.tmp` before it publishes it, over it:
* `wp_existTmp`: `fileutil.Exist(d/b)` (over `os.Stat`'s shared-mode triples: `wp_absentS`, or
  `wp_dirS` through the spine extended by the claim), nothing changed;
* `wp_removeAllTmp`: `os.RemoveAll(d/b)` (`specAbsentS` or `specDirS`), leaving a `tmpDirH` (the
  directory's files some of what they were, or it removed).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import LinuxFs.Proof.os.StatS
public import LinuxFs.Proof.os.MkdirAllParts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

/-- `os.Stat` of a directory, its result's `FileInfo` dropped (the form `fileutil.Exist.spec` takes). -/
theorem wp_statDir_err (p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm qc }}
      (App (Val (@! os.Stat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm qc }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.Stat.wp_dirS p R J dq qc $$ Hpre as %fi %err ⟨Hp, Hperm, -⟩
  iapply HΦ
  iframe

/-- **`fileutil.Exist(d/b)` of a `tmpDirH`**: some answer, nothing changed. -/
theorem wp_existTmp (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (d b : GoString) (R : Roots) (j : Ino) (qd : Qp) (h : NamesH) (qc : Qp) (hb : NameOk b) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ tmpDirH j b h ∗
        osCallPerm qc }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Exist)) (Val #(child d b)))
    {{ (x : Bool), RET #x; osPathS R d (DFrac.own qd) j ∗ tmpDirH j b h ∗ osCallPerm qc }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hp, Ht, Hperm⟩ HΦ
  unfold tmpDirH
  icases Ht with ⟨Hn, (%hnone | ⟨%J, %hJ, %hd, HJ⟩)⟩
  · wp_apply wp_Exist (child d b) _ _
      (os.Stat.wp_absentS d b R j (.only [b]) (DFrac.own qd) (DFrac.own 1) h qc hb
        (by simp [NameSet.Mem]) hnone) $$ [Hp Hn Hperm] as %x ⟨%err, %-, Hp, Hn, Hperm, %-⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
    ileft; ipureintro; exact hnone
  · obtain ⟨e, a', b', hqd, hqq⟩ := os.qp_common qd 1
    subst hqd
    icases (osPathS_frac R d e a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
    icases (osNames_join j (.only [b]) e b' h hqq).2 $$ Hn with ⟨Hne, Hnb⟩
    ihave Hpc := osPathS_child R d b (DFrac.own e) j J h hb hd.1 $$ Hpe Hne
    wp_apply wp_Exist (child d b) _ _
      (wp_statDir_err (child d b) R J (DFrac.own e) qc) $$ [Hpc Hperm]
      as %x ⟨%err, %-, Hpc, Hperm⟩
    · iframe; isplitl [] <;> iassumption
    icases os.osPathS_unchild R d b j J e a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
    · iframe
    icases osNames_agree j (.only [b]) _ _ h'' h $$ Hne Hnb with %he
    subst he
    ihave Hn := (osNames_join j (.only [b]) e b' h'' hqq).1 $$ [Hne Hnb]
    · iframe
    iapply HΦ
    iframe
    iright
    iexists J, hJ
    iframe
    ipureintro; exact hd

end proof

section rm
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os_sem : os.Assumptions]

/-- The removal's outcome on a directory of files is a `tmpDirH`. -/
theorem rmAllOut_tmpDirH (j : Ino) (b : GoString) (J : Ino) (h hJ : NamesH)
    (hd : h.cur !! b = some (.dir J)) (hf : FilesOnly hJ.cur) :
    rmAllOut (GF := GF) j b J h hJ ⊢ ∃ h', tmpDirH j b h' := by
  unfold rmAllOut tmpDirH
  iintro ⟨%h', %hJ', Hn, HJ, %hsub, Ho⟩
  have hf' : FilesOnly hJ'.cur := fun c n hc => hf c n (hsub c n hc)
  icases Ho with (%he | ⟨%x, %s, -, %he⟩)
  · subst he
    iexists h'
    iframe Hn
    iright
    iexists J, hJ'
    iframe
    ipureintro; exact ⟨hd, hf'⟩
  · iexists h'
    iframe Hn
    ileft
    ipureintro
    rw [he.1]
    simp [NamesH.log, restrictN_lookup _ _ _ (show (NameSet.only [b]).Mem b by simp [NameSet.Mem])]

/-- **`os.RemoveAll(d/b)` of a `tmpDirH`**: a `tmpDirH` again. -/
theorem wp_removeAllTmp (wp_RmAbs : os.RemoveAll.specAbsentS (GF := GF) (hG := hG))
    (wp_RmDir : os.RemoveAll.specDirS (GF := GF) (hG := hG))
    (d b : GoString) (R : Roots) (j : Ino) (qd : Qp) (h : NamesH) (hb : NameOk b) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ tmpDirH j b h ∗
        osCallPerm 1 }}
      (App (Val (@! os.RemoveAll)) (Val #(child d b)))
    {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm 1 ∗
        (∃ h', tmpDirH j b h') ∗ fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hp, Ht, Hperm⟩ HΦ
  iunfold tmpDirH at Ht
  icases Ht with ⟨Hn, (%hnone | ⟨%J, %hJ, %hd, HJ⟩)⟩
  · wp_apply wp_RmAbs d b j R qd (DFrac.own 1) h 1 hb hnone $$ [Hp Hn Hperm]
      as %err ⟨Hp, Hn, Hperm, Hok⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
    iexists h
    unfold tmpDirH
    iframe
    ileft; ipureintro; exact hnone
  · wp_apply wp_RmDir d b j J R qd h hJ hb hd.1 hd.2 $$ [Hp Hn HJ Hperm]
      as %err ⟨Hp, Hperm, Ho, Hok⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
    iapply rmAllOut_tmpDirH j b J h hJ hd.1 hd.2 $$ Ho

end rm

end EtcdGrove
end Perennial
