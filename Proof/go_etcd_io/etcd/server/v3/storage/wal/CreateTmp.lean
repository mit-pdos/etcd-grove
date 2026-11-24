/- Lean-first (no Rocq counterpart).

# `Create`'s temporary directory (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", eleventh
session; over any leftover since 2026-11-22, ledger 2026-11-22)

`tmpAny j b h` (`CreateCallees.lean`): the whole claim on `b`, holding anything, and the whole claims of
the directories under it. What `Create` does to `nm.tmp` before it publishes it, over it:
* `wp_existTmpNE`: `fileutil.Exist(d/b)` (over `os.Stat`'s shared-mode triples: `wp_absentS`,
  `wp_fileAnySW`, or `wp_dirSW` through the spine extended by the claim), nothing changed; `false` only
  with `b` absent, when the file system does not fail on `d/b` (`FsNoErrAt`);
* `wp_removeAllTmp`: `os.RemoveAll(d/b)` (`specSubS`), leaving a `tmpAny`; `nil` only with `b` gone,
  when the file system does not fail on `d/b` and `d`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import Proof.os.StatS
public import Proof.os.StatNE
public import Proof.os.RemoveAllCover
public import Proof.os.MkdirAllParts

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
variable [os_sem : os.Assumptions]

/-- `os.Stat` of a directory, its result's `FileInfo` dropped (the form `fileutil.Exist.spec` takes):
an error only when the file system can fail on the path. -/
theorem wp_statDirW_err (p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm (callKey R p) qc }}
      (App (Val (@! os.Stat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm (callKey R p) qc ∗ ⌜err = interface.nil ∨ ¬ FsNoErrAt p⌝ }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.Stat.wp_dirSW p R J dq qc $$ Hpre as %fi %err ⟨Hp, Hperm, Hor⟩
  iapply HΦ
  iframe
  icases Hor with (⟨%fs, %sz, %he, -⟩ | %he)
  · ipureintro; exact .inl he.1
  · ipureintro; exact .inr he.2

/-- `os.Stat` of a file, its result's `FileInfo` dropped: an error only when the file system can fail
on the path. -/
theorem wp_statFileW_err (d b : GoString) (R : Roots) (j i : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (Val (@! os.Stat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d dq j ∗
        osNames j N dqn h ∗ osCallPerm (callKey R d) qc ∗ ⌜err = interface.nil ∨ ¬ FsNoErrAt (child d b)⌝ }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.Stat.wp_fileAnySW d b R j i N dq dqn h qc hb hN hi $$ Hpre as %fi %err ⟨Hp, Hn, Hperm, Hor⟩
  iapply HΦ
  iframe
  icases Hor with (⟨%fs, %sz, %he, -⟩ | %he)
  · ipureintro; exact .inl he.1
  · ipureintro; exact .inr he.2

/-- **`fileutil.Exist(d/b)` of a `tmpAny`**: nothing changed; `false` only with `b` absent, when the
file system does not fail on `d/b`. -/
theorem wp_existTmpNE (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (d b : GoString) (R : Roots) (j : Ino) (qd : Qp) (h : NamesH) (qc : Qp) (hb : NameOk b) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ tmpAny j b h ∗
        osCallPerm (callKey R d) qc }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Exist)) (Val #(child d b)))
    {{ (x : Bool), RET #x; osPathS R d (DFrac.own qd) j ∗ tmpAny j b h ∗ osCallPerm (callKey R d) qc ∗
        ⌜x = false → FsNoErrAt (child d b) → h.cur !! b = none⌝ }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hp, Ht, Hperm⟩ HΦ
  iunfold tmpAny at Ht
  icases Ht with ⟨Hn, Hs⟩
  rcases hcur : h.cur !! b with _ | ⟨i | J⟩
  · have hnone := hcur
    wp_apply wp_Exist (child d b) _ _
      (os.Stat.wp_absentS d b R j (.only [b]) (DFrac.own qd) (DFrac.own 1) h qc hb
        (by simp [NameSet.Mem]) hnone) $$ [Hp Hn Hperm] as %x ⟨%err, %-, Hp, Hn, Hperm, %-⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    unfold tmpAny
    rw [hcur]
    iframe
    ipureintro; intro _ _; rfl
  · have hi : h.cur !! b = some (.file i) := hcur
    wp_apply wp_Exist (child d b) _ _
      (wp_statFileW_err d b R j i (.only [b]) (DFrac.own qd) (DFrac.own 1) h qc hb
        (by simp [NameSet.Mem]) hi) $$ [Hp Hn Hperm] as %x ⟨%err, %hx, Hp, Hn, Hperm, %hor⟩
    · iframe; isplitl [] <;> iassumption
    have hx' : x = false → FsNoErrAt (child d b) → False := by
      intro hf hne
      rcases hor with he | he
      · rw [hx, decide_eq_true he] at hf; cases hf
      · exact he hne
    iapply HΦ
    unfold tmpAny
    rw [hcur]
    iframe
    ipureintro; intro h1 h2; exact (hx' h1 h2).elim
  · have hd : h.cur !! b = some (.dir J) := hcur
    obtain ⟨e, a', b', hqd, hqq⟩ := os.qp_common qd 1
    subst hqd
    icases (osPathS_frac R d e a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
    icases (osNames_join j (.only [b]) e b' h hqq).2 $$ Hn with ⟨Hne, Hnb⟩
    ihave Hpc := osPathS_child R d b (DFrac.own e) j J h hb hd $$ Hpe Hne
    icases osCallPerm_child R d b _ j qc $$ Hpa Hperm with ⟨Hpa, Hperm⟩
    wp_apply wp_Exist (child d b) _ _
      (wp_statDirW_err (child d b) R J (DFrac.own e) qc) $$ [Hpc Hperm]
      as %x ⟨%err, %hx, Hpc, Hperm, %hor⟩
    · iframe; isplitl [] <;> iassumption
    have hx' : x = false → FsNoErrAt (child d b) → False := by
      intro hf hne
      rcases hor with he | he
      · rw [hx, decide_eq_true he] at hf; cases hf
      · exact he hne
    icases os.osPathS_unchild R d b j J e a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
    · iframe
    icases osCallPerm_unchild R d b _ j qc $$ Hp Hperm with ⟨Hp, Hperm⟩
    icases osNames_agree j (.only [b]) _ _ h'' h $$ Hne Hnb with %he
    subst he
    ihave Hn := (osNames_join j (.only [b]) e b' h'' hqq).1 $$ [Hne Hnb]
    · iframe
    iapply HΦ
    unfold tmpAny
    rw [hcur]
    iframe
    ipureintro; intro h1 h2; exact (hx' h1 h2).elim

end proof

section rm
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os_sem : os.Assumptions]

/-- **`os.RemoveAll(d/b)` of a `tmpAny`**: a `tmpAny` again; `nil` only with `b` gone, when the file
system does not fail on `d/b` and `d`. -/
theorem wp_removeAllTmp (wp_RmSub : os.RemoveAll.specSubS (GF := GF) (hG := hG))
    (d b : GoString) (R : Roots) (j : Ino) (qd : Qp) (h : NamesH) (hb : NameOk b) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ tmpAny j b h ∗
        osCallPerm (callKey R d) 1 }}
      (App (Val (@! os.RemoveAll)) (Val #(child d b)))
    {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) 1 ∗
        (∃ h', tmpAny j b h' ∗
          ⌜err = interface.nil → FsNoErrAt (child d b) → FsNoErrAt d → h'.cur !! b = none⌝) ∗
        fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hp, Ht, Hperm⟩ HΦ
  unfold tmpAny tmpCls
  icases Ht with ⟨Hn, %ct, Hct, %hct⟩
  wp_apply wp_RmSub d b j R qd h ct hb hct.1 hct.2 $$ [Hp Hn Hct Hperm]
    as %err ⟨Hp, Hperm, ⟨%h', %cl', Hn, Hcl, %hpost⟩, Hok⟩
  · iframe; isplitl [] <;> iassumption
  obtain ⟨hes, hcs, hnil⟩ := hpost
  iapply HΦ
  iframe Hp Hperm Hok
  iexists h'
  isplitl [Hn Hcl]
  · iframe Hn
    iexists cl'
    iframe Hcl
    ipureintro
    exact ⟨SubCover.of_sub hct.1 hcs (fun n hn => hes b n hn), ClRanked.of_sub hcs hct.2⟩
  · ipureintro; exact hnil

end rm

end EtcdGrove
end Perennial
