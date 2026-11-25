/- Lean-first (no Rocq counterpart).

`absent.spec` proved, by what `b` holds: nothing (`os.Lstat.wp_absentErrS`: a `*PathError` of an
errno, at which `errors.Is(err, os.ErrNotExist)` answers, `errors.IsPathErrnoNotExist.spec`), a file
(`wp_fileAnySW`) or a directory (`wp_childDirSW`), neither failing where the file system does not
(`FsNoErrAt`): `err == nil`, so `false` (`Proof/os/LstatAnyS.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.absent
public import Spec.errors.IsPathErrnoNotExist
public import Proof.os.LstatAnyS

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem absent.wp_proof
    (wp_IsNE : errors.IsPathErrnoNotExist.spec (GF := GF) (hG := hG)) :
    absent.spec (GF := GF) (hG := hG) := by
  intro _ _ _ d b R j qd h qc hb hne
  wp_start as ⟨#Hinv, #Hsi, Hp, Hn, Hperm⟩
  ihave #Hos : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
  · iPkgInit
  try wp_auto
  have hN : NameSet.Mem (.only [b]) b := by simp [NameSet.Mem]
  cases hc : h.cur !! b with
  | none =>
    wp_apply os.Lstat.wp_absentErrS d b R j (.only [b]) (DFrac.own qd) (DFrac.own 1) h qc hb hN hc
      $$ [Hp Hn Hperm] as %fi %err ⟨Hp, Hn, Hperm, %e, %he, #Herr⟩
    · iframe; iframe #
    ihave #HisNE := wp_IsNE err e he $$ Hos Herr
    ihave %hnil := os.errnoPathErr_ne err e $$ Herr
    ihave ⟨%ee, #Hee⟩ := os.errNotExist_of_pkgInit $$ Hos
    cases err with
    | nil => exact absurd rfl hnil
    | ok ie =>
    try wp_auto
    wp_bind (App (App _ (Val #(GoInterface.ok ie))) (Val #ee))
    iunfold errIsNotExist at HisNE
    iapply HisNE $$ Hee
    inext
    try wp_auto
    iapply HΦ
    iframe
    ipureintro; intro _; rfl
  | some nd =>
    cases nd with
    | file i =>
      wp_apply os.Lstat.wp_fileAnySW d b R j i (.only [b]) (DFrac.own qd) (DFrac.own 1) h qc hb hN hc
        $$ [Hp Hn Hperm] as %fi %err ⟨Hp, Hn, Hperm, Hres⟩
      · iframe; iframe #
      icases Hres with (⟨%fs, %sz, %herr, -⟩ | %herr)
      · obtain ⟨rfl, -⟩ := herr
        try wp_auto
        iapply HΦ
        iframe
        ipureintro; intro hf; cases hf
      · exact absurd hne herr.2
    | dir J =>
      wp_apply os.Lstat.wp_childDirSW d b R j J qd 1 h qc hb hc
        $$ [Hp Hn Hperm] as %fi %err ⟨Hp, Hn, Hperm, Hres⟩
      · iframe; iframe #
      icases Hres with (⟨%fs, %sz, %herr, -⟩ | %herr)
      · obtain ⟨rfl, -⟩ := herr
        try wp_auto
        iapply HΦ
        iframe
        ipureintro; intro hf; cases hf
      · exact absurd hne herr.2

end proof

end mvccrand
end EtcdGrove
end Perennial
