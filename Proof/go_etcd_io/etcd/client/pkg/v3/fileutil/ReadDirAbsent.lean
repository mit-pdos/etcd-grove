/-
The proof of `Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDirAbsent.lean`, over
`os.Open.wp_absentS` (`Proof/os/NsAbsentS.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirAbsent
public import Spec.errors.IsPathErrnoTerm
public import Proof.os.NsChildS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.wp_proofAbsent
    (wp_Term : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.specAbsent (GF := GF) (hG := hG) := by
  intro d b R j dq qc N dqn h hb hN hi
  wp_start as ⟨#Hos, #Hsi, #Hpkg, Hp, Hperm, Hn⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_method_call
  wp_auto
  ihave IH : iprop("i" ∷ i_ptr ↦ W64 0) $$ [i]
  · simp only [named]; iframe
  wp_for IH
  wp_apply os.Open.wp_absentErrS d b R j N dq dqn h qc hb hN hi $$ [Hp Hn Hperm]
    as %f %err ⟨Hp, Hn, Hperm, %e, %he, #Herr⟩
  · iframe; (repeat' isplitl []) <;> (first | iassumption | iPkgInit)
  ihave %herr := os.errnoPathErr_ne err e $$ Herr
  ihave #Hosp : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
  · iPkgInit
  cases err with
  | nil => exact absurd rfl herr
  | ok ie =>
  wp_auto
  iapply HΦ
  iframe
  isplitr
  · ipureintro; exact herr
  isplitl []
  · iapply (os.errnoPathErr_fmtErrorOkOrNil _ e he.1) $$ Hsys Herr
  · iapply (wp_Term _ e he.1) $$ Hosp Herr

end proof

end EtcdGrove
end Perennial

end
