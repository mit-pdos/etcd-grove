/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/readWALNamesAbsent.lean`, over
`fileutil.ReadDir.specAbsent` and `fmt.ErrorfErrs.spec`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNamesAbsent
public import Spec.fmt.ErrorfErrsTerm
public import Proof.errors.ErrTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.readWALNames.wp_proofAbsent
    (HRead : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.specAbsent (GF := GF) (hG := hG))
    (HErrorf : fmt.ErrorfErrsTerm.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.readWALNames.specAbsent (GF := GF) (hG := hG) := by
  intro lg d b R j dq qc N dqn h hb hN hi
  wp_start as ⟨#Hlg, #Hos, #Hsi, Hp, Hperm, Hn⟩
  wp_auto
  wp_apply HRead d b R j dq qc N dqn h hb hN hi $$ [Hp Hperm Hn]
    as %r %err ⟨Hp, Hperm, Hn, %herr, #Herr, #Hterm⟩
  · isplitl []
    · iexact Hos
    isplitl []
    · iexact Hsi
    isplitl []
    · iPkgInit
    iframe
  cases err with
  | nil => exact absurd rfl herr
  | ok ie =>
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply HErrorf _ _ [GoInterface.ok ie] [ie] ?wf ?ww $$ [Hasl] as %err2 ⟨#Herr2, #Ht2⟩
  case wf => errargs_wf
  case ww => wraps_le1
  · iframe
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => iprop(errOk (GF := GF) e ∗
      errTreeTerm (GoInterface.ok e)))).2
    iframe Hterm
    iapply errOk_of_fmtErrorOkOrNil
    iexact Herr
  try wp_auto
  iapply HΦ
  iframe
  iexists err2
  isplitr
  · ipureintro; rfl
  isplitl []
  · iexact Herr2
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  iapply (errIsTerm_of_tree (GoInterface.ok err2)) $$ Herrs Ht2

end proof

end EtcdGrove
end Perennial

end
