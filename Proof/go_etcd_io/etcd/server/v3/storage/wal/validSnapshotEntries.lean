/-
The proofs of `Spec/go_etcd_io/etcd/server/v3/storage/wal/validSnapshotEntries.lean` (W8 of
`notes/wal-fsext-plan.md`): `specAbsent` (`readWALNames.specAbsent` of the missing directory, its error's
`errIsTerm` giving the retry test, `wal.vseErrIs_of_term`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNamesAbsent
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the spec file's header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.wp_proofAbsent
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (wp_namesAbs : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.specAbsent (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.specAbsent (GF := GF) (hG := hG) := by
  intro lg R r nm j qp N h hnm hN hcur
  wp_start as ⟨#Hzap, #Hinv, #Hsi, Hp, Hperm, Hn⟩
  ihave #Hos : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_namesAbs lg r nm R j (DFrac.own qp) 1 N (DFrac.own (1 : Qp).half) h hnm hN hcur
    $$ [Hp Hperm Hn] as %rr %err ⟨Hp, Hperm, Hn, %e, %herr, #He, #Ht⟩
  · iframe; iframe #
  subst herr
  try wp_auto
  iapply HΦ
  iframe Hp Hperm Hn
  isplitr
  · ipureintro; nofun
  iapply wal.vseErrIs_of_term
  iframe Hos Ht

end proof

end EtcdGrove
end Perennial

end
