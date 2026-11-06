/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchableStore.Write.wp_proof (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.Write.spec (GF := GF) (hG := hG) := by
  have hWrite := mvcc.store.Write.spec_R hWrite
  intro s st γ trace P Pre Q f te
  wp_start as ⟨#Hws, Hrd, Hwt, %Htrnn, Hhook, Hpre, #Htr, Htrc⟩
  ihave #Hws0 : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  (try wp_auto)
  wp_apply (hWrite st γ.st trace P Pre Q f te) $$ [$Hs $Hrd $Hwt $Hhook $Hpre $Htr $Htrc]
    as %mw ⟨⟨%ilog, %crev, Htx, -⟩, HQ, Hhook⟩
  · ipureintro; exact Htrnn
  icases mvcc.isTxnWrite_cert _ _ _ _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, #Hcert⟩
  (try wp_auto)
  wp_alloc wtw as Hwtw
  ipersist Hwtw
  (try wp_auto)
  iapply HΦ
  iframe HQ Hhook
  iunfold mvcc.isWatchTxnWrite
  iexists mw
  simp only [named]
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
