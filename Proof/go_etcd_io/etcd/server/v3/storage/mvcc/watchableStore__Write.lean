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

/-- **The sole writer pins its write transaction**: with the certificate of `L` and every token
of `L`'s budget but the transaction's, the transaction's committed log is `L`. -/
theorem mvcc.watchWriter_pins (γ : mvcc.StoreNames) (L ilog : mvcc.Log) (pend : List mvcc.Change)
    (tw s : Loc) (crev : Int) :
    mvcc.idxCert (GF := GF) γ.idx L ∗ ownToks γ.revs (mvcc.wBudget L - 1) ∗
      mvcc.storeTxnWriteIs tw s γ trace ilog pend crev ⊢ ⌜ilog = L⌝ := by
  iintro ⟨#Hmycert, Hmine, H⟩
  unfold mvcc.storeTxnWriteIs
  icases H with ⟨%ti, %bt, %Locked, %chs, %ps, %ntok, %Pw, %fw, H⟩
  iNamed H
  unfold mvcc.revToken
  icombine Hmine Htok as Hall
  icombine Htoks Hall gives %hle
  ihave %hpre := mvcc.idxWriter_cert_prefix γ.idx ilog pend L $$ [$Hw $Hmycert]
  ipureintro
  have hl := hpre.length_le
  have heq : ilog.length = L.length := by unfold mvcc.wBudget at hle; omega
  exact (hpre.eq_of_length heq.symm).symm

theorem mvcc.watchableStore.Write.wp_proof (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.Write.spec (GF := GF) (hG := hG) := by
  have hWrite := mvcc.store.Write.spec_R hWrite
  intro s st γ trace L P Pre Q f te
  wp_start as ⟨#Hws, Hrd, Hwt, Hww, %Hlen, %Htrnn, Hhook, Hpre, #Htr, Htrc⟩
  ihave #Hws0 : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  iunfold mvcc.watchWriter at Hww
  icases Hww with ⟨#Hcert, Htoks, Hwlog⟩
  have hb : mvcc.wBudget L = (mvcc.wBudget L - 1) + 1 := by unfold mvcc.wBudget; omega
  rw [hb]
  icases (ownToks_add 1 (mvcc.wBudget L - 1) γ.st.revs).1 $$ Htoks with ⟨Htoks, H1⟩
  (try wp_auto)
  wp_apply (hWrite st γ.st trace P Pre Q f te) $$ [$Hs $Hrd H1 $Hwt $Hhook $Hpre $Htr $Htrc]
    as %mw ⟨⟨%ilog, %crev, Htx, -⟩, HQ, Hhook⟩
  · unfold mvcc.revToken; iframe H1; ipureintro; exact Htrnn
  iunfold mvcc.isTxnWrite at Htx
  iNamed Htx
  ihave %Heq := mvcc.watchWriter_pins γ.st L ilog [] tw st crev $$ [$Hcert $Htoks $Htw]
  subst Heq
  ihave Htx : mvcc.isTxnWrite mw st γ.st trace ilog [] (W64 0) (W64 0) (W64 0) crev $$ [Hmw Htw Htrc]
  · iunfold mvcc.isTxnWrite
    iexists tw, ranges
    iframe
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
