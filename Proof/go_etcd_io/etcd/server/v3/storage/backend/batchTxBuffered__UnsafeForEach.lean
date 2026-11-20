/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeForEach.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeForEach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.batchTxBuffered.UnsafeForEach.wp_proof
    (hFE : backend.batchTx.UnsafeForEach.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st c bk bi fn I E
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, HI, #Hvis⟩
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  wp_apply (hFE γ P W Pk b t st bk bi fn I E) $$ [Htxf Hpend Hwtx $HI] as %err ⟨Hw, Hr⟩
  · iframe #
    unfold btW
    iframe
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  iapply HΦ
  iframe Hr
  iexists t, db
  iframe
  iframe #
  ipureintro
  exact Hwf

end proof

end EtcdGrove
end Perennial
