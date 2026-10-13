/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeRange.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTxBuffered.UnsafeRange.wp_proof
    (hBT : backend.batchTx.UnsafeRange.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t st bk bi key endKey kb eb dk de limit Hend
  wp_start as ⟨#Hb, #Ht, Hl, #Hbk, Hkey, HendKey⟩
  ihave #Hacc : (□ (∀ (s : GoSlice) (v : GoString) (st' : BSess), rdB st.tx s v -∗
      batchLocked γ P b st' -∗ ⌜st'.tx = st.tx⌝ -∗
      ∃ dq : DFrac, s ↦*{dq} v ∗ (s ↦*{dq} v -∗ batchLocked γ P b st')) : IProp GF) $$ []
  · iintro !> %s %v %st' Hr Hl %Htx
    iapply batchLocked_rdB γ P b st st' s v $$ [$Hr $Hl]
    ipureintro
    exact Htx
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb, %HP⟩
  · iframe #
  unfold batchLocked batchLockedAt batchPhys
  icases Hl with ⟨%t', %db, #Ht', Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb', Hwtx, #Htxdb, Hmu⟩,
    Hg, %Hwf⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  wp_apply (hBT γ P WR b t st bk bi key endKey kb eb dk de limit)
    $$ [Htxf Hpend Hwtx $Hkey $HendKey] as %keys %vals ⟨Hw, Hkey, HendKey, Hout⟩
  · iframe #
    unfold btW
    iframe
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  iapply HΦ
  iframe Hkey HendKey Hout
  isplitl
  · iexists t, db
    iframe
    iframe #
    ipureintro
    exact Hwf
  iexact Hacc

end proof

end EtcdGrove
end Perennial
