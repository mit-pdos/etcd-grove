/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__CommitAndStop.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__CommitAndStop
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__Unlock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.batchTxBuffered.CommitAndStop.wp_proof
    (hlock : backend.batchTx.lock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG))
    (hBU : backend.batchTx.Unlock.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.CommitAndStop.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t X Y
  wp_start as ⟨#Hb, #Ht, Ho, Hq, HX, #Hreq⟩
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t2, %rt, %db1, %lg2, #Ht2, #Hrt, #-, %-, #Hmi, #-, #-, #Hrg, #-, #-, #Hci, %HP⟩
  wp_auto
  wp_method_call
  wp_call
  wp_apply (hlock γ P W Pk b t (1 : Qp).half.half) $$ [$Hq] as ⟨%st, Hl, %Hfo, ⟨HWv, HWR⟩, Hq⟩
  · iframe #
  ihave Hl := batchLocked_W γ P b st $$ Hl
  wp_apply (hC γ P W Pk b t rt st false true 0 0 X Y (vData P (st.C, st.R))) $$ [$Hl $HWR Ho Hq HX]
    as ⟨HY, HWR, -, Hpost⟩
  · iframe #
    isplitr
    · ipureintro
      exact ⟨room_of_freeOk HP Hfo.1, Hfo.2, Hfo.1.2.2.2.1⟩
    isplitr
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [vData_free P st Hfo.1.1 Hfo.1.2.2.1 Hfo.1.2.2.2.1]
      iapply thinV_refl
    unfold payIn
    simp only [↓reduceIte]
    isplitl [Ho Hq]
    · isplitl [Ho]
      · iexact Ho
      · iexact Hq
    iexact HX
  try simp only [↓reduceIte]
  icases Hpost with ⟨Hown, Hpend, #Hbs, Hout, Htok⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hBU γ P W Pk b t) $$ [$Hown Hpend]
  · iframe #
    iright
    iframe
  iapply HΦ
  iframe Hbs HY Htok
  -- (R2b-3c part 2) the stopped lock's client resources go with the database
  unfold bDBOut
  iframe Hout HWv HWR

end proof

end EtcdGrove
end Perennial
