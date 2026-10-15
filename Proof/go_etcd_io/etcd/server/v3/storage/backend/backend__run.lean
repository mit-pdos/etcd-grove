/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__run.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__run
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__safePending
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__CommitAndStop
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.backend.run.wp_proof
    (hSP : backend.batchTx.safePending.spec (GF := GF) (hG := hG))
    (hlock : backend.batchTx.lock.spec (GF := GF) (hG := hG))
    (hC : backend.batchTxBuffered.commit.spec (GF := GF) (hG := hG))
    (hBU : backend.batchTx.Unlock.spec (GF := GF) (hG := hG))
    (hCS : backend.batchTxBuffered.CommitAndStop.spec (GF := GF) (hG := hG)) :
    backend.backend.run.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b sc dc γsc γdc u d
  wp_start as ⟨#Hb, #Hsc, #Hbi, Hdcp, Hrt, Hq, Hus⟩
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t, %rt, %db, %lg, #Ht, #Hrt, #Hlg, %Hlgn, #Hmi, #Hbe, #Hm, #Hrg, #Hmug, #Hisdb, #Hci, %HP⟩
  unfold isStopChansAt
  icases Hsc with ⟨#Hscf, #Hdcf, #Hscb, #Hdcb, #Hinv⟩
  ihave #Hscc := ownBroadcastChan_is_chan _ _ _ _ $$ Hscb
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply (lc := 2) time.wp_NewTimer as %tm %tch %γt #Htm
  ihave #Htm' := Htm
  iunfold time.isTimer at Htm'
  icases Htm' with ⟨#HtC, #Hbag, -⟩
  ihave #Htch := is_bag_is_chan _ _ _ $$ Hbag
  ihave Hus : (∃ u : Nat, ghostVar γ.used (1 : Qp).half u) $$ [Hus]
  · iexists u; iexact Hus
  wp_for
  icases Hus with ⟨%u, Hus⟩
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    iframe Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %v -
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType batchTxBuffered.ty) (m := go!"safePending") #t]
    wp_call
    wp_apply (lc := 2) (hSP γ P W Pk b t u) $$ [$Hq $Hus] as %p ⟨Hq, Hus, Hp⟩
    · iframe #
    by_cases hp : p = W64 0
    · subst hp
      wp_auto
      wp_apply (_root_.Perennial.time.Timer.wp_Reset tm tch γt d) $$ [$Htm] as %bb -
      wp_for_post
      iframe
      iexists u
      iexact Hus
    · icases Hp with (%Hp0 | #Hlb)
      · exact absurd Hp0 hp
      rw [decide_eq_false hp]
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType batchTxBuffered.ty) (m := go!"Commit") #t]
      wp_call
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType batchTxBuffered.ty) (m := go!"lock") #t]
      wp_call
      wp_apply (hlock γ P W Pk b t (1 : Qp).half.half) $$ [$Hq] as ⟨%st, Hl, %Hfo, ⟨HWv, HWR⟩, Hq⟩
      · iframe #
      ihave Hl := batchLocked_W γ P b st $$ Hl
      wp_apply (hC γ P W Pk b t rt st false false 1 u) $$ [$Hl $HWR Hus] as ⟨HWR, Hpo, Hpost⟩
      · iframe #
        isplitr
        · ipureintro
          exact ⟨room_of_freeOk HP Hfo.1, Hfo.2, Hfo.1.2.2.2.1,
        fun _ => vData_free P st Hfo.1.1 Hfo.1.2.2.1 Hfo.1.2.2.2.1⟩
        unfold payIn
        rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
        iframe Hus Hlb
      unfold payOut
      rw [if_pos ⟨rfl, rfl⟩]
      icases Hpo with ⟨%u', Hus⟩
      try simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hpost with ⟨%st2, %db2, Hown, Hph2, Hg2, %Hfin, -⟩
      rw [method_unfold (t := go.GoType.PointerType batchTxBuffered.ty) (m := go!"Unlock") #t]
      wp_call
      unfold batchPhys
      icases Hph2 with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
      rw [Hfin.2.2]
      wp_auto
      wp_apply (hBU γ P W Pk b t) $$ [$Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hg2 HWv HWR]
      · iframe #
        ileft
        iexists st2, db2
        iframe HWv HWR Hg2
        isplitl
        · unfold batchPhys
          iexists hk
          rw [Hfin.2.2]
          iframe
          iframe #
        · ipureintro
          exact Hfin.1
      wp_apply (_root_.Perennial.time.Timer.wp_Reset tm tch γt d) $$ [$Htm] as %bb -
      wp_for_post
      iframe
      iexists u'
      iexact Hus
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γsc
    isplitr
    · ipureintro; rfl
    iframe Hscc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hscb
    iintro ⟨#Hsq, -⟩
    wp_auto
    imod (stop_get γ sc γsc) $$ [$Hinv $Hsq $Hrt] with Hhalf
    wp_apply (hCS γ P W Pk b t) $$ [$Hhalf $Hq] as #Hbs
    · iframe #
    wp_for_post
    wp_apply (_root_.Perennial.time.Timer.wp_Stop tm) $$ [] as %bb -
    · ileft; iexists tch, γt; iexact Htm
    wp_apply (wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
      dc γdc iprop(True)) $$ [$Hdcp] as -
    · imodintro
      itrivial
    iapply HΦ
    itrivial
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
