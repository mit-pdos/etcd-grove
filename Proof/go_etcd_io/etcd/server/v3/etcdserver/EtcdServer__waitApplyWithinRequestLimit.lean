/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__waitApplyWithinRequestLimit.lean`
(etcd-io/etcd#22527, branch `pr-verify/etcd-22527`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitApplyWithinRequestLimit
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply exit passes the request limit**: an applied index `ai` the applied index has
reached at least `c - 5000` (for `5000 < c`) puts `c` within `exceedsRequestLimit`'s normal gap
(`c ≤ ai + 5000`, in the integers: Go's `appliedIndex+maxNormalGap` wraps only past `2^64 - 5000`,
where the gap holds as well). -/
theorem waitApply_within_limit (c ai : w64) (hc : 5000 < uint.Z c)
    (hai : uint.Z (c - W64 5000) ≤ uint.Z ai) : uint.Z c ≤ uint.Z ai + 5000 := by
  word

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.waitApplyWithinRequestLimit.wp_proof
    (hGCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG)) :
    EtcdServer.waitApplyWithinRequestLimit.spec (GF := GF) (hG := hG) := by
  intro s E γr d
  wp_start as #Hsr
  ihave #Hsr' := Hsr
  iunfold isServerRead at Hsr'
  icases Hsr' with ⟨%v, #Hf⟩
  iunfold srvReadFieldsAt at Hf
  icases Hf with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hci, #Hawf, #Hwt,
    -, -, #Hstf, #Hst⟩
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (lc := 2) hGCI s γr none $$ [] as %c ⟨#Hc, -, -⟩
  · iframe #; simp only [srvCommittedOwnOpt]; itrivial
  (try wp_auto)
  wp_if_destruct
  · -- `ci <= maxNormalGap`: no wait
    (try wp_auto)
    iapply HΦ
    iexists c
    iframe Hc
    iunfold waitApplyExit
    ileft; ipureintro; word
  wp_apply time.wp_NewTimer as %t %tc %γt #Ht
  ihave #Ht' := Ht
  iunfold time.isTimer at Ht'
  icases Ht' with ⟨#HtC, #HtB, -⟩
  (try wp_auto)
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, #HW, -⟩
  rw [Hwi]
  wp_apply HW $$ %(c - W64 5000) as %ch ⟨%Q, #Hch, #HQ⟩
  iunfold waitBcast at Hch
  icases Hch with ⟨%γa, #Hch⟩
  iunfold stopChan at Hst
  icases Hst with ⟨%γst, #Hst⟩
  (try wp_auto)
  wp_apply_core chan.wp_select_blocking
  -- `<-s.applyWait.Wait(ci - maxNormalGap)`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γa
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hch
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hch
    iintro ⟨#HQc, -⟩
    (try wp_auto)
    wp_apply time.Timer.wp_Stop $$ [] as %_ -
    · ileft; iexists tc, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists c
    iframe Hc
    iunfold waitApplyExit
    iright; ileft
    isplitr
    · ipureintro; word
    iapply HQ $$ HQc
  -- `<-t.C`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance,
      inferInstance, tc, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HtB
    iapply bag_recv_au γt tc _ _ $$ [$Hlc1 $Hlc2] HtB
    inext
    iintro %tm -
    (try wp_auto)
    wp_apply time.Timer.wp_Stop $$ [] as %_ -
    · ileft; iexists tc, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists c
    iframe Hc
    iunfold waitApplyExit
    iright; iright; itrivial
  -- `<-s.stopping`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.stopping, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hst
    iapply stop_chan_receive _ _ _ _ _ $$ Hst
    iintro ⟨-, -⟩
    (try wp_auto)
    wp_apply time.Timer.wp_Stop $$ [] as %_ -
    · ileft; iexists tc, γt; iexact Ht
    (try wp_auto)
    iapply HΦ
    iexists c
    iframe Hc
    iunfold waitApplyExit
    iright; iright; itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
