/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewLeaseFromLeaseClient.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewLeaseFromLeaseClient
public import Spec.go_etcd_io.etcd.client.v3.WithRequireLeader
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem NewLeaseFromLeaseClient.wp_proof
    (wp_WithRequireLeader : WithRequireLeader.spec (GF := GF) (hG := hG))
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG)) :
    NewLeaseFromLeaseClient.spec (GF := GF) (hG := hG) := by
  intro rlc conn c addr d
  wp_start as ⟨#Hrlc, #Hconn, %Hcnn, #Hlgc, %sl, #Hco, #Hcopts⟩
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %dc %γd ⟨#Hdcc, %_, Hdoc⟩
  imod alloc_broadcast_chan iprop(True) γd dc $$ Hdcc Hdoc with Hdpend
  ihave #Hdu := ownBroadcastChan_Unknown _ _ _ _ $$ Hdpend
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref Hm
  (try wp_auto)
  iStructNamed «$r0»
  ipersist l
  ipersist c
  wp_if_destruct
  · rw [show go_etcd_io.etcd.client.v3.defaultTTL = #(W64 5000000000) from rfl]
    (try wp_auto)
    rw [decide_eq_false Hcnn]
    (try wp_auto)
    wp_apply wp_GetLogger c $$ [] as %lg %Hlgnn
    · iframe #
    (try wp_auto)
    wp_apply context.wp_Background
    wp_apply wp_WithRequireLeader as %rc #HWC
    (try wp_auto)
    ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
    · iPkgInit
    iapply wp_fupd
    wp_apply HWC $$ [] as %sctx %γs %scancel ⟨#Hscan, #Hsctx⟩
    (try wp_auto)
    ipersist donec
    ipersist stopCtx
    ipersist lg
    ipersist firstKeepAliveTimeout
    ipersist remote
    ipersist callOpts
    imod sync.init_Mutex (lessorInv «$r0_ptr») ⊤ (lsF go!"mu" «$r0_ptr»)
      $$ mu [keepAlives Hm stream streamCancel loopErr] with #Hmu
    · inext
      unfold lessorInv
      iexists mref, ∅, GoInterface.nil, func.nil, GoInterface.nil
      iframe
      isplitl
      · iapply BigSepM.bigSepM_empty.2; itrivial
      ileft; ipureintro; rfl
    imod sync.init_Once (lsF go!"firstKeepAliveOnce" «$r0_ptr»)
      (ownBroadcastChan dc γd (iprop(True) : IProp GF) .Pending) iprop(True) ⊤
      $$ [firstKeepAliveOnce Hdpend] with #Honce
    · iframe
    imodintro
    iapply HΦ
    iexists «$r0_ptr»
    isplitr
    · ipureintro; rfl
    unfold lessorAt
    iexists dc, γd, sctx, _, lg, _
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    unfold lessorRemoteAt
    iexists rlc, conn, sl
    iframe #
  · (try wp_auto)
    rw [decide_eq_false Hcnn]
    (try wp_auto)
    wp_apply wp_GetLogger c $$ [] as %lg %Hlgnn
    · iframe #
    (try wp_auto)
    wp_apply context.wp_Background
    wp_apply wp_WithRequireLeader as %rc #HWC
    (try wp_auto)
    ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
    · iPkgInit
    iapply wp_fupd
    wp_apply HWC $$ [] as %sctx %γs %scancel ⟨#Hscan, #Hsctx⟩
    (try wp_auto)
    ipersist donec
    ipersist stopCtx
    ipersist lg
    ipersist firstKeepAliveTimeout
    ipersist remote
    ipersist callOpts
    imod sync.init_Mutex (lessorInv «$r0_ptr») ⊤ (lsF go!"mu" «$r0_ptr»)
      $$ mu [keepAlives Hm stream streamCancel loopErr] with #Hmu
    · inext
      unfold lessorInv
      iexists mref, ∅, GoInterface.nil, func.nil, GoInterface.nil
      iframe
      isplitl
      · iapply BigSepM.bigSepM_empty.2; itrivial
      ileft; ipureintro; rfl
    imod sync.init_Once (lsF go!"firstKeepAliveOnce" «$r0_ptr»)
      (ownBroadcastChan dc γd (iprop(True) : IProp GF) .Pending) iprop(True) ⊤
      $$ [firstKeepAliveOnce Hdpend] with #Honce
    · iframe
    imodintro
    iapply HΦ
    iexists «$r0_ptr»
    isplitr
    · ipureintro; rfl
    unfold lessorAt
    iexists dc, γd, sctx, _, lg, _
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    unfold lessorRemoteAt
    iexists rlc, conn, sl
    iframe #

end proof

end EtcdGrove
end Perennial
