/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__serveWatchClient.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveWatchClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.serveWatchClient.wp_proof :
    watchGRPCStream.serveWatchClient.spec (GF := GF) (hG := hG) := by
  intro V G callSl wc γs Dn cd' e γc i sent0 tok
  wp_start as ⟨#Hwgs, #Hcs, #Hspec, Htok, #Hep, Hprod, Hcnt⟩
  ihave #Hwgs' := Hwgs
  iunfold isWGS at Hwgs'
  icases Hwgs' with ⟨%Hwnn, -, #Hfacts, -, -, -, -, -, -, -, -, #Frespc, #Fdonec, #Ferrc, -, -,
    -, -, -, #Herr, -, #Hdone, #Hspsc⟩
  iunfold watchSrvFacts at Hfacts
  icases Hfacts with ⟨-, #Hfacts⟩
  iunfold watchConnFacts at Hfacts
  icases Hfacts with ⟨-, -, -, -, #Heof, -⟩
  iunfold v3rpc.cliWatchStreamIs at Hcs
  iunfold cliBidiStreamIs at Hcs
  icases Hcs with ⟨%ci, %Hci, -, #HRecv, -⟩
  subst Hci
  wp_auto
  ihave HI : iprop(∃ (L : List v3rpc.WatchRespM) (sent : List Loc),
      "Htok" ∷ cliRecvTok (Rep := v3rpc.pbWatchResponse) γs L ∗ "Hprod" ∷ sspscProducer G.γr sent ∗
      "Hcnt" ∷ monoNatAuthOwn γc 1 sent.length ∗
      "%Hlen" ∷ ⌜sent.length = sent0.length + L.length⌝) $$ [Htok Hprod Hcnt]
  · iexists [], sent0
    iframe
    ipureintro; rfl
  wp_for HI
  wp_bind (App (Val #(methods ci.ty go!"Recv" ci.v)) (Val #()))
  iapply HRecv $$ %L Htok
  inext
  iintro %resp %err Hr
  icases Hr with (⟨%Herr0, %m, Hm, HDn, Htok⟩ | ⟨%Hrn, #Heofe, %Hen, Htok, -⟩ | ⟨%Hrn, #Hse, Htok⟩)
  · subst Herr0
    ihave ⟨Htok, #Hlb⟩ := cliRecvTok_lb $$ Htok
    -- (D25) the epoch's count past the response
    imod mono_nat_own_update (sent.length + 1) (Nat.le_succ _) $$ Hcnt with ⟨Hcnt, #Hcl⟩
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, G.respc,
        G.γr.chanName, resp
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · ihave #H := Hspsc
        unfold isSspsc
        icases H with ⟨$, -⟩
      iunfold v3rpc.watchSpec at Hspec
      iunfold v3rpc.watchStreamSpec at Hspec
      ihave Hwd := Hspec $$ %L.length %m
      icases Hwd with ⟨Hto, -⟩
      ihave HDn := Hto $$ HDn
      iapply sspsc_send_au G.γr G.respc _ _ sent resp _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hm HDn]
      · iframe
        iunfold respcE
        iexists e, sent0.length, γs, γc, i, tok
        simp only [Int.toNat_natCast]
        iframe Hep Hcl
        isplitr
        · ipureintro; omega
        iunfold respcElem
        iexists m, L
        have Hk : (((sent.length - sent0.length : Nat) : Int)).toNat = L.length := by
          simp only [Int.toNat_natCast]; omega
        rw [Hk]
        iframe
        isplitl
        · iunfold v3rpc.downLbW; iunfold downLb at Hlb; iexact Hlb
        ipureintro; rfl
      inext
      iintro Hprod
      (try wp_auto)
      wp_for_post
      iframe
      iexists L ++ [m], sent ++ [resp]
      simp only [List.length_append, List.length_singleton]
      iframe
      ipureintro; omega
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdone
      iapply broadcast_chan_receive $$ Hdone
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · cases err with
    | nil => exact absurd rfl Hen
    | ok ei =>
    iunfold eofOk at Heof
    ihave ⟨%Hok, #Hst⟩ := Heof $$ %(GoInterface.ok ei) Heofe
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.errc,
        G.γerr, GoInterface.ok ei
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iapply is_bag_is_chan $$ Herr
      iapply bag_send_au G.γerr G.errc (errP G.γr G.γep) _ _ $$ [$Hlc1 $Hlc2] Herr [Hprod Hcnt]
      · iunfold errP
        isplitr
        · ipureintro; exact Hen
        isplitr
        · iright; iexact Heofe
        iframe Hst
        iunfold prodBack
        iexists e, sent0.length, γs, γc, i, tok, sent
        iframe Hep Hprod Hcnt
        ipureintro; omega
      inext
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdone
      iapply broadcast_chan_receive $$ Hdone
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · ihave #Hse' := Hse
    iunfold cliStreamErr at Hse'
    icases Hse' with ⟨%Hok, #Hst, -⟩
    cases err with
    | nil => exact absurd rfl Hok.1
    | ok ei =>
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.errc,
        G.γerr, GoInterface.ok ei
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iapply is_bag_is_chan $$ Herr
      iapply bag_send_au G.γerr G.errc (errP G.γr G.γep) _ _ $$ [$Hlc1 $Hlc2] Herr [Hprod Hcnt]
      · iunfold errP
        isplitr
        · ipureintro; exact Hok.1
        isplitr
        · ileft; iexact Hse
        iframe Hst
        iunfold prodBack
        iexists e, sent0.length, γs, γc, i, tok, sent
        iframe Hep Hprod Hcnt
        ipureintro; omega
      inext
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdone
      iapply broadcast_chan_receive $$ Hdone
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
