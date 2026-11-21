/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__waitLeader.lean`:
`s.waitLeader(ctx)` (`v3_server.go`), the cluster's member at the leader's id
(`s.cluster.Member(s.Leader())`, a fresh clone or `nil`); while `nil`, a `select` over
`time.After` (ask again), `s.stopping` (`ErrStopped`) and `ctx.Done()` (`ErrNoLeader`); then
`ErrNoLeader` for a member without peer URLs, else the member, persisted. Lean-first; until
prove-srvloops (2026-11-21) a names-only contract (the lease-renew plan's C4, 2026-11-01).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Member
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.waitLeader.wp_proof
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hMem : membership.RaftCluster.Member.spec (GF := GF) (hG := hG)) :
    EtcdServer.waitLeader.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr ctx cd
  wp_start as ⟨#Hreq, #Hrd, #Hctx⟩
  ihave ⟨⟨%rv, #Hrf⟩, -⟩ := (isServerReqM_split _ _ _ _).1 $$ Hreq
  iunfold srvReqFieldsAtM at Hrf
  icases Hrf with ⟨-, -, -, -, -, -, -, -, -, #Het, #Htm, -, -, -, -, -, #Hlead, #Hcl, -, #Hpeers,
    -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨-, #Hrc, -⟩
  iunfold isServerReadM at Hrd
  icases Hrd with ⟨%v, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hstf,
    #Hstc, -⟩
  ihave #HLI : srvLeadInv (GF := GF) s $$ []
  · iunfold srvAtomicU64 at Hlead; iunfold srvLeadInv; iexact Hlead
  ihave #Pmb : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  -- the error variables: `ErrStopped` (the server's fact), `ErrNoLeader` (its package's)
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, -, ⟨-, -, #HStop, -⟩⟩, -⟩
  ihave ⟨%eStop, #HeStop, #HaStop⟩ := errVarLeaf_get _ $$ HStop
  ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Herr
  icases Hei with ⟨-, #Hev, -⟩
  ihave #NNL := EtcdGrove.errorsNewVars_mem
    (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoLeader)
    (m := go!"etcdserver: no leader")
    (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; simp) $$ Hev
  ihave #LNL := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NNL
  ihave ⟨%eNL, #HeNL, #HaNL⟩ := errVarLeaf_get _ $$ LNL
  iunfold stopChan at Hstc
  icases Hstc with ⟨%γst, #Hstc⟩
  ihave #Hctx' := Hctx
  iunfold v3rpc.ctxDoneErr at Hctx'
  iNamed Hctx'
  wp_auto
  -- `leader := s.cluster.Member(s.Leader())`
  wp_apply hLead s $$ [] as %ld -
  · iframe #
  wp_apply (membership.RaftCluster.Member.spec_static hMem rv.cluster ld) $$ [] as %l0 Hl0
  · iframe #
  (try wp_auto)
  ihave IH : iprop(∃ l : Loc, "leader" ∷ leader_ptr ↦ l ∗
      "Hl" ∷ (⌜l = null⌝ ∨
        ∃ (mv : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member) (pus cus : List GoString),
          l ↦ mv ∗ mv.RaftAttributes'.PeerURLs' ↦* pus ∗ mv.Attributes'.ClientURLs' ↦* cus)) $$
      [leader Hl0]
  · iexists l0; simp only [named]; iframe
  wp_for IH
  wp_if_destruct
  · -- still no leader: wait an election
    wp_apply (lc := 2) (time.After.spec_pkgInit time.wp_After _) as %tch %γa #Htch
    (try wp_auto)
    wp_apply HDone as %chD %γD #HcD
    (try wp_auto)
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the timer: ask again
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γa
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Htch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
      inext
      iintro %t -
      (try wp_auto)
      wp_apply hLead s $$ [] as %ld' -
      · iframe #
      wp_apply (membership.RaftCluster.Member.spec_static hMem rv.cluster ld') $$ [] as %l1 Hl1
      · iframe #
      (try wp_auto)
      wp_for_post
      iframe
      iexists l1; iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `s.stopping`: `ErrStopped`
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.stopping, γst
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hstc
      iapply stop_chan_receive _ _ _ _ _ $$ Hstc
      iintro ⟨-, -⟩
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨rfl, fun h => by cases h⟩
      iexact HaStop
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the context done: `ErrNoLeader`
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chD, γD
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply context.isContextDone_is_chan $$ HcD
      iapply context.isContextDone_receive _ _ _ _ $$ HcD
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨rfl, fun h => by cases h⟩
      iexact HaNL
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- a leader
    icases Hl with (%Hnl | ⟨%mv, %pus, %cus, Hm, Hpus, -⟩)
    · exact absurd Hnl (by assumption)
    ipersist Hm
    ipersist Hpus
    ihave #Hm2 := Hm
    iStructNamed Hm2
    iStructNamed RaftAttributes
    (try wp_auto)
    wp_if_destruct
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨rfl, fun h => by cases h⟩
      iexact HaNL
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists mv, pus
      iframe #

end proof

end EtcdGrove
end Perennial
