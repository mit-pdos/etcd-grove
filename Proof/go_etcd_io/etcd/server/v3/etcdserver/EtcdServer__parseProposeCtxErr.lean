/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__parseProposeCtxErr.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__parseProposeCtxErr
public import Spec.errors.IsCtxErr
public import Spec.time.Time__After
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getLead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isConnectedToQuorumSince
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isConnectedSince
public import EtcdDeps.GeneratedProof.go_etcd_io.raft.v3

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
local macro "ppce_exit" : tactic => `(tactic| (
  iapply HΦ; iunfold srvLeadTimeReader; iframe Hrd; isplitr; · ipureintro; simp
  first | iexact HaTOLF | iexact HaTOCL | iexact HaTO | iexact HaCan))

set_option hygiene false in
/-- After the leader-failure test: the leader's connectivity. -/
local macro "ppce_tail" : tactic => `(tactic| (
  wp_apply hGL s $$ [] as %ld -
  · iframe #; iunfold srvAtomicU64 at Hlead; iunfold srvLeadInv; iexact Hlead
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto); ppce_exit
  · wp_apply hMid s v.memberID $$ []
    · iframe #
    (try wp_auto)
    wp_if_destruct
    · wp_apply hMid s v.memberID $$ []
      · iframe #
      (try wp_auto)
      wp_apply hMem v.cluster as %msl -
      (try wp_auto)
      wp_apply hQ as %bq -
      cases bq <;> (try wp_auto) <;> ppce_exit
    · (try wp_auto)
      wp_apply hC as %bc -
      cases bc <;> (try wp_auto) <;> ppce_exit))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.parseProposeCtxErr.wp_proof
    (hIs : errors.IsCtxErr.spec (GF := GF) (hG := hG))
    (hAfter : time.Time.After.spec (GF := GF) (hG := hG))
    (hGL : EtcdServer.getLead.spec (GF := GF) (hG := hG))
    (hMid : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hMem : membership.RaftCluster.Members.spec (GF := GF) (hG := hG))
    (hQ : isConnectedToQuorumSince.spec (GF := GF) (hG := hG))
    (hC : isConnectedSince.spec (GF := GF) (hG := hG)) :
    EtcdServer.parseProposeCtxErr.spec (GF := GF) (hG := hG) := by
  intro s E ρ err start Herr
  wp_start as ⟨#Hsrv, Hrd, #Herrv⟩
  iunfold isServerReq at Hsrv
  icases Hsrv with ⟨%v, #Hv⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, #Het, #Htm, -, -, -, -, #Hmid, #Hlead, #Hcl, #Htr,
    -, -, -, -⟩
  ihave #Perrors : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pmem : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave Hci : (context.isInit : IProp GF) $$ []
  · iapply context.isInit_access $$ Pctx
  iNamed Hci
  icases HCanceled with ⟨%eC, #HeC, %-⟩
  icases HDeadlineExceeded with ⟨%eD, #HeD, %-⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, -, ⟨-, -, -, #HCan, #HTO, #HTOLF, #HTOCL, -⟩⟩, -⟩
  ihave ⟨%eCan, #HeCan, #HaCan⟩ := errVarLeaf_get _ $$ HCan
  ihave ⟨%eTO, #HeTO, #HaTO⟩ := errVarLeaf_get _ $$ HTO
  ihave ⟨%eTOLF, #HeTOLF, #HaTOLF⟩ := errVarLeaf_get _ $$ HTOLF
  ihave ⟨%eTOCL, #HeTOCL, #HaTOCL⟩ := errVarLeaf_get _ $$ HTOCL
  wp_auto
  wp_apply hIs err eC Herr $$ [] as %b1 %Hb1
  · iframe #
  cases b1
  · (try wp_auto)
    wp_apply hIs err eD Herr $$ [] as %b2 %Hb2
    · iframe #
    cases b2
    · -- the `default` branch: `err` is `Canceled`'s or `DeadlineExceeded`'s, so one `Is` held
      iexfalso
      icases Herrv with (#H | #H)
      · icombine H HeC gives %h
        exact absurd (Hb1 h) (by simp)
      · icombine H HeD gives %h
        exact absurd (Hb2 h) (by simp)
    · (try wp_auto)
      iunfold srvLeadTimeReader at Hrd
      wp_apply sync.RWMutex.wp_RLock _ _ $$ [Hrd] as ⟨Hrl, HP⟩
      · iframe #; iframe Hrd
      iunfold leadTimeP at HP
      icases HP with ⟨%tl, Htl⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock _ _ $$ [Hrl Htl] as Hrd
      · iframe #; iframe Hrl; inext; iunfold leadTimeP; iexists tl; iframe Htl
      (try wp_auto)
      wp_apply time.Time.wp_ptr_Add $$ [$curLeadElected] as %prev curLeadElected
      (try wp_auto)
      wp_apply hAfter $$ [$start] as %b3 start
      cases b3
      · (try wp_auto)
        ppce_tail
      · (try wp_auto)
        wp_apply time.Time.wp_ptr_Before $$ [$start] as %b4 start
        cases b4
        · (try wp_auto)
          ppce_tail
        · (try wp_auto)
          ppce_exit
  · rw [decide_eq_true rfl]
    (try wp_auto)
    iapply HΦ; iframe Hrd; isplitr; · ipureintro; simp
    iexact HaCan

end proof

end EtcdGrove
end Perennial
