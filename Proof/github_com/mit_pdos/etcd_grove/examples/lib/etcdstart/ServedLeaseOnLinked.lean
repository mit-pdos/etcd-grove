/-
**`lease_served_on`** (auth-lease S4): the linking half of `ServedLeaseOn.lean` (see its header), over
linked results (`client.etcd_lease_auth_served_on`, `client.etcd_lease_read_served`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLease
public import Proof.go_etcd_io.etcd.client.v3.AuthnServedOn
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLeaseLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLeaseOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **etcd's Lease service served with auth on** (see the file header): in the revocable lease mode,
with auth on at `γa`, from the server token `grpcServerAt` of the address (whose registrations include
`grpcLeaseUp`'s), the four Lease methods registered (`etcdLeaseServedOn`). -/
theorem lease_served_on (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (A : v3rpc.KVAns GF) (il im iu : GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (γ : GName) (γa : auth.AuthNames) (hγa : E.authMode = .on γa) (hlm : ρ.rd.kv.lm = .revocable)
    (hA : A.revR = mvcc.api.mvccReaders E.γ 1)
    (HT : threadBound GF ≤ 2 ^ 30 - 1) (Hrb : receiptBound GF ≤ 2 ^ 62) (hP : leasePeersOk)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM true s E ρ ∗ isServerReadM true s E ρ.rd ∗ srvAuthLb s E ∗
        □ (|==> idCred ρ.ids 1) ∗ srvLeaseRd s E .revocable ∗ grpcLeaseUp s A regs ∗
        srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
        srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
        srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ∗
        grpcServerAt addr [il, im, iu] regs etcdTys γ ∗ srvRevokeBuilt s E ∗ srvRunPool s E ρ.rd ⊢
      |={⊤}=> etcdLeaseServedOn addr s E ρ := by
  iintro ⟨#Pv, #Ps, #Hreq, #Hrd, #Hlb, #HNR, #Hlr, #Hlu, #Hil, #Him, #Hiu, #Hat, #Hb, #Hrp⟩
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [hγa]; rfl
  iunfold grpcLeaseUp at Hlu
  icases Hlu with ⟨%ql, %pl, %lcid, %lmid, %HLr, #Hql, #Hlat⟩
  -- the grant and the revocation
  imod (client.etcd_lease_auth_served_on addr ql pl s A lcid lmid E ρ ρ.rd il im iu regs γ γa hγa
      hlm rfl HLr HL) $$ [] with ⟨#HG, #HR⟩
  · iframe #
  -- the reads' contract, from the server
  ihave #HreqM : isServerReqM E.authOn s E ρ $$ []
  · rw [hon]; iexact Hreq
  ihave #HrdM : isServerReadM E.authOn s E ρ.rd $$ []
  · rw [hon]; iexact Hrd
  ihave #Hauth := srvAuthAt_of_viewsM true s E ρ ρ.rd $$ [Hreq Hrd]
  · iframe #
  ihave #HaLL := srvAuthLeaseLb_of_server s E ρ.rd (Or.inr ⟨γa, hγa⟩) $$ []
  · iframe #
  icases v3rpc.srvHeaderFacts_server E.authOn s E ρ $$ HreqM with ⟨%cs, %ms, #Hhf⟩
  ihave ⟨#Hlrd, #Hpool⟩ := srvLeaseRd_lessorRd s E .revocable $$ Hlr
  ihave #HLR := v3rpc.raftLeaseRead_server s E ρ ρ.rd (mvcc.api.mvccLeases E.γ) cs ms HT Hrb hP
    $$ []
  · iframe #
  imod (client.etcd_lease_read_served addr ql pl s A lcid lmid E ρ.rd (mvcc.api.mvccLeases E.γ)
      il im iu regs γ hA HLr HL) $$ [] with ⟨#HT', #HL'⟩
  · iframe #
  imodintro
  iunfold etcdLeaseServedOn
  iframe #

end served

end etcdstart
end EtcdGrove
end Perennial
