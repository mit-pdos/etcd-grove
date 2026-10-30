/-
**M2, the storage side: linkv3p's members over the Draft** (review round 2's N1; the route in
`notes/m2-storage-plan.md`, "Step 1 on the merged lean"). Imported by nothing; no `axiom`, no
`sorry`.

A member's watch facts gain the server's mode, off (`memberWatchD`, `memberAtD`: `¬ kbCmpM E.γ.kb`
appended to their pure facts), which `startCluster` reads off each member's `memberServed`
(`envAgree E E₀`, redefined: `envAgreeD_off`, with linkv3p's allocation's `E₀.cmp = false`), so
that the member's drafted facts (`watchMemberFactsD`, with its "no compactor" fact) follow from its
watch server (`memberWatchD_facts`). The watch server and its stream are read over the Draft's
copies (`isWatchServerD`, `watchUpD`: today's names, redefined in place at the switch).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchEnv
public import Proof.go_etcd_io.etcd.client.v3.M2StorageDraft

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **Draft of `memberWatch`** (N1): the member's server off, appended to the pure facts. The rest
as today. -/
def memberWatchD (γr : ReadNames) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(isServerRead s E ρ.rd ∗ (∃ pw : Loc, v3rpc.isWatchServerD pw R) ∗
    ⌜R.E = E ∧ v3rpc.memberOf γr.raft γr.kv ρ.rd ∧ ρ.rd.kv.st = γr.kv.st ∧
      ¬ mvcc.kbCmpM E.γ.kb⌝)

instance memberWatchD_persistent (γr : ReadNames) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (R : v3rpc.WSrv GF) : Persistent (memberWatchD γr s E ρ R) := by
  unfold memberWatchD; infer_instance

/-- **A member's drafted watch facts are its `watchMemberFactsD`** (N1; `memberWatch_facts` with
the "no compactor" fact from the watch server at the server's mode). -/
theorem memberWatchD_facts (V : client.WEnv GF) (γr : ReadNames) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (hWM : V.WM = v3rpc.etcdModelOfHistory γr.raft γr.kv)
    (hWL : V.WL = v3rpc.histWL γr.raft γr.kv) (hK : V.kst = γr.kv.st)
    (hlog0 : γr.kv.log0 = [[], []]) (hrb : receiptBound GF ≤ 2 ^ 62) :
    memberWatchD γr s E ρ V.R ⊢ client.watchMemberFactsD V := by
  iintro #H
  iunfold memberWatchD at H
  icases H with ⟨#Hrd, ⟨%pw, #Hws⟩, %h⟩
  obtain ⟨hE, hm, hst, hoff⟩ := h
  have hoff' : ¬ mvcc.kbCmpM V.R.E.γ.kb := by rw [hE]; exact hoff
  ihave #Hws' := v3rpc.isWatchServerD_to pw V.R hoff' $$ Hws
  ihave #Hmf := memberWatch_facts V γr s E ρ hWM hWL hK hlog0 hrb $$ []
  · iunfold memberWatch
    iframe #
    ipureintro; exact ⟨hE, hm, hst⟩
  iapply client.watchMemberFactsD_of_server V pw hoff' $$ [Hmf Hws]
  iframe #

set_option linter.unusedVariables false in
/-- **Draft of `memberAt`** (N1; `Defs.lean`): the member's server off, appended to the pure facts
(from `memberServed`'s `envAgree E E₀` at `startCluster`, `envAgreeD_off`); the watch server and
its stream over the Draft's copies (today's names at the switch). The rest as today. -/
def memberAtD (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E : apply.AEnv GF)
    (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft) : IProp GF :=
  iprop(forwards b c ∗ isServerRead s E ρ.rd ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid) ∗
    ⌜noRefusalAt c⌝ ∗ (∃ pw : Loc, v3rpc.isWatchServerD pw R) ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
    isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) c
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUpD R.γ)
      (fun γs Dn => v3rpc.watchStreamSpec γs R.γ R.cid R.mid Dn) ∗
    ⌜(∃ reg : GName, ρ.rd.raft = ⟨{ γ with reg := reg }, [], W64 0⟩) ∧ ρ.rd.kv.c0 = W64 0 ∧
      ρ.rd.kv.ch0 = apply.alarmChain false false false ∧ ρ.rd.kv.log0 = [[], []] ∧
      ¬ mvcc.kbCmpM E.γ.kb⌝)

instance memberAtD_persistent (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames)
    (E : apply.AEnv GF) (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft) :
    Persistent (memberAtD γn s id ρ E cid mid R b c γ) := by
  unfold memberAtD; infer_instance

/-- **A member's drafted watch facts, from its drafted `memberAt`** (N1; `MainWatch.lean`'s step
after unfolding `memberAt`, which builds the `memberWatch` of each member: the mode now carried
along). -/
theorem memberWatchD_of_at (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames)
    (E : apply.AEnv GF) (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft)
    (γr : ReadNames) (hm : v3rpc.memberOf γr.raft γr.kv ρ.rd) (hst : ρ.rd.kv.st = γr.kv.st) :
    memberAtD γn s id ρ E cid mid R b c γ ⊢ memberWatchD γr s E ρ R := by
  iintro #H
  iunfold memberAtD at H
  icases H with ⟨-, #Hrd, -, -, -, -, -, ⟨%pw, #Hws⟩, %HR, -, %Hp⟩
  iunfold memberWatchD
  iframe #
  ipureintro; exact ⟨HR.2, hm, hst, Hp.2.2.2.2⟩

end draft

end linkv3p
end EtcdGrove
end Perennial
