/-
**The lease checks' auth store, from the server's views** (the lease-src plan, 2026-11-02;
`notes/lease-src-plan.md`). Lean-first (no Rocq counterpart).

`srvAuthLeaseLb s E`, a premise of the lease discharges (`v3rpc.raftLeaseRead_of_server`,
`raftLeaseRenew_of_server`), from what `NewServer` and `Start` give: with auth off, the request side's
store (`isServerReqM false`'s `isAuthStore … .off`, whose verdicts are the lower-bound ones: auth
disabled, every check passing); with auth on, the read side's (`srvAuthLb`, whose `authStoreLbM`
carries the lease checks' methods since this plan).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck

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

/-- **The lease checks' auth store, in the server's mode** (see the file header). -/
theorem srvAuthLeaseLb_of_reqM (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) E.authOn s E ρ ∗ srvAuthLb s E ⊢ srvAuthLeaseLb s E := by
  sorry

end proof

end EtcdGrove
end Perennial
