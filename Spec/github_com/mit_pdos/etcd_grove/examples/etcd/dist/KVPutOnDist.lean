/-
`(*kv).Put(ctx, key, val, opts...)` across machines, auth on, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVPutOnDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
written in. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`KV_PutOn_dist`: `(*kv).Put(ctx, key, val, opts...)` across machines, auth on** (mirrors
`client.client_put_on` at the cluster: `etcdPutSpecOn`'s registration replaced by `kvClientAt` at `Γ`, the
member's floor `F` dropped, the update persistent (`writeAuD`: a write is resent after
`ErrInvalidAuthToken`'s token refresh, `isSafeRetryMutableRPC` does not apply), the token's binding replaced
by the principal of `cfg`; a success tells the member and its grant, `writeCheckedD`; the error arm claims
nothing). A lease `0`, or the revocable lease mode, as `etcdPutSpecOn`'s filter: this is also F2's
`KV_PutLease_dist` row (`Put` with `WithLease(id)`, auth on), at `leaseID ≠ 0`; the lease's attach is
`kvOpStep`'s (the update's `Q` sees it), its absence `ErrLeaseNotFound` (a refusal, no step).
No revision lower bound: the in-process `etcdPutSpecMW` gives one only with auth off; the bound was dropped
while `kvRevLb` read the auth-off model (2026-11-27, `notes/axiom-review/onrevlb-weakening.md`) and is not
re-added (since N1b-2 `kvRevLb`'s `kvModel` is `kvModelOn γk srvAuthSt0`; re-adding waits for N5).

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVPutOnDist.lean`). Reviews (`notes/axiom-review/`): `f7-a.md` (`d946f6cbda`) SOUND, `f7-rerev-a.md` (`6d9d9fd662`) SOUND. Unchanged since (`f7-changed-since-review.md`) but for the 2026-11-27 weakening above. -/
abbrev KV_PutOn_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (key val : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      userClientAt cl api eps V Γ cfg ∗ metadata.outMD ctx om ∗ srvReqLogLb γR L₀ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ (opPutModel key val opts).putPanics ∧ (opPutModel key val opts).t = W64 2 ∧
        ((putWireOf (opPutModel key val opts)).leaseID = W64 0 ∨ Γ.kv.lm = .revocable)⌝ ∗
      writeAuD Γ.kv (principalOf cfg) (.put (putWireOf (opPutModel key val opts))) L₀ Q ∗
      ⌜opSizeOk (opPutModel key val opts)⌝ }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #val)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
        ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ kvRevFits (σ.rev + 1) ∧ kvLogOk σ⌝ ∗
        writeCheckedD eps Γ γR (principalOf cfg) (irrPut (putWireOf (opPutModel key val opts))) L₀) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
