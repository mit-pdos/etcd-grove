/-
`(*lessor).TimeToLive(ctx, id, WithAttachedKeys())` at member `mid`, auth on, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/LeaseTimeToLiveKeysOnDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
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

/-- **`Lease_TimeToLiveKeysOn_dist`: `(*lessor).TimeToLive(ctx, id, WithAttachedKeys())` at member
`mid`, auth on** (F2's `Lease_TimeToLiveKeys_dist` row; mirrors `lessor.TimeToLive.spec` at
`etcdLeaseTTLSpecMdW` with `leaseKeysFold gs false = true`: `checkLeaseTimeToLive` runs at the member that
received the call, over its own auth store and its own lessor (`s.lessor.Lookup`), before the TTL itself
is asked of the leader. So the success is the echoed `ID` (F2's view-free claim: nothing of the TTL, which
the leader answers) and member `mid`'s keys verdict (`leaseKeysVerdictFrom`: the lease absent, or each
attached key readable) at its published auth index `n ≥ n₀` and its lessor's index `j ≥ m₀`; or the
member's admin pass).

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/LeaseTimeToLiveKeysOnDist.lean`). Reviews (`notes/axiom-review/`): `f7-c.md` (`d946f6cbda`: UNSOUND as written; F1 the member names bound to `Γ.au`, F2 the lessor name `Γ.ls mid` tied by Serve), then `f7-rerev-c.md` (`6d9d9fd662`): SOUND given the proposed Serve, adopted as `Serve_dist` (`f7-combined.md`, F7 step 3 `eb138f6f8c`). Since then a comment only (`f7-changed-since-review.md`). -/
abbrev Lease_TimeToLiveKeysOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) (n₀ m₀ : Nat)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (id : w64)
    (sl : GoSlice) (gs : List (Bool → Bool)),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  -- (F7 review C, 2026-11-26) the revocable mode, as `Lease_LeasesOn_dist`: Serve ties `Γ.ls mid` to the
  -- member's lessor at the view's mode `Γ.kv.lm` (`Serve_dist`)
  Γ.auth = true → Γ.kv.lm = .revocable → outTokOk (principalOf cfg) om → leaseKeysFold gs false = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseUserAt cl lp ep V Γ mid cfg ∗ metadata.outMD ctx om ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      leaseOptsAt sl gs ∗ auth.authPubLbM (.on (Γ.au mid)) n₀ ∗ lease.lessorLb (Γ.ls mid) m₀ }}
    (App (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ctx))) (Val #id)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ id ∗
          ∃ n j : Nat, ⌜n₀ ≤ n ∧ m₀ ≤ j⌝ ∗ auth.authPubLbM (.on (Γ.au mid)) n ∗ lease.lessorLb (Γ.ls mid) j ∗
            leaseCheckD (Γ.au mid) (principalOf cfg) n
              (fun info => leaseKeysVerdictFrom (.on (Γ.au mid)) n info (Γ.ls mid) j id .read)) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
