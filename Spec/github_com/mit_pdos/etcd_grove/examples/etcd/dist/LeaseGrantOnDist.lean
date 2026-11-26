/-
`(*lessor).Grant(ctx, ttl)` at member `mid`, auth on, revocable mode, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/LeaseGrantOnDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
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

/-- **`Lease_GrantOn_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, auth on, revocable
mode** (mirrors `client.client_lease_grant_on` at `γl := Γ.ls mid`, in F2's `Lease_GrantLive_dist`
statement: the grant's update persistent at every id (`□ ∀ id`, `writeAuD`), its result `Q m.id σ`; the
member's own check (`requireAuthInfo`'s, `leaseCheckD … True`) at its published index at least the
caller's `n₀`).

**Strengthened before approval** (F7 S5, 2026-11-26, the lead's approval #50 06:35Z; needs a fresh review): `leaseCheckD`'s binding is `P = some info.Username'` (`requireAuthInfo`'s condition: a nil `AuthInfo` is refused with auth on), no longer `userOk P`, which admitted the empty user and so made the check vacuous for an anonymous principal (`f7-c.md`).

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/LeaseGrantOnDist.lean`). Reviews (`notes/axiom-review/`): `f7-c.md` (`d946f6cbda`: NEEDS-FIX; F1 the member names bound to `Γ.au`, F2 the lessor name `Γ.ls mid` tied by Serve), then `f7-rerev-c.md` (`6d9d9fd662`): SOUND given the proposed Serve, adopted as `Serve_dist` (`f7-combined.md`, F7 step 3 `eb138f6f8c`). Unchanged since (`f7-changed-since-review.md`). -/
abbrev Lease_GrantOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel) (n₀ : Nat)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (ttl : w64)
    (Q : w64 → KVState → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseUserAt cl lp ep V Γ mid cfg ∗ metadata.outMD ctx om ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      srvReqLogLb γR L₀ ∗ auth.authPubLbM (.on (Γ.au mid)) n₀ ∗
      □ (∀ id : w64, writeAuD Γ.kv (principalOf cfg) (.leaseGrant id ttl) L₀ (Q id)) }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ (∃ (i : Nat) (l : Loc),
          lease.leaseLiveFrom (Γ.ls mid) i m.id l ∗ lease.leaseReqIs (Γ.ls mid) m.id ttl) ∗
        (∃ σ : KVState, Q m.id σ) ∗
        ∃ n : Nat, ⌜n₀ ≤ n⌝ ∗ auth.authPubLbM (.on (Γ.au mid)) n ∗
          leaseCheckD (Γ.au mid) (principalOf cfg) n (fun _ => iprop(True))) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
