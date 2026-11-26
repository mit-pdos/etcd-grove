/-
`(*lessor).TimeToLive(ctx, id, opts...)` at member `mid`, auth on, with or without `WithAttachedKeys()`, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/LeaseTimeToLiveOnDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
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

/-- **`Lease_TimeToLiveOn_dist`: `(*lessor).TimeToLive(ctx, id, opts...)` at member `mid`, auth on, with
or without attached keys** (F2's `Lease_TimeToLiveKeys_dist` row; mirrors `lessor.TimeToLive.spec` at
`etcdLeaseTTLSpecMdW`, any options: `checkLeaseTimeToLive` runs at the member that
received the call, over its own auth store and its own lessor (`s.lessor.Lookup`), before the TTL itself
is asked of the leader. So the success is the echoed `ID` (F2's view-free claim: nothing of the TTL, which
the leader answers) and member `mid`'s keys verdict (`leaseKeysVerdictFrom`: the lease absent, or each
attached key readable) at its published auth index `n ≥ n₀` and its lessor's index `j ≥ m₀`; or the
member's admin pass). Without attached keys (`leaseKeysFold gs false = false`, `r.Keys` false) the check
is `requireAuthInfo`'s alone (`v3_server.go:700`, run whatever `r.Keys`): with auth on, the context's
`AuthInfo` is non-nil, so it came from a token the member accepted, which (`outTokOk`: the caller adds no
issued token of its own, `cfg.Token' = []`) is the one `New` obtained for `cfg`'s user: the info's user is
the principal (`principalOf cfg = some info.Username'`). This is `etcdLeaseTTLSpecMdW`'s `else`
(`True` under `principalBound`, which binds the info to the token) with the token's binding stated as the
principal, as `userOk` does for the keys arm; `userOk` alone would admit the empty user, which
`requireAuthInfo` refuses (`ErrUserEmpty`). So an anonymous or invalid-token caller is refused.

**Generalized before approval** (2026-11-26, the lead's choice (a), F7 S4): until then
`Lease_TimeToLiveKeysOn_dist`, which required `leaseKeysFold gs false = true` and named only the keys arm;
now any options, the refusal (error) arm unchanged. Needs a fresh review. **Reviewed** `f7-getOn-n1.md` (2026-11-26): SOUND as drafted. It must keep claiming nothing about
`TTL` or `GrantedTTL` (a `ttl = -1` claim would be false for an expired, not yet revoked lease); of `Keys` only
the fork's readability claim below.

**Strengthened before approval** (F7 S5, 2026-11-26, the lead's approval #50 06:35Z; needs a fresh review): `leaseCheckD`'s binding is `P = some info.Username'` (`requireAuthInfo`'s condition), no longer `userOk P`; the no-keys arm's `principalOf cfg = some info.Username'` is now implied by it (kept, redundant).

**The reply's keys** (F7 fork, 2026-11-26, SPECULATIVE: branch `etcd-safe-f7-fork/2026-11-26` only, approved there by
the lead and the coordinator, pending Upamanyu's decision; review `notes/axiom-review/f7fork-ttl-dist-keys.md`):
with attached keys, the reply's `Keys` (`ks`, read-only: the client's `LeaseTimeToLiveResponse` holds the decoded
`pb` response's slice, `lease.go:257`, which protobuf-go decodes into fresh copies, `consumeBytesSlice`) are the
byte lists `kss`, each readable (`IsRangePermitted(k, [])`) by the caller's principal at member `mid`'s applied
auth state at an index `≥ n` (`n ≥ n₀` its published index, as the keys verdict above), or the principal an
admin there, or auth disabled there (`leaseCheckD`, its own `info`: the re-check calls `AuthInfoFromCtx` again).
Why it is true of the fork `d26dd5da6` only: `LeaseTimeToLive` checks the keys it returns
(`checkLeaseTimeToLiveKeys`, `v3_server.go:719-725, 733-757`) after `leaseTimeToLive`'s lookup on the leader or the
forwarded reply, over the receiving member's auth store, and returns the checked `resp` unchanged; proved in-process
as `EtcdServer.LeaseTimeToLive.spec`'s keys conjunct. At the pin `df6af0c36a` it is false
(`notes/etcd-dist-f7-bprime.md` on branch `etcd-safe-f7-bprime`: a follower applying a snapshot answered keys
the user may not read). A grant revoked at the leader but not yet applied at `mid` still passes: the claim is
relative to `mid`'s auth state, as the reads' `authFloorD`.

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/LeaseTimeToLiveOnDist.lean`). Reviews (`notes/axiom-review/`): `f7-c.md` (`d946f6cbda`: UNSOUND as written; F1 the member names bound to `Γ.au`, F2 the lessor name `Γ.ls mid` tied by Serve), then `f7-rerev-c.md` (`6d9d9fd662`): SOUND given the proposed Serve, adopted as `Serve_dist` (`f7-combined.md`, F7 step 3 `eb138f6f8c`). Since then a comment only (`f7-changed-since-review.md`). -/
abbrev Lease_TimeToLiveOn_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) (n₀ m₀ : Nat)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (id : w64)
    (sl : GoSlice) (gs : List (Bool → Bool)),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  -- (F7 review C, 2026-11-26) the revocable mode, as `Lease_LeasesOn_dist`: Serve ties `Γ.ls mid` to the
  -- member's lessor at the view's mode `Γ.kv.lm` (`Serve_dist`)
  Γ.auth = true → Γ.kv.lm = .revocable → outTokOk (principalOf cfg) om →
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
              (fun info => if leaseKeysFold gs false then
                  leaseKeysVerdictFrom (.on (Γ.au mid)) n info (Γ.ls mid) j id .read
                else iprop(⌜principalOf cfg = some info.Username'⌝)) ∗
            (if leaseKeysFold gs false then
              iprop(∃ (ks : GoSlice) (kbs : List GoSlice) (kss : List (List w8)),
                structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"Keys" resp ↦□ ks ∗
                ks ↦*□ kbs ∗ ([∗list] kb;k ∈ kbs;kss, kb ↦*□ k) ∗
                leaseCheckD (Γ.au mid) (principalOf cfg) n
                  (fun info => [∗list] k ∈ kss,
                    auth.permVerdictFrom (.on (Γ.au mid)) n info k [] .read GoInterface.nil))
             else iprop(True))) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
