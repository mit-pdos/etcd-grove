# `etcd_noOtherRefusal` (draft, 2026-10-29)

**Reviewed:** the draft axiom `etcd_noOtherRefusal` (not in the tree; the exact statement below), part 1 of
the split of `etcd_noRefusal` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NoRefusal.lean`) that
F-S2 route B proposes. Go: etcd's fork `goose-lean` at the pin of `etc/goose.py`, grpc v1.84.

    axiom etcd_noOtherRefusal (addr) (gs q p s : Loc) (lis) (E : apply.AEnv GF) (ρ) (ics sics) (svcs) (regs sregs) :
      (∀ x ∈ v3rpc.kvRegs q, x ∈ regs) →
      isServerReqM E.authOn s E ρ ∗ v3rpc.quotaKVServerAt q ⟨…kvServer.ty, #p⟩ s ∗
        grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
      grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ∗ ⌜noOtherRefusalAt addr⌝

`noOtherRefusalAt addr` (opaque): no status the server at `addr` sends for a KV call has a description among
the learner's refusal ("etcdserver: rpc not supported for learner") and the old balancer's two ("there is
no address available", "there is no connection available").

## Verdict

**Survives, under the same condition as `etcd_noRefusal`**: the model's member is a voter for its whole life.
No counterexample program was attempted: the axiom's conclusion is an opaque `Prop` read only by the grpc
attempt contract (a retry decision), so a panicking program would have to come through that contract; the
review is of the claim itself.

## Attacks tried

1. **An auth-on path producing one of the strings.** None. The learner refusal is
   `rpctypes.ErrGRPCNotSupportedForLearner`, returned only by the interceptors
   (`server/etcdserver/api/v3rpc/interceptor.go:54` unary, `:225` stream), under
   `s.IsMemberExist(s.MemberID()) && s.IsLearner() && !isRPCSupportedForLearner(req)`; nothing on the auth
   path (`AuthInfoFromCtx`, the apply's permission checks, `auth/store.go`) returns it. The balancer strings
   occur only in the client (`client/v3/retry.go:93`, `isSafeRetryMutableRPC`), in neither the server nor
   grpc v1.84. Dropping `E.authOn = false` adds no path.
2. **The member a learner with auth on.** The learner branch needs `IsLearner()`. Auth does not change
   membership handling: a conf change is applied the same in both modes, and etcd has no demotion of a voter
   to a learner (only `PromoteMember`, learner to voter). So the member is a learner only if it booted as
   one or a conf change re-added it as one; both are excluded only by the voter condition, which is not
   proved: the KV invariants' `entryShape`/`ccLogOk` say a conf change's id is 0 and its policy holds, and
   `IsLearner.spec` returns any boolean. As for `etcd_noRefusal` ("the voter fact rests on this axiom
   too"), the condition is part of the trust.
3. **A stream call.** The conclusion is about unary KV calls (`kvMethod`), which only the unary
   interceptor sees; the stream interceptor's learner branch concerns Watch/LeaseKeepAlive, not KV.

## Remarks

- `etcd_noRefusal`'s docstring and the draft's justification cite `srvCCPolicy`, which is no definition
  (only comments). The voter fact's actual support is the docstring's argument; fix the citation when the
  axiom is frozen (name the conf-change policy the invariants hold, `ccLogOk`, and say it does not exclude
  adding a learner).
- Not tried: a Go program; whether `ccLogOk`'s policy could be strengthened to prove the voter fact (that
  would remove the condition from the trust).
