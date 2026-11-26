/- Lean-first (no Rocq counterpart).

**DRAFT (etcd_safe S0, 2026-11-26; unreached, not reviewed).** `etcdstart.Serve` of a restarted member
incarnation on a member machine: a trust-boundary axiom until #24's S2, as `Serve_dist`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDistR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`etcdstart.Serve` of a restarted incarnation on a member machine** (DRAFT, trust boundary until #24's S2).

**Contract.** `Serve_dist`'s, for an incarnation after the first of member `mid` of an auth-off view `Γ` at the
lease mode `.none`, whose lessor is the incarnation's own (`memberUpL … .none γl`, any `γl`): `Serve` builds the
gRPC server, listens at `a`, serves etcd's table for `(Γ, mid)` on its own goroutine and returns, and no thread it
starts gets stuck or panics on the connections to `a`.

**Why it is true.** The argument is `Serve_dist.wp_proof`'s, for this incarnation's server (the in-process
`etcdstart.Serve.wp_proof` over the incarnation's `memberUp`, which `memberUpL_memberUp` gives), with two
differences, both about the restart:
* *The lessor name.* `Serve_dist` ties the member's lessor to `Γ.ls mid` because the lease client axioms read it
  (F2's P-L1). Every lease axiom requires `Γ.kv.lm = .mono` or `.revocable` (`LeaseGrantDist.lean`,
  `LeaseLeasesGrantedDist.lean`, `LeaseGrantLiveDist.lean`, `LeaseLeasesLiveDist.lean`) or auth on (the `*On`
  axioms), so at `Γ.kv.lm = .none` with `Γ.auth = false` no client axiom reads `Γ.ls mid` or `Γ.au mid`, and the
  served incarnation's own lessor suffices. Condition C of `Serve_dist` (auth on) is not involved.
* *The address after a crash.* A machine's crash, or its process's exit, drops its listeners
  (`GooseLang/Ext/Net/Impl.lean:810`, `crash`), so the new incarnation listens at `a` again; `etcdAddrAt a Γ mid`
  is persistent and global and survives. A connection dialed before the crash may be accepted by the new
  incarnation (Impl.lean:132); each call on it was deposited under `a`'s protocol at `(Γ, mid)`, whose spec is at
  the view's KV names, and every incarnation's KV names agree with them (`kvCongr ρ.rd.kv Γ.kv`, §18.3 of
  `notes/etcd-dist-plan.md`), so the new incarnation's handlers meet it.

**Retired by** S2's `etcdSvc` with `Serve_dist`, the restarted member's `memberUp` coming from `NewServer.specC`'s
post and `Start`.

**Route.** Translate: `etcdstart.Serve` is translated; the gRPC server across machines needs grpc over the net
extension (phase 7 S2/S3), not yet. Go model: the grpc model (`models/grpc`) is in-process only (S1). Trusted code:
none. Axiom: interim, as `Serve_dist`; alternatively `Serve_dist` restated with the lessor free at `.none` (one
fewer axiom, but a change to an approved axiom). -/
axiom Serve_distR.wp_proof : Serve_distR.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
