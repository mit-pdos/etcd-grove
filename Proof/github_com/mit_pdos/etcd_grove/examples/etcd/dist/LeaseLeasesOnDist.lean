/-
`(*lessor).Leases(ctx)` at member `mid`, auth on, revocable mode, auth on, at the cluster view: an interim trust-boundary axiom (F7, `notes/etcd-dist-f7.md`;
`notes/etcd-dist-plan.md` §18.4). The real Go is translated; the cross-machine proof needs #24's S2 client side,
which retires it. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesOnDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **INTERIM: `Lease_LeasesOn_dist`** (`(*lessor).Leases(ctx)` at member `mid`, auth on, revocable mode; trust boundary until #24's S2 client side; the statement and its
mirror are in the spec's docstring). What it asserts of clientv3 v3.6, grpc-go v1.84 (the model) and an auth-on
etcd member over the net extension.

**Why it is an axiom** (the standing rule's order, as `KV_Put_dist`): the real Go is translated and in one
process its in-process counterpart (the spec's docstring names it) is proved over `Invoke`'s registration; across
machines the call goes through grpc's `Invoke` over the net extension, where no proof establishes the protocols of
any bytes and `etcdSvc` has no law. A Go model with the same behaviour is the grpc model itself (the same gap).

**Why it is true.** It is the in-process contract with the registration replaced by the address facts of the view
(`servedBy`/`etcdAddrAt`: a success is answered only by `Serve_dist` at the member named), the token's binding
replaced by the principal of the client's configuration (`principalOf`, `userOk`), member-local facts at the member's
own names `Γ.au mid`/`Γ.ls mid`, which `Serve_dist`'s auth-on premise (`memberUpOnL`) ties to the member's exclusive
resources, and an error arm that claims nothing (an invalid or expired token, a token another member has not yet
applied, a permission refusal, a timeout or partition all return `err ≠ nil`).

**Reviews** (`notes/axiom-review/`): `f7-c.md` (`d946f6cbda`: UNSOUND as written; F1 the member names bound to `Γ.au`, F2 the lessor name `Γ.ls mid` tied by Serve), then `f7-rerev-c.md` (`6d9d9fd662`): SOUND given the proposed Serve, adopted as `Serve_dist` (`f7-combined.md`, F7 step 3 `eb138f6f8c`). Unchanged since (`f7-changed-since-review.md`).

Retired by #24's S2 client side (`etcdSvc` defined, `Invoke` over the net model). The statement does not
change. -/
axiom Lease_LeasesOn_dist.wp_proof : Lease_LeasesOn_dist.spec (GF := GF) (hG := hG)

end proof

end authd
end etcd_dist
end EtcdGrove
end Perennial
