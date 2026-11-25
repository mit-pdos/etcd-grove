/-
`run(srvs, ms, lg)` (`examples/etcd/leaseexpiryN/leaseexpiryN.go`; `notes/leaseN-plan.md`, 2026-11-16):
every started member's gRPC API served at its client address, a lease granted through a client of each
member, then, member by member, the member's listing polled until it no longer lists the lease granted
through it (`gone`) and listed once more, with a panic if that listing has the lease. Lean-first (no
Rocq counterpart).

**The triple:** leaseN's `run.spec` at the revocable lease mode: the servers' slice `ss` and the
members' slice `xs.map (·.1)` (`xs` pairing each member with its ghost names, as `StartMembers`' post),
the thread token and each member's `memberUp` given it (`StartMembers`' post, at the lease mode
`revocable`), each member's KV names at that mode, the right to listen at each client address (a plain
endpoint), and the deployment premise `leasePeersOk`: `run` returns `Checked` (`0`) or `Failed` (`1`);
it does not panic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Base
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiryN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]

/-- See the file header. -/
abbrev run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (srvsl msl : GoSlice) (lg : Loc) (ss : List Loc) (xs : List (GMember × MemberG GF))
    (γn : NetNames GF),
  xs.length ≤ 1000 →
  (∀ x ∈ xs, plainEndpoint x.1.Client') → (∀ x ∈ xs, x.2.ρ.rd.kv.lm = .revocable) →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 →
  apply.backendUnderQuota → grpcRepliesFit → leasePeersOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN ∗
      zapLoggerOk lg ∗ srvsl ↦* ss ∗ msl ↦*□ xs.map (·.1) ∗ threadTok ∗
      ([∗list] x ∈ xs, netAddrFree x.1.Client') ∗
      ([∗list] s; x ∈ ss; xs, (threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id .revocable)) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.run))
      (Val #srvsl)) (Val #msl)) (Val #lg))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1⌝ }}

end spec

end etcd_leaseexpiryN
end EtcdGrove
end Perennial
