/-
`run(srvs, ms, lg)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): authN's `run` on the
`k ≥ 1` started members, with the lease checks in place of authN's workloads. Lean-first (no Rocq
counterpart).

The steps: each member's gRPC API served (`Serve`; the member's Lease service with auth on registered,
`etcdstart.lease_served_on`); the set-up through member `0` (`auth.SetUp`); root's barrier read at each
member (`barriers`); the clients (root and the client with no token through member `0`, u and the
client with the invalid token through member `1 mod k`, v through member `2 mod k`); the leases (`Lz`
root's on `z/lease`, `Lu` u's on `a/lease` and, by a transaction, `a/txn`: `grantPut`, the cell's
invariant `Cell.lean`); the second barrier at each member; the checks (`noAuth`, u's refused leased
puts, `absent`, `foreign`, root's read of `z/lease`, u's revocation of `Lu` and the absences after it).
Every error returns `Failed` (`1`).

**The triple:** authN's `run.spec` in the revocable lease mode: every member started in it (`memberUpOn
… .revocable`, `StartMembersAuth`'s post at `.revocable`, its KV names in that mode), its cluster without
snapshots (`clusterNoSnap`, the lessor law's premise: Main allocates with `ns := true`), under the
deployment premise `leasePeersOk` (the member's lease reads, `lease_served_on`); in place of authN's
history invariant, the client's half of member `0`'s KV state (`etcdKV`) at a state without `a/x` (the
driver's cell, `Cell.lean`, is allocated over it): `run` returns `0` or `1`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersAuthDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3On
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Base
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- See the file header. -/
abbrev run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (srvsl msl : GoSlice) (lg : Loc) (ss : List Loc) (xs : List (GMember × MemberG GF))
    (x0 : GMember × MemberG GF) (γn : NetNames GF) (σ0 : KVState),
  xs[0]? = some x0 → xs.length ≤ 1000 → (∀ x ∈ xs, plainEndpoint x.1.Client') →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 →
  apply.backendUnderQuota → grpcRepliesFit → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  x0.2.ρ.rd.kv.c0 = W64 0 → x0.2.ρ.rd.kv.log0 = [[], []] →
  (∀ x ∈ xs, x.2.ρ.rd.kv.lm = .revocable) → leasePeersOk → clusterNoSnap x0.2.ρ.rd.raft.raft.cl →
  (∀ x ∈ xs, etcdstart.sameCluster x0.2.ρ x.2.ρ) → mvcc.findKey go!"a/x" σ0.kvs = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗
      zapLoggerOk lg ∗ srvsl ↦* ss ∗ msl ↦*□ xs.map (·.1) ∗ threadTok ∗
      ([∗list] x ∈ xs, netAddrFree x.1.Client') ∗
      ([∗list] s; x ∈ ss; xs,
        (threadTok -∗ ∃ γa : auth.AuthNames, etcdstart.memberUpOn s x.2.ρ x.2.E lg γn x.2.id γa .revocable)) ∗
      etcdKV x0.2.ρ.rd.kv σ0 ∗ authHistView x0.2.ρ.rd.kv [srvAuthSt0] }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.run))
      (Val #srvsl)) (Val #msl)) (Val #lg))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1⌝ }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
