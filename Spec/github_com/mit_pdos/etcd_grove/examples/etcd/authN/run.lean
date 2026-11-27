/-
`run(srvs, ms, lg)` (`examples/etcd/authN/authN.go`; authN, `notes/authN-plan.md`, 2026-11-15): auth3's
`run` on the `k ≥ 1` started members. Lean-first (no Rocq counterpart).

The steps: each member's gRPC API served (`Serve`, the thread token passed from member to member);
the set-up through member `0` (`auth.SetUp`); root's barrier read at each member (`barrier`: the auth
state fixed after the set-up at that member, `akAuthFixed`); the clients (root and the client with no
token through member `0`, u and the client with the invalid token through member `1 mod k`, v through
member `2 mod k`); the four workloads (`auth.Work`, each at its member's names) in goroutines; root's
last write and the history's check through member `0`; u's watch check through u's member. Every error
returns `Failed` (`1`), a watch that ends early `WatchEnded` (`2`).

**The triple:** auth3's `run.spec` for a list of members: the servers' slice `ss` and the members'
slice `xs.map (·.1)` (`xs` pairing each member with its ghost names, as `StartMembersAuth`'s post,
`x0` the first), the thread token and each member's `memberUpOn` given it (`StartMembersAuth`'s post),
the right to listen at each client address (a plain endpoint), every member's names the cluster's as
member `0`'s (`etcdstart.sameCluster`), member `0`'s KV names at the start (`c0 = 0`, `log0`), and the
history invariant and the client's view of the auth history at the start, both at member `0`'s KV
names: `run` returns `0`, `1` or `2`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersAuthDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3On
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Base
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

/-- See the file header. -/
abbrev run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (srvsl msl : GoSlice) (lg : Loc) (ss : List Loc) (xs : List (GMember × MemberG GF))
    (x0 : GMember × MemberG GF) (γn : NetNames GF),
  xs[0]? = some x0 → xs.length ≤ 1000 → (∀ x ∈ xs, plainEndpoint x.1.Client') →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 →
  apply.backendUnderQuota → grpcRepliesFit → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  x0.2.ρ.rd.kv.c0 = W64 0 → x0.2.ρ.rd.kv.log0 = [[], []] →
  (∀ x ∈ xs, etcdstart.sameCluster x0.2.ρ x.2.ρ) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authN ∗
      zapLoggerOk lg ∗ srvsl ↦* ss ∗ msl ↦*□ xs.map (·.1) ∗ threadTok ∗
      ([∗list] x ∈ xs, netAddrFree x.1.Client') ∗
      ([∗list] s; x ∈ ss; xs,
        (threadTok -∗ ∃ γa : auth.AuthNames, etcdstart.memberUpOn s x.2.ρ x.2.E lg γn x.2.id γa)) ∗
      akHistInv x0.2.ρ.rd.kv ∗ authHistView x0.2.ρ.rd.kv [srvAuthSt0] }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authN.run))
      (Val #srvsl)) (Val #msl)) (Val #lg))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end etcd_authN
end EtcdGrove
end Perennial
