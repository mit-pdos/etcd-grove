/-
`run(s1, s2, s3, a1, a2, a3, lg)` (`examples/etcd/auth3/auth3.go`; the auth3 Scope's A2, 2026-11-14):
authkv's run (`auth.Run`) across the three members. Lean-first (no Rocq counterpart).

The steps: each member's gRPC API served (`Serve`, the thread token passed from member to member);
the set-up through member 1 (`auth.SetUp`); root's barrier read at each member (`barrier`: the auth
state fixed after the set-up at that member, `akAuthFixed`); the clients (root through member 1, u
through member 2, v through member 3, the client with no token through member 1, the one with the
invalid token through member 2); the four workloads (`auth.Work`, each at its member's names) in
goroutines; root's last write and the history's check through member 1; u's watch check through
member 2. Every error returns `Failed` (`1`), a watch that ends early `WatchEnded` (`2`).

**The triple:** from the three members started with auth on (`memberUpOn`, member 2's and 3's
without the thread token, which member 1's holds: putget3's start passes one token along), the
right to listen at each client address, the history invariant and the client's view of the auth
history at the start, both at member 1's KV names, and the members' names of one cluster
(`etcdstart.sameCluster`), `run` returns `0`, `1` or `2`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3On
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Base
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

/-- See the file header. -/
abbrev run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (s₁ s₂ s₃ lg : Loc) (a₁ a₂ a₃ : GoString) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
    (γn : NetNames GF) (id₁ id₂ id₃ : w64) (γa₁ γa₂ γa₃ : auth.AuthNames),
  plainEndpoint a₁ → plainEndpoint a₂ → plainEndpoint a₃ →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 →
  apply.backendUnderQuota → grpcRepliesFit → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ρ₁.rd.kv.c0 = W64 0 → ρ₁.rd.kv.log0 = [[], []] →
  etcdstart.sameCluster ρ₁ ρ₂ → etcdstart.sameCluster ρ₁ ρ₃ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth3 ∗
      zapLoggerOk lg ∗ netAddrFree a₁ ∗ netAddrFree a₂ ∗ netAddrFree a₃ ∗
      etcdstart.memberUpOn s₁ ρ₁ E₁ lg γn id₁ γa₁ ∗
      (threadTok -∗ etcdstart.memberUpOn s₂ ρ₂ E₂ lg γn id₂ γa₂) ∗
      (threadTok -∗ etcdstart.memberUpOn s₃ ρ₃ E₃ lg γn id₃ γa₃) ∗
      akHistInv ρ₁.rd.kv ∗ authHistView ρ₁.rd.kv [srvAuthSt0] }}
    (App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth3.run))
      (Val #s₁)) (Val #s₂)) (Val #s₃)) (Val #a₁)) (Val #a₂)) (Val #a₃)) (Val #lg))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end etcd_auth3
end EtcdGrove
end Perennial
