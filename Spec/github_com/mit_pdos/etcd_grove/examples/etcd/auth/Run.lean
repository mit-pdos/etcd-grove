/- Lean-first (no Rocq counterpart).

`Run(s, addr, lg)` (`examples/etcd/auth/authkv.go`; the auth3 Scope's Q6, `notes/auth3-scope.md`):
`Main()` after the member's start, shared with `examples/etcd/auth3`, which runs it on its first
member: `s`'s gRPC API served at `addr` (`etcdstart.Serve`), a client of `addr` with no user name
that sets up the auth state and enables auth (`SetUp`), clients of `addr` that authenticate as root,
`u` and `v`, the four principals' workloads at once (`Work`), root's last write `z/end`, root's watch
of every key from revision `1` and the history's check (`CheckHistory`), and `u`'s watch of `[a, b)`.

**The triple:** from the member started with auth on at the auth names `γa` (`memberUpOn`, what
`startServer`'s and auth3's `startMember`'s posts give), the right to listen on `addr`, the history
invariant over the member's KV names (`akHistInv`: every state the cluster's KV state takes is
admitted by the history's check) and the client's view of the auth history at the start
(`authHistView … [srvAuthSt0]`), `Run` does not panic and returns `Ok`, `Failed` or `WatchEnded`
(`Main.spec`'s post; see its header for what not panicking means). The member's KV names start at
the first consistent index `0` and the start log `[[], []]` (`alloc`'s, the boot state's).

**The pure premises:** `Main.spec`'s that `Main`'s proof uses after the start, and `addr` a plain
`host:port` (`plainEndpoint`, `clientv3.New`'s premise).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.ClientAuth
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (s lg : Loc) (addr : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames),
  plainEndpoint addr →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 →
  apply.backendUnderQuota → grpcRepliesFit → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ρ.rd.kv.c0 = W64 0 → ρ.rd.kv.log0 = [[], []] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth ∗
      zapLoggerOk lg ∗ netAddrFree addr ∗ etcdstart.memberUpOn s ρ E₀ lg γn id γa ∗
      akHistInv ρ.rd.kv ∗ authHistView ρ.rd.kv [srvAuthSt0] }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth.Run))
      (Val #s)) (Val #addr)) (Val #lg))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
