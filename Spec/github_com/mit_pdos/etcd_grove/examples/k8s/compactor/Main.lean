/-
`Main()` (`examples/k8s/compactor/compactor.go`; K4 of `notes/k8s-compactor-plan.md`): one etcd member
started in process in compaction mode with etcd's compactor off (`etcdstart.StartCompactingServer` at
retention `0`, member `k8scompactor`, peer address `127.0.0.1:23986`, client address
`127.0.0.1:23976`), served (`etcdstart.Serve`), a client that waits for the member to serve
(`ready`), a writer goroutine, and five API servers, each with its own client, three with their own
compactor (`NewCompactor`), two sharing the process's (`StartCompactorPerEndpoint`; Q1 (c), C3,
2026-11-05) (both loops: `ListFromCacheSnapshot` is on by default since Kubernetes 1.34; until Q1 (b),
2026-11-04, `Main` turned it off), which `Main` waits for.
Lean-first.

**The triple:** from the package's `isPkgInit`, the right to listen on the client address, the main
thread's token, the member's start premises (`etcdstart.premises`, one-member, at this
configuration), a fresh WAL directory and the compactor registry's claims' authority with no endpoint
claimed (`regAuth ∅`, which the adequacy theorem allocates), `Main` returns: no check of an API server panics and no
compactor round panics. The pure premises are the one-member examples' (`compactwatch`'s
`Main.spec`: the member id and bootstrap log, the thread and receipt bounds, the server's workload
and effect premises, gRPC's method sets, `errors.As`'s target). Stated under the cache package's
assumptions, with the context-error classes (`compactwatch`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Inv
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartCompactingServer
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The member's name. -/
abbrev memberName : GoString := go!"k8scompactor"
/-- The member's peer address. -/
abbrev peerAddr : GoString := go!"127.0.0.1:23986"
/-- The member's client address. -/
abbrev clientAddr : GoString := go!"127.0.0.1:23976"

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry),
  etcdstart.BootFacts id ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the server's gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      -- (2026-11-05, hub step 7) the member's start bundle: its WAL directory fresh and the right
      -- to listen on its client address
      etcdstart.memberStartRes (GF := GF) memberName ⟨none, some clientAddr⟩ ∗ threadTok ∗
      etcdstart.premises memberName peerAddr clientAddr N id ctxs boot ∗
      k8s.regAuth (∅ : GMap GoString GName) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
