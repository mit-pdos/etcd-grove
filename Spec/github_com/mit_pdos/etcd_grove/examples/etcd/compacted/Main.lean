/-
**`putgetc`** (M2, 2026-10-27, `notes/m2-plan.md`): putget's file, for putget with the
auto-compactor on (`etcdstart.StartCompactingServer`, revision mode, retention 1); putget's history
below is the original's.

`Main()` (`examples/etcd/compacted/etcd_compacted.go`; item 9, stage 2, 2026-10-18): one etcd member started in
process, a client connected to it, a `Put` of `k` with value `v`, a `Get` of `k`, and a panic
unless the `Get` returned `v`. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23791` (`netAddrFree`, which program start gives once: D19d), the main thread's token
(`Start` forks the server's goroutines) and `Main`'s named premises (`etcd_compacted.premises`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/compacted/Defs.lean`), `Main()` returns: it does not
panic, so the `Get` that returned `nil` returned the `Put`'s value (D18's monotone route,
`putGetInv`).

**The pure premises:** the member id and bootstrap log Go computes (`etcd_compacted.BootFacts`); the
logic's thread bound and the time-receipt bounds (the adequacy theorem's choices: `threadBound GF ≤
2 ^ 28`, `receiptBound GF ≤ 2 ^ 48` and `≤ N + 1`); the named workload and effect premises of the
server's construction (`ckptEffectsOk`, `authRecordsFit`,
`apply.backendUnderQuota`, `grpcRepliesFit`, `storage.diskOk`); Go's method sets of the gRPC service values
(`v3rpc.ServerMethodSets`) and that `errors.As` takes `*rpctypes.EtcdError` as a target (both
discharged by the adequacy theorem, from the package assumptions).
The method-set facts of `*errorString` (`ErrorStringLeaf`, theorems of the package assumptions),
which make `io.EOF`'s package fact the server's `eofVar` (`v3rpc.eofVar_of_init`; until 2026-10-20, when Perennial's `io`
and `context` facts did not keep `EOF`'s value and `closedchan`'s invariant, the two named Props
`EofFromIoInit` and `ClosedchanFromContextInit` stood here). The proof
allocates the storage registry (D19r (B)); it is stated under the cache package's assumptions,
which the server's and the client's lemmas take (their files' section variables) although
`putgetc` does not import the cache.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compacted.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_compacted

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.compacted.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry),
  BootFacts id ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the server's gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.compacted ∗
      -- (2026-11-05, hub step 7) the member's start bundle: its WAL directory fresh and the right
      -- to listen on its client address (`netAddrFree`, which program start gives once: D19d)
      etcdstart.memberStartRes (GF := GF) go!"putgetc" ⟨none, some go!"127.0.0.1:23791"⟩ ∗
      threadTok ∗ premises N id ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.compacted.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_compacted
end EtcdGrove
end Perennial
