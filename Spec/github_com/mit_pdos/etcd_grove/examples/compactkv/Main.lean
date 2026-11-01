/-
**`compactkv`** (the client's `kv.Compact`, 2026-11-01): putgetc's file, for putgetc under
compaction pressure (`common.StartCompactingServer`, revision mode, retention 1; rounds of a put of
the round's key, a client compaction at the revision before it, a get of the key); putgetc's and
putget's history below is the originals'.

`Main()` (`examples/compactkv/compactkv.go`; item 9, stage 2, 2026-10-18): one etcd member started in
process with the auto-compactor on, a client connected to it, and five rounds of a `Put` of the
round's key with value `v`, a `Compact` at the revision before the put's and a `Get` of the key,
each with a panic unless the `Get` returned `v`. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23794` (`netAddrFree`, which program start gives once: D19d), the main thread's token
(`Start` forks the server's goroutines) and `Main`'s named premises (`compactkv.premises`,
`Proof/github_com/mit_pdos/etcd_grove/examples/compactkv/Defs.lean`), `Main()` returns: it does not
panic, so each round's `Get` that returned `nil` returned its `Put`'s value (D18's monotone
route, over the rounds: `compactkv.roundsInv`).

**The pure premises:** the member id and bootstrap log Go computes (`compactkv.BootFacts`); the
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
`compactkv` does not import the cache.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace compactkv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry),
  BootFacts id ctxs boot →
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.compactkv ∗
      netAddrFree (GF := GF) go!"127.0.0.1:23794" ∗ threadTok ∗ premises N id ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.compactkv.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end compactkv
end EtcdGrove
end Perennial
