/-
`Main()` (`examples/putget/putget.go`; item 9, stage 2, 2026-10-18): one etcd member started in
process, a client connected to it, a `Put` of `k` with value `v`, a `Get` of `k`, and a panic
unless the `Get` returned `v`. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23790` (`netAddrFree`, which program start gives once: D19d), the main thread's token
(`Start` forks the server's goroutines) and `Main`'s named premises (`putget.premises`,
`Proof/github_com/mit_pdos/etcd_grove/examples/putget/Defs.lean`), `Main()` returns: it does not
panic, so the `Get` that returned `nil` returned the `Put`'s value (D18's monotone route,
`putGetInv`).

**The pure premises:** the member id and bootstrap log Go computes (`putget.BootFacts`); the
logic's thread bound and the time-receipt bounds (the adequacy theorem's choices: `threadBound GF ≤
2 ^ 31`, `receiptBound GF ≤ 2 ^ 48` and `≤ N + 1`); the named workload and effect premises of the
server's construction (`ckptEffectsOk`, `authRecordsFit`,
`apply.backendUnderQuota`); Go's method sets of the gRPC service values
(`v3rpc.ServerMethodSets`) and that `errors.As` takes `*rpctypes.EtcdError` as a target.
The two named Props `EofFromIoInit` and `ClosedchanFromContextInit` (`io.EOF` and `context`'s
`closedchan` from their packages' facts: false under the current Perennial pin, D19r). The proof
allocates the storage registry (D19r (B)); it is stated under the cache package's assumptions,
which the server's and the client's lemmas take (their files' section variables) although
`putget` does not import the cache.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (id : w64) (bootLog : List EntryM),
  BootFacts id bootLog →
  -- the two package facts Perennial's initializers do not keep yet (D19r: false under the
  -- current pin, made theorems by the proposed Perennial changes)
  EofFromIoInit (GF := GF) → ClosedchanFromContextInit (GF := GF) →
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.putget ∗
      netAddrFree (GF := GF) go!"127.0.0.1:23790" ∗ threadTok ∗ premises N id bootLog }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.putget.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end putget
end EtcdGrove
end Perennial
