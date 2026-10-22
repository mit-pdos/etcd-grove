/- Lean-first (no Rocq counterpart).

`Main(clients, ops)` (`examples/linkvtxn/linkvtxn.go`; linkv-txn stage G): one etcd member started
in process (as `examples/linkv`'s `Main`, on `linkvtxn`'s ports), a client with etcd's
default configuration (its default retries; D29), and `Check(cli, clients, ops, 0)`, with a panic if porcupine reports the
history `Illegal`.

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23796`, the main thread's token and `Main`'s named premises (`linkvtxn.premises`,
putget's at `linkvtxn`'s configuration, `Proof/.../linkvtxn/MainDefs.lean`), `Main(clients, ops)` does
not panic and returns `Ok` (the check ran: the history is linearizable) or `Unknown` (a step
before the check failed). The pure premises are putget's (`putget.Main.spec`: the member id and
bootstrap log, the thread and time-receipt bounds, the server's workload and effect premises,
gRPC's method sets, `errors.As`'s target, the method-set classes of `*errorString`) and `Run`'s bounds on
`clients` and `ops`. Stated under the cache package's assumptions, as putget's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.MainDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ErrorStringLeaf] [context.ErrorStringIsError]
    (N : Nat) (id : w64) (bootLog : List EntryM)
    (clients ops : w64),
  putget.BootFacts id bootLog →
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  mvcc.backendNoCompaction → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      netAddrFree (GF := GF) go!"127.0.0.1:23796" ∗ threadTok ∗ premises N id bootLog }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.Main)) (Val #clients))
      (Val #ops))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
