/- Lean-first (no Rocq counterpart).

`Check(cli, clients, ops, timeout)` (`examples/linkvtxn/linkvtxn.go`; linkv-txn stage G, as
`examples/linkv`'s): `lintest.Run` with the
model `Model()`, the closure `func(input any) any { return Apply(cli, input) }`, the generator
`Gen` and the clock `lintest.CounterClock()`. Over `New`'s client `cli` (`Apply.spec`'s
premises: `isNewClient`, `clientWriteOnce`: a write sent at most once, etcd's `Put`, `Range`,
`DeleteRange` and `Txn` registered
at its endpoint) and
the instance's invariant with the library state at the model's start (`linkvInv γ γr.kv`,
`linkvState γ (linkv.pInit TS)`, what `linkvInv_alloc` gives), under `Run`'s bounds on `clients` and `ops`
and `CounterClock`'s on the time receipts (`receiptBound GF ≤ 2^63`): the result is never
`Illegal`, and it is `Ok` if `timeout ≤ 0`.

Stated under the cache package's assumptions and `errors.As`'s target, as `Apply.spec`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev Check.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (γ : LinkvNames) (cl : Loc) (ep : GoString)
    (V : EtcdGrove.client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64)
    (clients ops dur : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  receiptBound GF ≤ 2 ^ 63 →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      context.isClosedchanInit ∗
      isNewClient cl [ep] V ∗ EtcdGrove.client.clientWriteOnce cl [ep] ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E γr cid mid) ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E γr cid mid) ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/DeleteRange" (EtcdGrove.client.etcdDeleteSpec E γr cid mid) ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E γr γr cid mid) ∗
      linkvInv γ γr.kv ∗ linkvState γ (linkv.pInit TS) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.Check))
      (Val #cl)) (Val #clients)) (Val #ops)) (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
