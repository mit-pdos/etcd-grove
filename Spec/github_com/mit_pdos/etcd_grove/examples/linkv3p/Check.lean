/- Lean-first (no Rocq counterpart).

`Check(clis, clients, ops, timeout)` (`examples/linkv3p/linkv3p.go`; the partition plan's S3a,
2026-10-20; over linkvtxn's workload since 2026-10-20, `notes/linkv3p-txn-plan.md`): `lintest.Run`
with linkvtxn's model `Model()`, the closure `func(input any) any { return Apply(clis, input) }`
(each operation through a random client of `clis`), linkvtxn's generator `Gen` and the clock
`lintest.CounterClock()`: linkvtxn's `Check` (`Spec/.../linkvtxn/Check.lean`, whose header explains
the triple) over a slice of clients. Over the read-only, non-empty slice with linkvtxn's
`Apply.spec`'s premises for each client (`clientOk`) and the library state at the model's start
(`linkvState γ (linkv.pInit TS)`, what linkvtxn's `linkvInv_alloc_boot` gives, the invariant
itself in each `clientOk`), under `Run`'s bounds on `clients` and `ops` and `CounterClock`'s on the
time receipts (`receiptBound GF ≤ 2^63`): the result is never `Illegal`, and it is `Ok` if
`timeout ≤ 0`.

Stated under the cache package's assumptions and `errors.As`'s target, as `Apply.spec`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev Check.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (γ : linkvtxn.LinkvNames) (cls : GoSlice)
    (clis : List Loc) (clients ops dur : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  receiptBound GF ≤ 2 ^ 63 → clis ≠ [] →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      context.isClosedchanInit ∗
      cls ↦*□ clis ∗ ([∗list] cl ∈ clis, clientOk γ cl) ∗
        linkvtxn.linkvState γ (linkv.pInit linkvtxn.TS) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.Check))
      (Val #cls)) (Val #clients)) (Val #ops)) (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end linkv3p
end EtcdGrove
end Perennial
