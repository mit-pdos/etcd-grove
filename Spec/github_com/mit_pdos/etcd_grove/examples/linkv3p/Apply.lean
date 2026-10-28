/- Lean-first (no Rocq counterpart).

`Apply(clis, input)` (`examples/linkv3p/linkv3p.go`; the partition plan's S3a, 2026-10-20): one
operation through a client of `clis` picked at random (`primitive.RandomUint64 % len(clis)`),
`linkvtxn.Apply(clis[i], input)` (linkv's `Apply` until 2026-10-20, `notes/linkv3p-txn-plan.md`).
Logically atomic against the instance's model as linkvtxn's `Apply` (`Spec/.../linkvtxn/Apply.lean`,
whose header explains the triple), in the form `lintest`'s `applySpec` takes for the closure
`Check` passes: the same triple, over the slice of clients (read-only, non-empty) with linkvtxn's
`Apply.spec`'s premises for each client (`clientOk`, `Defs.lean`: `New`'s client of some members'
endpoints, sending a write at most once, etcd's `Put`, `Range`, `DeleteRange` and `Txn` at each member's endpoint,
the instance's invariant at each member's KV names). Stated under the cache package's assumptions and `errors.As`'s target,
as linkvtxn's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls
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
abbrev Apply.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (γ : linkvtxn.LinkvNames) (cls : GoSlice)
    (clis : List Loc),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → clis ≠ [] →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p -∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn -∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 -∗
    cls ↦*□ clis -∗ ([∗list] cl ∈ clis, clientOk γ cl) -∗
    iprop(∀ i : GoInterface,
      {{ linkvtxn.linkvInOk i }} <<{ ∀∀ S, linkvtxn.linkvState γ S }>>
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.Apply)) (Val #cls))
          (Val #i)) @@ linkvtxn.linkvE
      <<{ ∃∃ S' o, linkvtxn.linkvState γ S' ∗
            ⌜(linkvtxn.linkvtxnS (GF := GF)).M.step S (i, o) = some S'⌝ }>>
      {{ RET #o; linkvtxn.linkvtxnS.ioOk i o }})

end spec

end linkv3p
end EtcdGrove
end Perennial
