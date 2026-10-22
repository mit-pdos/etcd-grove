/- Lean-first (no Rocq counterpart).

`Apply(cli, input)` (`examples/linkvtxn/linkvtxn.go`): one operation through `New`'s client
`cli`, logically atomic against the instance's model (`linkvtxnS`: `pM TS decOp`), in the form
`lintest`'s `applySpec` (`Proof/.../lintest/Defs.lean`) takes for the closure `Check` passes,
`func(input any) any { return Apply(cli, input) }`:

  `{{ linkvInOk i }} <<{ ∀∀ S, linkvState γ S }>> Apply(cli, i) @@ linkvE
     <<{ ∃∃ S' o, linkvState γ S' ∗ ⌜linkvtxnS.M.step S (i, o) = some S'⌝ }>>
     {{ RET #o; ioOk i o }}`

over the library's state `linkvState γ S` (the history's ghost variable, whose other half is in
the instance's invariant `linkvInv γ γr.kv` with the server's `etcdKV`: `Proof/.../linkvtxn/Inv.lean`).
The mask `linkvE` is the server's invariants open where it fires a client's update and the
instance's. The input is one `Gen` may return (`linkvInOk`: `GenIn`, its transactions not empty).

Premises: what `New` returns for a client of the members `ms` (at least one; several since
2026-10-21, failover, `notes/decisions.md` D27) configured with `MaxUnaryRetries: 1`
(`isNewClient`, `clientWriteOnce`: a write sent at most once), each member's `Put`, `Range`, `DeleteRange` and `Txn` registered
with etcd's specs at its endpoint (`client.kvRegsAt`: `etcd_kv_served`'s, at the member's apply
environment, read names and ids), the instance's invariant at each member's KV names, the packages'
facts, and `errors.As`'s target (the client's context lemma). Stated
under the cache package's assumptions, which the client's lemmas take.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

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
abbrev Apply.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (γ : LinkvNames) (cl : Loc)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → ms ≠ [] →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn -∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 -∗
    isNewClient cl (ms.map client.SrvAt.addr) V -∗ client.clientWriteOnce cl (ms.map client.SrvAt.addr) -∗
    ([∗list] sv ∈ ms, client.kvRegsAt sv) -∗
    ([∗list] sv ∈ ms, linkvInv γ sv.γr.kv) -∗
    iprop(∀ i : GoInterface,
      {{ linkvInOk i }} <<{ ∀∀ S, linkvState γ S }>>
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.Apply)) (Val #cl))
          (Val #i)) @@ linkvE
      <<{ ∃∃ S' o, linkvState γ S' ∗ ⌜(linkvtxnS (GF := GF)).M.step S (i, o) = some S'⌝ }>>
      {{ RET #o; linkvtxnS.ioOk i o }})

end spec

end linkvtxn
end EtcdGrove
end Perennial
