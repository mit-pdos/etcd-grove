/- Lean-first (no Rocq counterpart).

`Apply(cli, input)` (`examples/linkv/linkv.go`; D20 (c)): one operation through `New`'s client
`cli`, logically atomic against the instance's model (`linkvS`: `kvM decOp`), in the form
`lintest`'s `applySpec` (`Proof/.../lintest/Defs.lean`) takes for the closure `Check` passes,
`func(input any) any { return Apply(cli, input) }`:

  `{{ linkvInOk i }} <<{ ∀∀ S, linkvState γ S }>> Apply(cli, i) @@ linkvE
     <<{ ∃∃ S' o, linkvState γ S' ∗ ⌜linkvS.M.step S (i, o) = some S'⌝ }>> {{ RET #o; ioOk i o }}`

over the library's state `linkvState γ S` (the history's ghost variable, whose other half is in the
instance's invariant `linkvInv γ γr.kv` with the server's `etcdKV`: `Proof/.../linkv/Inv.lean`).
The mask `linkvE` is the server's invariants open where it fires a client's update and the
instance's.

Premises: what `New` returns for a client that sends a write at most once (`isNewClient`,
`clientWriteOnce`: one attempt, or a refusal-free member, D29), the server's `Put` and `Range`
registered with etcd's specs at the client's
endpoint (`etcd_kv_served`), the instance's invariant, the packages' facts, and `errors.As`'s
target (`background_ctx`, the client's context lemma). Stated under the cache package's assumptions,
which the client's lemmas take (as `putget.Main.spec`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Inv
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev Apply.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (γ : LinkvNames) (cl : Loc) (ep : GoString)
    (V : EtcdGrove.client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv -∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 -∗
    isNewClient cl [ep] V -∗ EtcdGrove.client.clientWriteOnce cl [ep] -∗
    isGrpcRpc ep go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E γr cid mid) -∗
    isGrpcRpc ep go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E γr cid mid) -∗
    linkvInv γ γr.kv -∗
    iprop(∀ i : GoInterface,
      {{ linkvInOk i }} <<{ ∀∀ S, linkvState γ S }>>
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.Apply)) (Val #cl))
          (Val #i)) @@ linkvE
      <<{ ∃∃ S' o, linkvState γ S' ∗ ⌜(linkvS (GF := GF)).M.step S (i, o) = some S'⌝ }>>
      {{ RET #o; linkvS.ioOk i o }})

end spec

end linkv
end EtcdGrove
end Perennial
