/- Lean-first (no Rocq counterpart).

`call(cli, in)` (linkvtxn.go): one operation through `New`'s client `cli` (configured for one
attempt), for an input `x` `Gen` may return (`GenIn`) that decodes to `i`, with the update its
kind takes (`callUpd`: a write's, fired at most once; a read's read update, or none): the
failed call's output (`errOut`), or a successful one at the state `σ` the update fired at
(`callRes`), below `2 ^ 63`, which is the model's answer at `σ` (`outAt i σ`) when `σ` is good.

Premises: what `New` returns (`isNewClient`, `clientKVOnce`), the server's `Put`, `Range`,
`DeleteRange` and `Txn` registered with etcd's specs at the client's endpoint (`etcd_kv_served`,
at one read names `γr`), the packages' facts, and `errors.As`'s target (the client's context
lemma). Stated under the cache package's assumptions, which the client's lemmas take.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev call.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (x : Input) (i : MI) (Q : KVState → IProp GF), decIn x = some i → GenIn x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗ client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
      ([∗list] sv ∈ ms, client.kvRegsAt sv) ∗
      ([∧list] sv ∈ ms, callUpd sv.γr.kv i Q) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.call)) (Val #cl))
      (Val #x))
  {{ (y : Output), RET #y; ⌜y = errOut⌝ ∨
      ∃ σ : KVState, callRes i Q σ ∗
        ⌜y.Err' = false ∧ σ.rev + 3 < 2 ^ 63 ∧ (GoodKV σ → y = outAt i σ)⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
