/- Lean-first (no Rocq counterpart).

`Call(cli, input)` (linkvtxn.go): `call` on the input boxed as an `any`, its output boxed: the operation
of a client machine of `examples/lib/remote` (etcd-dist's kv, `examples/etcd/dist/kvremote`), with no
prophecy (the orchestrator's `remote.Do` makes it). `call.spec`, boxed: for an input `x` `Gen` may
return that decodes to `i`, with the update its kind takes (`callUpd`: a write's, fired at most once; a
read's read update, or none), the failed call's output (`errOut`), or a successful one at the state `σ`
the update fired at (`callRes`), which is the model's answer at `σ` when `σ` is good. The same premises
as `call.spec`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Calls
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.lib.txnwork

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Assumptions]

/-- See the file header. -/
abbrev Call.spec : Prop :=
  ∀ (cl : Loc) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (x : Input) (i : MI) (Q : KVState → IProp GF), decIn x = some i → GenIn x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl (ms.map client.SrvAt.addr) V ∗ client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
      ([∗list] sv ∈ ms, client.kvRegsAt sv) ∗
      ([∧list] sv ∈ ms, callUpd sv.γr.kv i Q)) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Call)) (Val #cl))
      (Val #(boxIn x)))
  {{ (v : GoInterface), RET #v; levelTok 0 ∗ (⌜v = boxOut errOut⌝ ∨
      ∃ (y : Output) (σ : KVState), callRes i Q σ ∗
        ⌜v = boxOut y ∧ y.Err' = false ∧ kvRevFits σ.rev ∧ (GoodKV σ → y = outAt i σ)⌝) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
