/- Lean-first (no Rocq counterpart).

`callGet(cli, key)` (etcd_txnlin.go): a get of `key` through `New`'s client `cli`, with a read
update or none: the failed call's output (`errOut`), or the reply's (`getOut`) at the state `σ`
the update fired at (`□ Q σ`): its revision and its key-values of `key`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Calls
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

/-- See the file header. -/
abbrev callGet.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (key : GoString) (Q : KVState → IProp GF), key.length ≤ inMax →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl (ms.map client.SrvAt.addr) V ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callGet)) (Val #cl))
      (Val #key))
  {{ (y : Output), RET #y; ⌜y = errOut⌝ ∨
      ∃ σ : KVState, □ Q σ ∗
        ⌜y = getOut (W64 (σ.rev : Int)) (σ.kvs.filter fun v => decide (v.key = key)) ∧
          kvRevFits σ.rev⌝ }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
