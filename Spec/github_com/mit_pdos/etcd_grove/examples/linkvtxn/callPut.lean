/- Lean-first (no Rocq counterpart).

`callPut(cli, key, val)` (linkvtxn.go): a put of `key ↦ val` through `New`'s client `cli`
that sends a write at most once, with an update fired at most once: the failed call's output
(`errOut`), or the reply's at the state `σ` the update fired at (`Q σ`): `σ`'s next revision.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev callPut.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (key val : GoString) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (linkv.putOp key val)) Q) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.callPut)) (Val #cl))
      (Val #key)) (Val #val))
  {{ (y : Output), RET #y; ⌜y = errOut⌝ ∨
      ∃ σ : KVState, Q σ ∗
        ⌜y = { zOut with Rev' := W64 ((σ.rev + 1 : Nat) : Int) } ∧ σ.rev + 4 < 2 ^ 63⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
