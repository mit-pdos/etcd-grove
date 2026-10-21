/- Lean-first (no Rocq counterpart).

`callPut(cli, key, val)` (linkvtxn.go): a put of `key ↦ val` through `New`'s client `cli`
configured for one attempt, with an update fired at most once: the failed call's output
(`errOut`), or the reply's at the state `σ` the update fired at (`Q σ`): `σ`'s next revision.
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
abbrev callPut.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString) (V : client.WEnv GF)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (key val : GoString) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
      clientKVOnce cl [ep] ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E γr cid mid) ∗
      kvOpAu1 γr.kv (.put (linkv.putOp key val)) Q }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.callPut)) (Val #cl))
      (Val #key)) (Val #val))
  {{ (y : Output), RET #y; ⌜y = errOut⌝ ∨
      ∃ σ : KVState, Q σ ∗
        ⌜y = { zOut with Rev' := W64 ((σ.rev + 1 : Nat) : Int) } ∧ σ.rev + 4 < 2 ^ 63⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
