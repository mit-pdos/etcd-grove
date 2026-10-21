/- Lean-first (no Rocq counterpart).

`callDel(cli, key)` (linkvtxn.go): a delete of `key` through `New`'s client `cli` configured
for one attempt, with an update fired at most once: the failed call's output (`errOut`), or the
reply's (`delOut`) at the state `σ` the update fired at (`Q σ`): the state's revision after the
delete, and the number of keys it deleted.
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
abbrev callDel.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (key : GoString) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl (ms.map client.SrvAt.addr) V ∗
      clientKVOnce cl (ms.map client.SrvAt.addr) ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.deleteRange (linkv.delOp key)) Q) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.callDel)) (Val #cl))
      (Val #key))
  {{ (y : Output), RET #y; ⌜y = errOut⌝ ∨
      ∃ σ : KVState, Q σ ∗
        ⌜y = delOut (W64 ((kvOpStep (.deleteRange (linkv.delOp key)) σ).rev : Int))
            (W64 ((rangeIn σ.kvs (linkv.delOp key)).length : Int)) ∧ σ.rev + 4 < 2 ^ 63⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
