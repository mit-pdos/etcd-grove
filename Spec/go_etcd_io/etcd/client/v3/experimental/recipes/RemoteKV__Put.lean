/-
`recipes.(*RemoteKV).Put(val)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
see `InvRecipesClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`rk.Put(val)`**, for a `RemoteKV` with a `KV` (the code dereferences it: after `Delete`
it is nil, a misuse ruled out here), knowing etcd has reached `lo`: `kv.Put(context.TODO(),
key, val)` (no lease: etcd detaches the key from any lease), returning its `putResult`. The
record is unchanged (the code does not update its `val`). -/
abbrev RemoteKV.Put.spec : Prop :=
  ∀ (rk : Loc) (st : RemoteKVSt) (kv : GoInterfaceOk) (pfx val : GoString) (lo : w64),
  {{ ownRemoteKV (GF := GF) rk st ∗ ⌜st.kv = GoInterface.ok kv⌝ ∗ isRecipesKV st.kv pfx ∗
      etcdReached lo ∗ ⌜pfx <+: st.key⌝ }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Put")) (Val #val))
  {{ (err : GoInterface), RET #err; ownRemoteKV rk st ∗
      putResult pfx lo (.put st.key val (W64 0)) err }}

end spec

end recipes
end EtcdGrove
end Perennial
