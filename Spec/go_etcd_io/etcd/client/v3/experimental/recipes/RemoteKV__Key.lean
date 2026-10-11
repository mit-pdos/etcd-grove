/-
`recipes.(*RemoteKV).Key()` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- `rk.Key()`: the record's `key`. -/
abbrev RemoteKV.Key.spec : Prop :=
  ∀ (rk : Loc) (st : RemoteKVSt),
  {{ ownRemoteKV (GF := GF) rk st }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Key")) (Val #()))
  {{ RET #st.key; ownRemoteKV rk st }}

end spec

end recipes
end EtcdGrove
end Perennial
