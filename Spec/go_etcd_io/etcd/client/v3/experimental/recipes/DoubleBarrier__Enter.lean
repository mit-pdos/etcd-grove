/-
`recipes.(*DoubleBarrier).Enter()` (`client/v3/experimental/recipes/double_barrier.go`). Lean-first (no Rocq
counterpart); see `InvDoubleBarrier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvDoubleBarrier

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

/-- **`b.Enter()`**, from any key, knowing etcd has reached `lo`: see `enterResult`. `nil` means a
fresh key under `key/waiters/` in `myKey` and `enterReady`: `count` waiters seen (the direct
path), or a write of `key/ready` at or after the key's creation (the waiting path); under the
protocol's premise both mean `count` waiters seen (`enterReady_counted`). -/
abbrev DoubleBarrier.Enter.spec : Prop :=
  ∀ (b s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (key : GoString)
    (count : w64) (o : Option (Loc × RemoteKVSt)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isDoubleBarrier b s γ client id key count ∗ dbMyKey b (key ++ go!"/") o ∗
      etcdReached lo }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"Enter")) (Val #()))
  {{ (err : GoInterface), RET #err; enterResult b key count id lo err }}

end spec

end recipes
end EtcdGrove
end Perennial
