/-
`recipes.(*RWMutex).Unlock()` (`client/v3/experimental/recipes/rwmutex.go`). Lean-first (no Rocq counterpart);
see `InvRWMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRWMutex

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

/-- **`rwm.Unlock()`**: `rwm.myKey.Delete()` (a key must be in `myKey`: a nil `myKey` is a nil
dereference), knowing etcd has reached `lo`: see `rwUnlockResult` (the key absent at some
revision at least `lo`, or an error; `nil` if it was deleted already); the key's `KV` becomes nil. -/
abbrev RWMutex.Unlock.spec : Prop :=
  ∀ (m : Loc) (pfx : GoString) (ek : Loc) (st : RemoteKVSt) (lo : w64),
  {{ rwMyKey (GF := GF) m pfx (some (ek, st)) ∗ etcdReached lo }}
    (App (Val (m @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #()))
  {{ (err : GoInterface), RET #err;
      rwMyKey m pfx (some (ek, { st with kv := GoInterface.nil })) ∗ rwUnlockResult pfx st lo err }}

end spec

end recipes
end EtcdGrove
end Perennial
