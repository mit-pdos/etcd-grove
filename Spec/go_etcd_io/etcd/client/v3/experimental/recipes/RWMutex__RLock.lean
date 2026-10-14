/-
`recipes.(*RWMutex).RLock()` (`client/v3/experimental/recipes/rwmutex.go`). Lean-first (no Rocq counterpart);
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

/-- **`rwm.RLock()`**, from any key, knowing etcd has reached `lo`: a fresh key under
`pfx/read/` (`newUniqueEphemeralKey(s, pfx + "read")`) in `myKey`, then `waitOnLastRev(pfx +
"write")` until done: `nil` means the key holds the mutex as a reader since some `R`
(`rwHeldAt pfx .read`: no key with the prefix `pfx/write` with a mod revision below the key's
creation at `R`); see `rwLockResult`. -/
abbrev RWMutex.RLock.spec : Prop :=
  ∀ (m s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (pfx : GoString)
    (o : Option (Loc × RemoteKVSt)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRWMutex m s γ client id pfx ∗ rwMyKey m pfx o ∗ etcdReached lo }}
    (App (Val (m @!! go.GoType.PointerType RWMutex.ty @!! go!"RLock")) (Val #()))
  {{ (err : GoInterface), RET #err; rwLockResult m pfx id .read lo err }}

end spec

end recipes
end EtcdGrove
end Perennial
