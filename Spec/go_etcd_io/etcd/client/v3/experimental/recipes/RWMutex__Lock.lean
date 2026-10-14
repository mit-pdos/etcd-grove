/-
`recipes.(*RWMutex).Lock()` (`client/v3/experimental/recipes/rwmutex.go`). Lean-first (no Rocq counterpart);
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

/-- **`rwm.Lock()`**, from any key, knowing etcd has reached `lo`: a fresh key under `pfx/write/`
(`newUniqueEphemeralKey(s, pfx + "write")`) in `myKey`, then `waitOnLastRev(pfx)` until done:
`nil` means the key holds the mutex as a writer since some `R` (`rwHeldAt pfx .write`: no key
under `pfx` with a mod revision below the key's creation at `R`); see `rwLockResult`. -/
abbrev RWMutex.Lock.spec : Prop :=
  ∀ (m s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (pfx : GoString)
    (o : Option (Loc × RemoteKVSt)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRWMutex m s γ client id pfx ∗ rwMyKey m pfx o ∗ etcdReached lo }}
    (App (Val (m @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #()))
  {{ (err : GoInterface), RET #err; rwLockResult m pfx id .write lo err }}

end spec

end recipes
end EtcdGrove
end Perennial
