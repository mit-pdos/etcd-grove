/-
## `(*bootstrappedBackend).Close()` (`bootstrap.go:139-169`)

**Users.** `NewServer`'s deferred cleanup on an error after `bootstrap` (`server.go:303-307`),
`bootstrap`'s own error paths (names only); down the chain `bootstrappedServer` →
`bootstrappedStorage` → `bootstrappedBackend` → `backend.Close`.

**Proof sketch.** The record's read-only path to the backend (`bootBackendAt`), then the backend's
`Close` (4a) with its whole open token (`ServerStorage.beOpen`): the file at rest.

**Changes** (from `specs-ref`'s `bootstrappedBackend__Close.lean`, R-D1: `bOpen γ 1`): the backend's token by its
provisional name; the closed file given back (a closer gives back: PRINCIPLES).

**Margin.** A second `Close` panics in Go (`close(b.stopc)`): the token is taken once.

Changes: verify-round (server-boot's request, A8-provability F5): over 4a's backend (`beClosable`: `isBackend` with its whole open token; `Backend.beFile` after), not the provisional `ServerStorage.beOpen`/`Snap.beFile`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Closes the bootstrapped backend** `bootstrappedBackend` reaches. -/
def bootstrappedBackend.Close.spec : Prop :=
  ∀ (b : Loc) (be : GoInterface) (path : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ bootBackendAt b be ∗ beClosable be path }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.bootstrappedBackend.ty @!! go!"Close")) (Val #()))
  {{ RET #(); ∃ I : Backend.Image, Backend.beFile path (some I) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
