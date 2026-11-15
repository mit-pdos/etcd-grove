/-
## `(*bootstrappedBackend).Close()` (`bootstrap.go:139-169`)

**Users.** `NewServer`'s deferred cleanup on an error after `bootstrap` (`server.go:303-307`),
`bootstrap`'s own error paths (names only); down the chain `bootstrappedServer` →
`bootstrappedStorage` → `bootstrappedBackend` → `backend.Close`.

**Proof sketch.** The record's read-only path to the backend (`bootBackendAt`), then the backend's
`Close` (4a) with its whole open token (`beClosable`): the file at rest.

**Changes** (from `specs-ref`'s `bootstrappedBackend__Close.lean`, R-D1: `bOpen γ 1`): the backend's token by its
provisional name; the closed file given back (a closer gives back: PRINCIPLES).

**Margin.** A second `Close` panics in Go (`close(b.stopc)`): the token is taken once.

Changes: verify-round (server-boot's request, A8-provability F5): over 4a's backend (`beClosable`: `isBackend` with its whole open token; `Backend.beFile` after), not the provisional `ServerStorage.beOpen`/`Snap.beFile`.

Changes: verify-round (repair3-boot, the crash pass's request 2): the file comes back through the
caller's `Backend.beCloseUpd γb path Q` (4a's `Close` now fires it at the release: the history out of
the disk's state, the closed file in), so the post is `beFinal γb I ∗ Q I` (was `beFile path (some I)`,
with which a crash after the return had two crash laws, one of them false); `beClosable` names `γb`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api

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
  ∀ (b : Loc) (be : GoInterface) (path : GoString) (γb : Backend.BeNames)
    (Q : Backend.Image → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ bootBackendAt b be ∗ beClosable be path γb ∗
      Backend.beCloseUpd γb path Q }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.bootstrappedBackend.ty @!! go!"Close")) (Val #()))
  {{ RET #(); ∃ I : Backend.Image, Backend.beFinal γb I ∗ Q I }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
