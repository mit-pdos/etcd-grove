/-
## `newTokenProviderNop()` (internal helper)

**Users.** `NewTokenProvider` (an empty kind).

**Proof sketch.** A fresh `tokenNop`: `info` never accepts, `assign` always fails (`ErrAuthFailed`), the rest do nothing; so it meets `tokenProviderAt` for every cluster, and never assigns a token (root tokens: no collision).

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary. Verify
round: at any gate `R` (no waiter).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`newTokenProviderNop()`**: a provider of any cluster's tokens (it accepts none). -/
def newTokenProviderNop.spec : Prop :=
  ∀ (γ : Cluster) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.newTokenProviderNop)) (Val #()))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); ⌜err = GoInterface.nil⌝ ∗
      tokenProviderAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenNop.ty) #p) γ R true }}

end spec
end Auth
end EtcdGrove
end Perennial
