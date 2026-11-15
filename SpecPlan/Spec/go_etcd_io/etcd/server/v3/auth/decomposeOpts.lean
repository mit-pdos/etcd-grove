/-
## `decomposeOpts(lg, optstr)` (internal helper)

**Users.** `NewTokenProvider`.

**Proof sketch.** `strings.Split(optstr, ",")` (never empty), its first element the kind; each other element split at `=`: not a pair, or a key repeated: `ErrInvalidAuthOpts`; else into a fresh map.

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Internal
public import SpecPlan.Spec.go_uber_org.zap.Api

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

/-- **`decomposeOpts(lg, opts)`**: the kind and the options' map, or `ErrInvalidAuthOpts`. -/
def decomposeOpts.spec : Prop :=
  ∀ (lg : Loc) (opts : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.decomposeOpts)) (Val #lg)) (Val #opts))
  {{ (kind : GoString) (m : Loc) (err : GoInterface), RET (PairV (PairV #kind #m) #err);
      (⌜err = GoInterface.nil ∧ kind = optsKind opts⌝ ∗ optsMapAt m opts) ∨
      errIs .invalidAuthOpts err }}

end spec
end Auth
end EtcdGrove
end Perennial
