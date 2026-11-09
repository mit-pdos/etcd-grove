/-
## `(*tokenNop).genTokenPrefix` (internal helper)

**Users.** `nop_provider` (the bundle).

**Proof sketch.** The body (`nop.go`).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

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

/-- **`p.genTokenPrefix`** of the no-op provider. -/
def tokenNop.genTokenPrefix.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenNop.ty @!! go!"genTokenPrefix")) (Val #()))
  {{ (s : GoString) (err : GoInterface), RET (PairV #s #err); ⌜s = [] ∧ err = GoInterface.nil⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
