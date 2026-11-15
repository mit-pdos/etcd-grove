/-
`(*consistentIndex).ConsistentApplyingIndex()` (`cindex.go`): two atomic loads.

**Users**: `applyConfChange` (`server.go:2042`), the post-lock hook (`server.go:2480`). A reader: no
writer's token. Snippet `ReqApplyMovesIndex`.

**Proof sketch**: the load of `applyingIndex` is the linearization point (state unchanged); the term
loaded after it is some value.

**Changes**: logically atomic (was owned `ciApplying`). **Margin**: the term is any value (a
concurrent setter may interleave).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cindex

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

def consistentIndex.ConsistentApplyingIndex.spec : Prop :=
  ∀ (l : Loc) (γ : CINames) (Φ : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI l γ ∗
      (AU <{ ∃∃ (m : CIState), ciState γ m }> @ ⊤, ∅ <{ ciState γ m, COMM Φ m.aIdx }>) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!!
      go!"ConsistentApplyingIndex")) (Val #()))
  {{ (v t : w64), RET (PairV #v #t); Φ v }}

end spec
end Cindex
end EtcdGrove
end Perennial
