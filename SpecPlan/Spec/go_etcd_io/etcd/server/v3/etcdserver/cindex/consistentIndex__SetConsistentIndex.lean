/-
`(*consistentIndex).SetConsistentIndex(v, term)` (`cindex.go`): two atomic stores.

**Users**: `applyEntryNormal`'s defer (`server.go:1977`), `applyConfChange` (`server.go:2043`), the
post-lock hook (`server.go:2482`), `ConsistentIndex` itself. Snippet `ReqApplyMovesIndex`.

**Proof sketch**: the store of `consistentIndex` is the linearization point (`ciWriter`: no other
writer); the term's store follows.

**Changes**: logically atomic (was over `ciIdx`). **Margin**: the term is not modelled.
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

def consistentIndex.SetConsistentIndex.spec : Prop :=
  ∀ (l : Loc) (γ : CINames) (v t : w64) (Φ : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI l γ ∗ ciWriter γ ∗
      (AU <{ ∃∃ (m : CIState), ciState γ m }> @ ⊤, ∅
        <{ ciState γ { m with idx := v }, COMM Φ }>) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!!
      go!"SetConsistentIndex")) (Val #v)) (Val #t))
  {{ RET #(); ciWriter γ ∗ Φ }}

end spec
end Cindex
end EtcdGrove
end Perennial
