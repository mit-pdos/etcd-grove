/-
`(*consistentIndex).SetConsistentApplyingIndex(v, term)` (`cindex.go`): two atomic stores.

**Users**: `apply` (`server.go:1938`), before applying an entry past the consistent index. Snippet
`ReqApplyMovesIndex`.

**Proof sketch**: the store of `applyingIndex` is the linearization point.

**Changes**: logically atomic (was `ciApplying ci v term`, owned). **Margin**: the term is not
modelled.
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

def consistentIndex.SetConsistentApplyingIndex.spec : Prop :=
  ∀ (l : Loc) (γ : CINames) (v t : w64) (Φ : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI l γ ∗ ciWriter γ ∗
      (AU <{ ∃∃ (m : CIState), ciState γ m }> @ ⊤, ∅
        <{ ciState γ { m with aIdx := v }, COMM Φ }>) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!!
      go!"SetConsistentApplyingIndex")) (Val #v)) (Val #t))
  {{ RET #(); ciWriter γ ∗ Φ }}

end spec
end Cindex
end EtcdGrove
end Perennial
