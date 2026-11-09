/-
`(*consistentIndex).UnsafeConsistentIndex()` (`cindex.go`): as `ConsistentIndex`, without the mutex
(the caller holds the backend's batch transaction lock, so the read uses `UnsafeReadConsistentIndex`).

**Users**: the post-lock hook (`server.go:2481`, `getTxPostLockInsideApplyHook`). Snippet
`ReqApplyMovesIndex`.

**Proof sketch**: as `ConsistentIndex`; `ci.be` is read unlocked, which is race-free because the only
writer of `be` (`SetBackend`) needs `ciWriter`, held here.

**Changes**: as `ConsistentIndex`. **Margin**: the term is not returned.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.Api

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

def consistentIndex.UnsafeConsistentIndex.spec : Prop :=
  ∀ (l : Loc) (γ : CINames) (Φ : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI l γ ∗ ciWriter γ ∗
      (AU <{ ∃∃ (m : CIState), ciState γ m ∗ ⌜m.idx = W64 0 → m.stored ≠ none⌝ }> @ ⊤, ∅
        <{ ciState γ (if m.idx = W64 0 then { m with idx := m.stored.getD (W64 0) } else m),
           COMM Φ (if m.idx = W64 0 then m.stored.getD (W64 0) else m.idx) }>) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!!
      go!"UnsafeConsistentIndex")) (Val #()))
  {{ (v : w64), RET #v; ciWriter γ ∗ Φ v }}

end spec
end Cindex
end EtcdGrove
end Perennial
