/-
`(*consistentIndex).ConsistentIndex()` (`cindex.go`): the in-memory index if non-zero; else, under
the mutex, the backend's stored one (`schema.ReadConsistentIndex(ci.be.ReadTx())`), which it stores.

**Users**: `apply` (`server.go:1925`), `applyEntryNormal`'s defer (`server.go:1975`),
`applySnapshot` (`server.go:1100`), `snapshot` (`server.go:2143`), bootstrap (`bootstrap.go:273,
491, 629`), the applier's `Authenticate` (`apply/backend.go:158`). Snippets `ReqApplyMovesIndex`,
`ReqReloadAfterSetBackend`.

**Proof sketch**: atomic load of `consistentIndex`: non-zero, the linearization point (the AU's
abort-free read: state unchanged). Zero: lock `mutex`; read the backend (`beStoredCI m.be v`, 4b's
`ReadConsistentIndex` over 4a's `ReadTx`); store `v` (the linearization point: with `ciWriter`, no
other writer changed `idx` since the load, so the state at the store has `idx = 0` and
`stored = some v`), store the term; unlock.

**Changes**: logically atomic over `ciState` (was `ciIdx γ i` read at a fixed value).

**Margin**: the term is not returned (Go returns only the index).
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

/-- **The consistent index**: the in-memory one, or (when `0`) the backend's stored one, which is
then loaded. -/
def consistentIndex.ConsistentIndex.spec : Prop :=
  ∀ (l : Loc) (γ : CINames) (Φ : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI l γ ∗ ciWriter γ ∗
      (AU <{ ∃∃ (m : CIState), ciState γ m ∗ ⌜m.idx = W64 0 → m.stored ≠ none⌝ }> @ ⊤, ∅
        <{ ciState γ (if m.idx = W64 0 then { m with idx := m.stored.getD (W64 0) } else m),
           COMM Φ (if m.idx = W64 0 then m.stored.getD (W64 0) else m.idx) }>) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!!
      go!"ConsistentIndex")) (Val #()))
  {{ (v : w64), RET #v; ciWriter γ ∗ Φ v }}

end spec
end Cindex
end EtcdGrove
end Perennial
