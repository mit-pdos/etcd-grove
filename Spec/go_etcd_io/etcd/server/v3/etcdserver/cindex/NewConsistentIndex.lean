/-
`cindex.NewConsistentIndex(be)` (`cindex.go`).

**Users**: `bootstrap.go:257` (`NewConsistentIndex(nil)`, then `SetBackend` once the backend is
open: batch 2e). Snippet `examples/specreq/cindex/cindex.go` (`ReqReloadAfterSetBackend`).

**Proof sketch**: allocate the struct (zero indices, `be`), the invariant of `isCI` and the ghost
state `ciState γ ⟨0, 0, be, stored⟩`, `ciWriter γ`.

**Changes**: the old `ciIdx γ 0 ∗ ciApplying ci 0 0 ∗ ciOwner ci be` become one client-owned state and
the writer's token; any `be` (was: the one bootstrap passes).

**Margin**: none.
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

/-- **A new indexer** over backend `be` (or `nil`): index `0` (not loaded), reading `be`'s stored
index `v` when `be` is not `nil`. -/
def NewConsistentIndex.spec : Prop :=
  ∀ (be : GoInterface) (stored : Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      (match stored with
       | none => iprop(⌜be = interface.nil⌝)
       | some v => beStoredCI be v) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.cindex.NewConsistentIndex)) (Val #be))
  {{ (ci : GoInterface), RET #ci; ∃ (l : Loc) (γ : CINames), ⌜ci = ciIface l⌝ ∗ isCI l γ ∗
      ciState γ ⟨W64 0, W64 0, be, stored⟩ ∗ ciWriter γ }}

end spec
end Cindex
end EtcdGrove
end Perennial
