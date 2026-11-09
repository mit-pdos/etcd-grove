/-
`(*treeIndex).unsafeVisit(key, end, f)` (`index.go:95`), the lock held: `f` on the key indexes from
`key` (below `end` if non-empty: `idxEnts`) in order (1g's `AscendGreaterOrEqual`), until it returns
false. `f`'s effects are the caller's family `I vis b` (`vis` the visited, `b` the last answer).
Internal (`Revisions`, `CountRevisions`, `Range`). **Changes**: the visit as a prefix of `idxEnts`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `ti.unsafeVisit(key, end, f)`. -/
def treeIndex.unsafeVisit.spec : Prop :=
  ∀ (ti : Loc) (dq : DFrac) (M : IndexM) (key endk : GoSlice) (k e : GoString) (dk de : DFrac)
    (f : GoFunc) (l : List (GoString × KeyIndexM)) (I : List (GoString × KeyIndexM) → Bool → IProp GF),
  {{ pkgInit ∗ treeOwn ti dq M ∗ ⌜idxEnts M k e l⌝ ∗ key ↦*{dk} k ∗ endk ↦*{de} e ∗ I [] true ∗
      □ (∀ (vis : List (GoString × KeyIndexM)) (p : Loc) (k' : GoString) (ki : KeyIndexM)
          (Φ : val → IProp GF),
        ⌜vis ++ [(k', ki)] <+: l⌝ -∗ I vis true -∗ ownKi p k' ki dq -∗
        ▷ (∀ b : Bool, I (vis ++ [(k', ki)]) b -∗ ownKi p k' ki dq -∗ Φ #b) -∗
        WP (App (Val #f) (Val #p)) {{ Φ }}) }}
    (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"unsafeVisit")) (Val #key)) (Val #endk)) (Val #f))
  {{ RET #(); treeOwn ti dq M ∗ key ↦*{dk} k ∗ endk ↦*{de} e ∗
      ∃ (vis : List (GoString × KeyIndexM)) (b : Bool), I vis b ∗ ⌜vis <+: l ∧ (b = true → vis = l)⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
