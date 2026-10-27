/-
`(*consistencyStore).EnsureReady(owner)` (`consistency.go:151`): whether the stores have seen the
owner's recorded writes; if so, the record is cleared. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.consistency.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI k8s_io.client_go.util.consistency

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- **`c.EnsureReady(o)`**, logically atomic. It returns `nil` (`ok`) only if, at its
linearization point, every version `wroteRV` the owner's record holds (`M !! o`) was checked
against its group resource's store (`readyRec`): a store is registered (not nil) for it, and its
`LastStoreSyncResourceVersion()` returned a non-empty `readRV` with the store's contract
`G gr readRV` and, **if `readRV` is well formed**, `decVal wroteRV ≤ decVal readRV`; the record
is then deleted (`GMap.delete o M`). Otherwise it returns an error and changes nothing. With no
record it returns `nil`.

The check fails safe on an empty `readRV` (an unsynced store) and on a group resource with no
store, but **not on a `readRV` that is not well formed** (`"0"`, say, or any non-decimal string):
`CompareResourceVersion` then fails and the loop skips the group resource
(`consistency.go:211`), so such a store counts as ready whatever it has seen.

The caller holds `T o 1` (the documented precondition: no `WroteAt(o, ...)` meanwhile) and one of
the map lock's reader slots. -/
abbrev consistencyStore.EnsureReady.spec : Prop :=
  ∀ (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) (o : Owner),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      isCons c γ T S G ∗ T o 1 ∗ consReader c γ }}
  <<{ ∀∀ M, consState γ M }>>
    (App (Val (c @!! go.GoType.PointerType consistencyStore.ty @!! go!"EnsureReady")) (Val #o))
    @@ ↑consN
  <<{ ∃∃ ok : Bool, consState γ (if ok then GMap.delete o M else M) ∗
      (if ok then readyRec S G (M !! o) else iprop(True)) }>>
  {{ (err : GoInterface), RET #err; ⌜ok = true ↔ err = interface.nil⌝ ∗ T o 1 ∗ consReader c γ }}

end spec

end consistency
end EtcdGrove
end Perennial
