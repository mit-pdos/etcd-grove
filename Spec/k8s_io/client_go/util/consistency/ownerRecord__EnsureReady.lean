/-
`(*ownerRecord).EnsureReady(c)` (`consistency.go:197`): checks every recorded version against its
store, under the record's lock. Lean-first; internal: `EnsureReady`'s linearization point.
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

/-- `r.EnsureReady(c)` for `EnsureReady(s.owner)`, which deposited its permission in the slot
`⟨r, V, false⟩` (so `r`'s versions are `V`): logically atomic as `EnsureReady` itself; on `nil`
the slot is marked cleared (the owner's record is deleted abstractly) and its receipt returned, on
an error the permission. -/
abbrev ownerRecord.EnsureReady.spec : Prop :=
  ∀ (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) (r : Loc) (s : RecS) (V : Vs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      isCons c γ T S G ∗ isRec γ r s ∗ ensTok γ s.owner ⟨r, V, false⟩ }}
  <<{ ∀∀ M, consState γ M }>>
    (App (Val (r @!! go.GoType.PointerType ownerRecord.ty @!! go!"EnsureReady")) (Val #c))
    @@ ↑consN
  <<{ ∃∃ ok : Bool, consState γ (if ok then GMap.delete s.owner M else M) ∗
      (if ok then readyRec S G (M !! s.owner) else iprop(True)) }>>
  {{ (err : GoInterface), RET #err; ⌜ok = true ↔ err = interface.nil⌝ ∗
      (if ok then ensTok γ s.owner ⟨r, V, true⟩ else T s.owner 1) }}

end spec

end consistency
end EtcdGrove
end Perennial
