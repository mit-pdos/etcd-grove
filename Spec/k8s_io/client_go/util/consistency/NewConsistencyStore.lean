/-
`NewConsistencyStore(stores)` (`consistency.go:91`): `newConsistencyStore` as a
`ConsistencyStore`. Lean-first.
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

/-- `NewConsistencyStore(sm)`: the interface value of a `*consistencyStore` `c` as
`newConsistencyStore` builds it. -/
abbrev NewConsistencyStore.spec : Prop :=
  ∀ (sm : Loc) (dq : DFrac) (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF)
    (T : Owner → Qp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      sm ↦${dq} S ∗ ([∗map] gr ↦ v ∈ S, getterOk v (G gr)) ∗ tokExcl T }}
    (App (Val (@! NewConsistencyStore)) (Val #sm))
  {{ (c : Loc) (γ : ConsNames),
      RET #(interface.mkOk (go.GoType.PointerType consistencyStore.ty) #c : ConsistencyStore);
      isCons c γ T S G ∗ consState γ ∅ ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), consReader c γ }}

end spec

end consistency
end EtcdGrove
end Perennial
