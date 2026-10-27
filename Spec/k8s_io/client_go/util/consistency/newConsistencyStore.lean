/-
`newConsistencyStore(stores)` (`consistency.go:95`): a new store over `stores`, with no records.
Lean-first.
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

/-- `newConsistencyStore(sm)` over the stores `S` (whose getters meet `G`; the map is kept, and is
read-only from now on), for the caller's permissions `T`: a store with no records
(`consState γ ∅`) and all the map lock's reader slots. -/
abbrev newConsistencyStore.spec : Prop :=
  ∀ (sm : Loc) (dq : DFrac) (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF)
    (T : Owner → Qp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      sm ↦${dq} S ∗ ([∗map] gr ↦ v ∈ S, getterOk v (G gr)) ∗ tokExcl T }}
    (App (Val (@! newConsistencyStore)) (Val #sm))
  {{ (c : Loc), RET #c; ∃ γ : ConsNames, isCons c γ T S G ∗ consState γ ∅ ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), consReader c γ }}

end spec

end consistency
end EtcdGrove
end Perennial
