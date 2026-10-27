/-
`(*threadSafeMap).List()` (`thread_safe_store.go:369`): the items, under the read lock.
Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.List()`**, logically atomic: a new slice of the items at the linearization point, one per
key (in some order, `ks`), each with its contract. Needs one of the lock's reader slots. -/
abbrev threadSafeMap.List.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      tsReader c γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"List")) (Val #()))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString,
      ⌜ks.Nodup ∧ ∀ k, k ∈ ks ↔ k ∈ σ.items⌝ ∗ sl ↦* (ks.map (objAt σ.items)) ∗
      ([∗list] o ∈ ks.map (objAt σ.items), okNil OK o) ∗ tsReader c γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
