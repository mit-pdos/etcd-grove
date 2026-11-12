/-
`(*threadSafeMap).ListKeys()` (`thread_safe_store.go:381`): the keys, under the read lock.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.ListKeys()`**, logically atomic: a new slice of the keys at the linearization point, each
once (in some order). Needs one of the lock's reader slots. -/
abbrev threadSafeMap.ListKeys.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      tsReader c γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"ListKeys")) (Val #()))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString,
      ⌜ks.Nodup ∧ ∀ k, k ∈ ks ↔ k ∈ σ.items⌝ ∗ sl ↦* ks ∗ tsReader c γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
