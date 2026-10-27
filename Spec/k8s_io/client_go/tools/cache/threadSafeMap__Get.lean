/-
`(*threadSafeMap).Get(key)` (`thread_safe_store.go:362`): the key's item, under the read lock.
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

/-- **`c.Get(key)`**, logically atomic: the key's item at the linearization point (`nil` and
`false` if none), with its contract (`nil` or `OK`). Needs one of the lock's reader slots. -/
abbrev threadSafeMap.Get.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      tsReader c γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Get")) (Val #key))
    @@ ∅
  <<{ storeSt γ σ }>>
  {{ (item : GoInterface) (ok : Bool), RET (PairV #item #ok);
      ⌜item = objAt σ.items key ∧ ok = decide (key ∈ σ.items)⌝ ∗ okNil OK item ∗
      tsReader c γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
