/-
Proof of `Spec/errors/AsLeaf.lean`: `errors.AsLeafTy` at `*errorString` (k8s 7f-5a-P, decided by
etcd-grove-81 2026-11-15: it was an axiom, which `AsLeafTy` generalizes).
-/
module

public import Spec.errors.AsLeaf
public import Spec.errors.AsLeafTy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

theorem errors.AsLeaf.wp_proof (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG)) :
    errors.AsLeaf.spec (GF := GF) (hG := hG) := by
  intro x l T' _ _ T _ v hT hl hts hu
  -- `*errorString` has kind `Pointer`, which is no struct, channel or function kind: either `T`'s
  -- kind is one of those (then the kinds differ) or it is not
  refine wp_AsLeafTy ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ l v hT hl hts
    (fun hI => ⟨hu hI, ?_⟩)
  rw [go.is_underlying (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty)]
  cases h : underlying T <;> simp [_root_.Perennial.errors.undecidedKind, go.kindOf, h]

end proof

end EtcdGrove
end Perennial
