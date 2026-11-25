/-
`errors.AsLeafTy` (`Spec/errors/AsLeafTy.lean`): the leaf case of `errors.AsNoMatch`
(`Spec/errors/AsNoMatch.lean`). An axiom from 2026-11-15 (approved by etcd-grove-81 after an
independent review) to 2026-11-20 (prove-k8s2), when `AsNoMatch` generalized it to wrappers.
-/
module

public import Spec.errors.AsLeafTy
public import Spec.errors.AsNoMatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

theorem errors.AsLeafTy.wp_proof (wp_AsNoMatch : errors.AsNoMatch.spec (GF := GF) (hG := hG)) :
    errors.AsLeafTy.spec (GF := GF) (hG := hG) := by
  intro ii l T' _ _ T _ v hT hleaf hts hmod hp hk hn hm hu
  iintro %Φ ⟨#Hpkg, Hl⟩ HΦ
  iapply (wp_AsNoMatch (GoInterface.ok ii) l v hT hk hn hm) $$ [Hl] HΦ
  iframe Hpkg Hl
  ileft
  ipureintro
  refine Or.inr ⟨ii, rfl, hleaf, hts, hmod, fun hI => ?_, hu⟩
  obtain ⟨X, p, hty, -⟩ := hp hI
  obtain ⟨ty, iv⟩ := ii
  simp only at hty
  subst hty
  exact _root_.Perennial.errors.asTyRepr_pointer T X iv hI

end proof

end EtcdGrove
end Perennial
