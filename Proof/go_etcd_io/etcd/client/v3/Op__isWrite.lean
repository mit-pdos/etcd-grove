/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__isWrite.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__isWrite

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.isWrite.wp_proof : Op.isWrite.spec (GF := GF) (hG := hG) := by
  intro opv o
  wp_start as ⟨#Hat, %Ht⟩
  iunfold opFullAt at Hat
  icases Hat with ⟨-, -, %Hf2, -, -⟩
  obtain ⟨ht, -⟩ := Hf2
  wp_auto
  rw [ht, decide_eq_false Ht]
  wp_auto
  rw [ht, show (!decide (o.t = W64 1)) = decide (o.t ≠ W64 1) by simp]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
