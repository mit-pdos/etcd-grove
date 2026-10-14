/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__IsSortOptionValid.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__IsSortOptionValid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.IsSortOptionValid.wp_proof : Op.IsSortOptionValid.spec (GF := GF) (hG := hG) := by
  intro opv o
  wp_start as ⟨#Hat, %Hs⟩
  iunfold opFullAt at Hat
  icases Hat with ⟨Hat, -⟩
  iunfold opAt at Hat
  icases Hat with ⟨%Hf, -⟩
  unfold OpFields at Hf
  obtain ⟨-, -, hs, -⟩ := Hf
  have hs' : opv.sort' = null := Classical.byContradiction fun hne => by
    rw [Hs] at hs; exact absurd (hs.1 hne) (by simp)
  wp_auto
  rw [hs']
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
