/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/isBadOp.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.isBadOp
public import Spec.go_etcd_io.etcd.client.v3.Op__Rev
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem isBadOp.wp_proof (hrev : Op.Rev.spec (GF := GF) (hG := hG))
    (hrange : Op.RangeBytes.spec (GF := GF) (hG := hG)) :
    isBadOp.spec (GF := GF) (hG := hG) := by
  intro opv o
  wp_start as Hop
  unfold opFullAt
  icases Hop with ⟨#Hat, #Hkey, %Hf, #Hval, #Hsort⟩
  wp_auto
  wp_apply hrev $$ [$op $Hat] as op
  unfold isBadOpM
  by_cases h1 : 0 < sint.Z o.base.rev
  · simp only [show sint.Z (W64 0) = 0 from rfl, h1, decide_true, true_or]
    wp_auto
    wp_end
  · simp only [show sint.Z (W64 0) = 0 from rfl, h1, decide_false, false_or]
    wp_auto
    wp_apply hrange $$ [$op $Hat] as %sl ⟨op, #Hend⟩
    ihave %Hlen := ownSlice_len $$ Hend
    have : decide (sint.Z (W64 0) < sint.Z sl.len) = decide (o.base.rangeEnd ≠ []) := by
      apply decide_eq_decide.2
      constructor
      · intro h hn; rw [hn] at Hlen; simp at Hlen; word
      · intro h; have := List.length_pos_iff.2 h; word
    rw [this]
    iapply HΦ; itrivial

end proof

end leasing
end EtcdGrove
end Perennial
