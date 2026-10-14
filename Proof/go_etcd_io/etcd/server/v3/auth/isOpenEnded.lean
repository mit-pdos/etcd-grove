/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/isOpenEnded.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.isOpenEnded

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.isOpenEnded.wp_proof :
    auth.isOpenEnded.spec (GF := GF) (hG := hG) := by
  intro re e de
  wp_start as He
  ihave %Hl := ownSlice_len _ _ _ $$ He
  wp_auto
  wp_if_destruct
  · have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z re.len := by
      rw [Hif]; decide
    have hlen : e.length = 1 := by rw [Hl.1, Hif]; rfl
    obtain ⟨x, hx⟩ : ∃ x, e[0]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [Hbnd, and_self, ite_true]
    wp_apply wp_load_slice_index re (sint.Z (W64 0)) e de x (by decide) $$ [He] as He
    · iframe He; ipureintro; exact hx
    wp_end
  · wp_end

end proof

end EtcdGrove
end Perennial
