/-
Proof of `Spec/.../mvcc/generation__isEmpty.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.generation.isEmpty.wp_proof : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG) := by
  constructor
  · intro g hg
    subst hg
    wp_start
    wp_auto
    wp_end
  · intro g gv gm dq
    wp_start as ⟨%Hg, Hgv, Hgm⟩
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hg
    · iunfold mvcc.ownGen at Hgm
      icases Hgm with ⟨%Hfields, Hrevs, Hcap⟩
      ihave %Hlen := ownSlice_len _ _ _ $$ Hrevs
      icases mvcc.gen_split _ _ _ $$ Hgv with ⟨Hver, Hcreated, Hrevsf, -⟩
      wp_auto
      have hdec : decide (gv.revs'.len = W64 0) = decide (gm.revs = []) := by
        apply decide_eq_decide.2
        rw [List.length_map] at Hlen
        constructor
        · intro h
          rw [h] at Hlen
          exact List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; rfl)
        · intro h
          rw [h] at Hlen
          simp only [List.length_nil] at Hlen
          word
      rw [hdec]
      iapply HΦ
      isplitl [Hver Hcreated Hrevsf]
      · iapply mvcc.gen_combine _ _ _ Hg; iframe Hver Hcreated Hrevsf
      iunfold mvcc.ownGen
      iframe Hrevs Hcap
      ipureintro; exact Hfields

end proof

end EtcdGrove
end Perennial
