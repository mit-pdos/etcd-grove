/- Port of election_proof/proof_raftLog__maxAppliableIndex.v (857d09190).

Lean notes: Rocq's `wp_min2_uint64` is the local `wp_min_u64` (as in
`Proof/Progress__MaybeDecrTo.lean`). -/
import EtcdGrove.Raft.Spec.raftLog__maxAppliableIndex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The builtin `min` on `uint64` (Rocq `wp_min2_uint64`): its body is `w64Min`'s `if`. -/
private theorem wp_min_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.min [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ RET #(w64Min a b); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Min a b = a from if_pos Hif]
    iapply HΦ; itrivial
  · rw [show w64Min a b = b from if_neg Hif]
    iapply HΦ; itrivial

theorem raftLog.maxAppliableIndex.wp_proof :
    raftLog.maxAppliableIndex.spec (GF := GF) (hG := hG) := by
  intro l ls au
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  wp_alloc l_ptr as l; wp_pures; wp_alloc allowUnstable_ptr as allowUnstable; wp_pures; wp_load
  wp_pures; wp_load; wp_pures; wp_alloc hi_ptr as hi; wp_pures; wp_store; wp_pures; wp_load
  wp_pures; iclear allowUnstable
  cases au
  · wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear l
    wp_apply wp_min_u64
    wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear hi
    iapply HΦ
    isplitl
    · reseal_raftLog
    ipureintro
    simp only [w64Min_spec, logOffset, Bool.false_eq_true, ite_false]
    subst lcm
    word
  · wp_pures; wp_load; wp_pures; iclear l hi
    iapply HΦ
    isplitl
    · reseal_raftLog
    ipureintro
    simp [Hcm]

end proof

end EtcdGrove
end Perennial
