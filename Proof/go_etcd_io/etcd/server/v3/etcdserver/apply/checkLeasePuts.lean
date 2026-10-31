/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
theorem apply.checkLeasePuts.wp_proof
    (hKeys : apply.checkLeasePutsKeys.spec (GF := GF) (hG := hG)) :
    apply.checkLeasePuts.spec (GF := GF) (hG := hG) := by
  intro st le γ P f RD on RW ai info dq id L I
  wp_start as ⟨#Hst, #Hle, Hai, Hrd, Hu⟩
  ihave ⟨Hu, %HI⟩ := lease.lessorUser_items γ.leases L I $$ Hu
  ihave #Hle' := Hle
  iunfold apply.isApplyLessorAny at Hle'
  icases Hle' with ⟨%sk, Hle'⟩
  iunfold apply.isApplyLessor at Hle'
  icases Hle' with ⟨Htl, -⟩
  iunfold txn.isTxnLessor at Htl
  icases Htl with ⟨-, %li, %Hli, #HLookup⟩
  subst Hli
  wp_auto
  wp_apply HLookup $$ %id %L %I [$Hu] as %l ⟨Hu, %Hlid⟩
  -- a lease the lessor does not have holds no key
  have hnone : l = null → ∀ it, I.lookup it ≠ some id := by
    intro hl it hit
    exact (Hlid.1 hl) (HI.2 it id hit)
  by_cases hln : l = null
  · subst hln
    wp_auto
    iapply HΦ; iframe Hai Hrd
    isplitl [Hu]
    · iapply lease.lessorUserOpen_close $$ Hu
    isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    iintro %_
    iapply apply.leaseKeysClass_empty
    exact hnone rfl
  · iunfold lease.lessorUserOpen at Hu
    icases Hu with (⟨%Hn, -⟩ | ⟨Hrdl, Hrv, Ho⟩)
    · exact absurd Hn hln
    simp only [hln, decide_false, Bool.not_false]
    wp_auto
    wp_apply (hKeys st γ P f RD on RW ai info dq l id γ.leases L I) $$ [$Hst $Hai $Hrd $Ho]
      as %err ⟨Hai, Hrd, Ho, #HeI, %Hoff, #Hcls⟩
    iapply HΦ; iframe Hai Hrd HeI Hcls
    isplitl [Hrdl Hrv Ho]
    · iapply lease.lessorUserOpen_close γ.leases L I id l
      iunfold lease.lessorUserOpen
      iright
      iframe Hrdl Hrv Ho
    ipureintro; exact Hoff

end proof

end EtcdGrove
end Perennial
