/-
Port of election_proof/proof_raftLog__zeroTermOnOutOfBounds.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__zeroTermOnOutOfBounds

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

/-- The three cases of the premise. For the two globals, the error is a pointer-typed
interface (`IsNewError`, `Base.lean`), so both comparisons step (`CheckComparable` of a
pointer type) and the first one that matches returns `0`. -/
theorem raftLog.zeroTermOnOutOfBounds.wp_proof :
    raftLog.zeroTermOnOutOfBounds.spec (GF := GF) (hG := hG) := by
  intro l t err
  wp_start as #Herr
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  icases Herr with (%Hnil | #Hc | #Hu)
  · subst Hnil
    wp_auto
    iapply HΦ
    ipureintro
    intro _; rfl
  · icombine Hc ErrCompacted gives %Heq
    subst Heq
    obtain ⟨ty, p, rfl⟩ := HErrCompacted_new
    wp_auto
    iapply HΦ
    ipureintro
    intro Hn; cases Hn
  · icombine Hu ErrUnavailable gives %Heq
    subst Heq
    obtain ⟨ty, p, rfl⟩ := HErrUnavailable_new
    obtain ⟨tyc, pc, rfl⟩ := HErrCompacted_new
    wp_auto
    split
    · -- same dynamic type: compare the pointers
      by_cases Hp : p = pc
      · subst Hp
        wp_auto
        iapply HΦ
        ipureintro
        intro Hn; cases Hn
      · wp_auto
        simp only [Hp, decide_false]
        wp_auto
        iapply HΦ
        ipureintro
        intro Hn; cases Hn
    · wp_auto
      iapply HΦ
      ipureintro
      intro Hn; cases Hn

end proof

end EtcdGrove
end Perennial
