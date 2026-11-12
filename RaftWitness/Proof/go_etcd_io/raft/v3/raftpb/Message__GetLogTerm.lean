/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/Message__GetLogTerm.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.Message.GetLogTerm.wp_proof :
    raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG) := by
  constructor
  · intro l dq dqe cap ms
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hp, %Hv⟩ | ⟨#Hp, %Hpn⟩) := cellRO_cases $$ cLt
    · subst Hp
      wp_auto
      rw [show (W64 0) = ms.msg.LogTerm' from Hv.symm]
      iapply HΦ
      iunfold msgPtsC
      iexists pty, pto, pfr, pte, null, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb
    · wp_if_destruct
      · exact absurd rfl Hpn
      · iapply HΦ
        iunfold msgPtsC
        iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
        isplitr
        · ipureintro; exact Hnn
        iframe
        iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
