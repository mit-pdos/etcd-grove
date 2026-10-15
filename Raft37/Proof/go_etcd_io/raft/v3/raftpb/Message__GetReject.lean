/-
Proof of `Raft37/Spec/go_etcd_io/raft/v3/raftpb/Message__GetReject.lean`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject

@[expose] public section

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

theorem raftpb.Message.GetReject.wp_proof :
    raftpb.Message.GetReject.spec (GF := GF) (hG := hG) := by
  constructor
  · intro l dq dqe cap ms
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hp, %Hv⟩ | ⟨#Hp, %Hpn⟩) := cellRO_cases $$ cRj
    · subst Hp
      wp_auto
      rw [show false = ms.msg.Reject' from Hv.symm]
      iapply HΦ
      iunfold msgPtsC
      iexists pty, pto, pfr, pte, plt, pix, pco, pvo, null, prh, es, els, ps, cs, rs, uf
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
