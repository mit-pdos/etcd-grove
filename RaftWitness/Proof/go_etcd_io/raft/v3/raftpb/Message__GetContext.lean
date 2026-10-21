/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/Message__GetContext.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext

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

theorem raftpb.Message.GetContext.wp_proof :
    raftpb.Message.GetContext.spec (GF := GF) (hG := hG) := by
  constructor
  · intro l dq dqe cap ms
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · iapply HΦ
      iframe Hcs
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
