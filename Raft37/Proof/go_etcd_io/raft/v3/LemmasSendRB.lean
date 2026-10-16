/-
Lemmas of group G2 (fork B: `appendEntry`, `handleAppendEntries`, `handleHeartbeat`,
`handleSnapshot`) of stage R4 phase 3.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.LemmasSendR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `From` field of a message, lent (`&pb.Message{To: m.From, ...}` reads the pointer: the
new message shares the read-only cell). (The same as `StepProof.msgPtsC_From_acc`, which is
`raft.Step`'s.) -/
theorem msgPtsC_From_lend (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦{dq} p ∗ cellRO p ms.msg.From' ∗
        (l.[raftpb.Message, go!"From"] ↦{dq} p -∗ msgPtsC l dq dqe cap ms) := by
  iintro H
  iunfold msgPtsC at H
  iNamed H
  iexists pfr
  iframe HFr cFr
  iintro HFr
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

end lemmas

end EtcdGrove
end Perennial
