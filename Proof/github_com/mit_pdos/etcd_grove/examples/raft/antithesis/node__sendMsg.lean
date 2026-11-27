/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__sendMsg.lean`. The node is not
dead (`emitOk`); the message, read-only at its content, is cloned (`cloneMsg.law`: it has no
responses, the spec's premise) while its capacity stays with the caller (`msgPtsCC_ro_split`); the clone,
its entries frozen at the network's capacity flag (`msgPtsCC_clone_net`), with the original's facts,
is a message `Cluster.send` takes (`sendMsg`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sendMsg
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__send
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.CloneMsgLaw

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A read-only message's content, without its capacity** (persistent), next to the message: the
capacity (when `cap`) is the only part not read-only. -/
theorem msgPtsCC_ro_split (l : Loc) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l DFrac.discard DFrac.discard cap c ⊢
      msgPtsCC l DFrac.discard DFrac.discard false c ∗ msgPtsCC l DFrac.discard DFrac.discard cap c := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %Hnn, #HTy, #cTy, #HTo, #cTo, #HFr, #cFr, #HTe, #cTe, #HLt, #cLt, #HIx, #cIx, #HCo, #cCo,
    #HVo, #cVo, #HRj, #cRj, #HRh, #cRh, #HEs, #Hes, #Hents, Hcap, #HSn, #Hsn, #HCx, #Hcx, #HRs, #Hrs,
    #Hpb⟩
  isplitr [Hcap]
  · iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr
    · ipureintro; exact Hnn
    iframe HTy cTy HTo cTo HFr cFr HTe cTe HLt cLt HIx cIx HCo cCo HVo cVo HRj cRj HRh cRh
      HEs Hes Hents HSn Hsn HCx Hcx HRs Hrs Hpb
  · iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
    isplitr
    · ipureintro; exact Hnn
    iframe HTy cTy HTo cTo HFr cFr HTe cTe HLt cLt HIx cIx HCo cCo HVo cVo HRj cRj HRh cRh
      HEs Hes Hents Hcap HSn Hsn HCx Hcx HRs Hrs Hpb

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.sendMsg.wp_proof
    (wp_send : Cluster.send.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG)) :
    node.sendMsg.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j ml cap st q
  wp_start as ⟨Hc, Hn, Hemit, Had, Htok, Hm, Hf, %Hss, %Hres⟩
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  iunfold nodeRO at Hn
  icases Hn with ⟨%ch, %d, #Hnc, -⟩
  iunfold emitOk at Hemit
  icases Hemit with ⟨Hdead, Hfuse⟩
  icases msgPtsC_msgPtsCC ml _ _ cap st $$ Hm with ⟨%cm, Hm, %Hcm⟩
  obtain ⟨rfl, hu⟩ := Hcm
  icases msgPtsCC_ro_split ml cap cm $$ Hm with ⟨#Hro, Hm⟩
  have hcr : cm.resps = [] := by simpa [MsgC.model] using Hres
  wp_auto
  wp_apply (cloneMsg_law_of wp_Clone) ml cm hcr $$ [$Hproto $Hro] as %l' Hl'
  try wp_auto
  imod msgPtsCC_clone_net l' (needsCap cm.model.msg) cm $$ Hl' with Hl'
  wp_apply wp_send c γ l' cm.model q $$ [$Hpkg $Hc $Had $Htok Hl' Hf] as ⟨Had, Htok⟩
  · iunfold sendMsg
    iframe Hf
    isplitl [Hl']
    · iexists cm; iframe Hl'; ipureintro; exact ⟨rfl, hu⟩
    ipureintro; exact Hss
  try wp_auto
  iapply HΦ
  iframe Had Htok
  iunfold emitOk
  iframe Hdead Hfuse
  iapply msgPtsCC_msgPtsC ml _ _ cap cm hu $$ Hm

end proof

end AntHarness
end EtcdGrove
end Perennial
