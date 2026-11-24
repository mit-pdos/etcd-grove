/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/msgOf.lean`: every
field read by its getter, the entries through `entriesOf` (its receipts passed on)..
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgType
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entriesOf
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetRejectHint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]


variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem msgOf.wp_proof
    (wp_msgType : msgType.spec (GF := GF) (hG := hG))
    (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_entriesOf : entriesOf.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG))
    (wp_GetRejectHint : raftpb.Message.GetRejectHint.spec (GF := GF) (hG := hG)) :
    msgOf.spec (GF := GF) (hG := hG) := by
  intro ml dq dqe cap st to hsnap hnorm
  wp_start as Hm
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetIndex.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_GetLogTerm.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
  try wp_auto
  wp_apply wp_GetType.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
  try wp_auto
  wp_if_destruct
  · exact absurd Hif hsnap
  wp_apply wp_GetType.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_msgType st.msg.Type' $$ [$Hpkg]
  wp_apply wp_GetFrom.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_Name st.msg.From' $$ [$Hpkg]
  try wp_auto
  wp_apply wp_Name to $$ [$Hpkg]
  wp_apply wp_GetTerm.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
  try wp_auto
  wp_apply wp_GetEntries.1 ml dq dqe cap st $$ [$Hpb $Hm] as %es %els ⟨Hes, #Hents, Hcap, Hclose⟩
  wp_apply wp_entriesOf es dqe els st.ents hnorm $$ [$Hpkg $Hes $Hents] as %out ⟨Hes, #Hout, Hr⟩
  ihave Hm := Hclose $$ %cap %els %st.ents Hes Hents Hcap
  rw [show ({ msg := st.msg, ents := st.ents, snap := st.snap, ctx := st.ctx, resps := st.resps } : MsgSt)
    = st from rfl]
  wp_apply wp_GetCommit.1 ml dq dqe cap _ $$ [$Hpb $Hm] as Hm
  wp_apply wp_GetReject.1 ml dq dqe cap _ $$ [$Hpb $Hm] as Hm
  wp_apply wp_GetRejectHint.1 ml dq dqe cap _ $$ [$Hpb $Hm] as Hm
  try wp_auto
  iapply HΦ
  isplitl [Hm]
  · iexact Hm
  iframe Hr
  iunfold AntCheck.msgRO
  have hns : decide (st.msg.Type' = MsgSnap) = false := decide_eq_false hsnap
  simp only [msgOfSt, hns, Bool.false_eq_true, ↓reduceIte, AntCheck.fieldRO]
  isplitr
  · ipureintro
    simp only [AntCheck.fieldRel, AntCheck.hasBit, AntCheck.mfType, AntCheck.mfFrom, AntCheck.mfTo,
      AntCheck.mfTerm, AntCheck.mfIndex, AntCheck.mfLogTerm, AntCheck.mfCommit, AntCheck.mfReject]
    and_intros <;> first | decide | trivial
  isplitr
  · ipureintro; simp only [AntCheck.hasBit, AntCheck.mfEntries]; decide
  iexact Hout

end proof

end AntHarness
end EtcdGrove
end Perennial
