/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__send.lean`: a proposal returns
at once; another message's goroutine is added to the network's join with the caller's thread token
(`netJoin.wp_Add_of`), forked keeping the fresh token (`wp_fork_tok_self`), and given the message
(`netMsg`): it reads the destination (`To`, the protocol message's `dst`, one of the three nodes), and
delivers the message to that node's input (`inputOk`) or drops it; its `Done` hands its token back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__node
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__isolatedNow
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Perennial.Spec.time.Sleep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [sync_sem : sync.Assumptions]

/-- A message's protocol reading is addressed to its `To`. -/
private theorem absMsgOf_dst' {st : MsgSt} {m : Msg} (H : absMsgOf st = some m) :
    m.dst = st.msg.To' := by
  unfold absMsgOf at H
  split at H
  · cases H
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 H; rfl
  · cases H; rfl

/-- `c.node(nodeId j)` is node `j`. -/
private theorem nodeOf_nodeId (ns : List Loc) (hl : ns.length = 3) (j : Fin 3) :
    nodeOf ns (AntSim.nodeId j) = ns[j.val]! := by
  obtain ⟨k, hk⟩ := j
  unfold nodeOf AntSim.nodeId
  match k, hk with
  | 0, _ => simp [hl]
  | 1, _ => simp [hl]
  | 2, _ => simp [hl]

/-- Node `j`'s record, of the three. -/
private theorem nodeRO_of (γ : AntNames) (ns : List Loc) (j : Fin 3) :
    nodeRO (GF := GF) γ ns[0]! 0 ∗ nodeRO γ ns[1]! 1 ∗ nodeRO γ ns[2]! 2 ⊢ nodeRO γ ns[j.val]! j := by
  obtain ⟨k, hk⟩ := j
  match k, hk with
  | 0, _ => show _ ⊢ nodeRO γ ns[0]! 0; iintro ⟨H, -, -⟩; iexact H
  | 1, _ => show _ ⊢ nodeRO γ ns[1]! 1; iintro ⟨-, H, -⟩; iexact H
  | 2, _ => show _ ⊢ nodeRO γ ns[2]! 2; iintro ⟨-, -, H⟩; iexact H

theorem Cluster.send.wp_proof
    (wp_deliver : Cluster.deliver.spec (GF := GF) (hG := hG))
    (wp_node : Cluster.node.spec (GF := GF) (hG := hG))
    (wp_isolatedNow : Cluster.isolatedNow.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    Cluster.send.spec (GF := GF) (hG := hG) := by
  intro _ c γ ml st q
  wp_start as ⟨#Hc, Had, Htok, Hm⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, #Hr, #Hrec, #Hro, %Hlen, #Hn0, #Hn1, #Hn2,
    #Hstop, #Hbc, #Hnj, #Hinv, %Hfits⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold sendMsg at Hm
  icases Hm with (⟨%Hprop, %cm, Hm, %Hcm⟩ | ⟨%m, Hnm⟩)
  · -- a forwarded proposal: dropped
    ihave Hm := msgPtsCC_msgPtsC ml _ _ _ cm Hcm.2 $$ Hm
    rw [Hcm.1]
    wp_auto
    wp_apply wp_GetType.1 ml _ _ _ st $$ [$Hpb $Hm] as Hm
    rw [Hprop]
    wp_auto
    iapply HΦ
    iframe Had Htok
  -- a message in flight
  iunfold netMsg at Hnm
  icases Hnm with ⟨⟨%cm, Hm, %Hcm⟩, %Hnf, #Hism, Htlb, #Hsent⟩
  ihave Hm := msgPtsCC_msgPtsC ml _ _ _ cm Hcm.2 $$ Hm
  rw [Hcm.1]
  have hnp : st.msg.Type' ≠ MsgProp := by
    have h := Hnf.2.1
    simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> rw [h] <;> simp only [MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp] <;> word
  wp_auto
  wp_apply wp_GetType.1 ml _ _ _ st $$ [$Hpb $Hm] as Hm
  wp_if_destruct
  · exact absurd Hif hnp
  ihave Hcf := Hcfg
  iStructNamed Hcf
  try wp_auto
  wp_apply wp_below (cfg.MaxDelay' + W64 1) (by have := Hcok.2.2; word) $$ [$Hpkg] as %dl %Hdl
  try wp_auto
  wp_apply wp_below (W64 100) (by decide) $$ [$Hpkg] as %dp %Hdp
  try wp_auto
  iunfold netAdder at Had
  wp_apply netJoin.wp_Add_of wp_Add antNetN _ γ.net q $$ [$Hsync $Had $Htok] as ⟨Had, Hdone⟩
  try wp_auto
  obtain ⟨j, hj⟩ := Hnf.2.2.2.2.2.1
  have hto : st.msg.To' = AntSim.nodeId j := by
    rw [← absMsgOf_dst' Hnf.2.2.2.2.1, hj]
  wp_apply wp_fork_tok_self $$ [Hm Htlb Hdone c m delay drop] as Htok
  · -- the network goroutine
    wp_auto
    wp_apply wp_Sleep
    wp_apply wp_isolatedNow c ns (W64 3) $$ [$Hpkg $Hro] as %iso -
    try wp_auto
    -- the isolation's drop, joined: `drop` holds some boolean after it
    wp_join iprop(∃ b : Bool, drop_ptr ↦ b ∗ m_ptr ↦ ml ∗
        msgPtsC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) st)
      at next with [drop m Hm iso] as ⟨%b, drop, m, Hm⟩
    · by_cases hiso : iso = W64 0
      · subst hiso
        simp only [_root_.decide_true, Bool.not_true]
        try wp_auto
        isplitr
        · ipureintro; trivial
        iexists _; iframe
      · simp only [hiso, _root_.decide_false, Bool.not_false]
        try wp_auto
        wp_apply wp_GetTo.1 ml _ _ _ st $$ [$Hpb $Hm] as Hm
        try wp_auto
        wp_if_destruct
        · try wp_auto
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _; iframe
        · wp_apply wp_GetFrom.1 ml _ _ _ st $$ [$Hpb $Hm] as Hm
          try wp_auto
          wp_if_destruct
          · try wp_auto
            isplitr
            · ipureintro; first | rfl | trivial
            iexists _; iframe
          · try wp_auto
            isplitr
            · ipureintro; first | rfl | trivial
            iexists _; iframe
    wp_apply wp_GetTo.1 ml _ _ _ st $$ [$Hpb $Hm] as Hm
    try wp_auto
    wp_apply wp_node c ns (W64 3) st.msg.To' $$ [$Hpkg $Hro]
    rw [hto, nodeOf_nodeId ns Hlen j]
    try wp_auto
    by_cases hnil : ns[j.val]! = null
    · rw [hnil]
      simp only [_root_.decide_true, Bool.not_true]
      try wp_auto
      wp_apply netJoin.wp_Done_of wp_Done antNetN _ γ.net $$ [$Hsync $Hdone] as Htok
      try wp_auto
      iframe Htok
    · simp only [hnil, _root_.decide_false, Bool.not_false]
      try wp_auto
      rcases b with _ | _
      rotate_left
      · simp only [Bool.not_true]
        try wp_auto
        wp_apply netJoin.wp_Done_of wp_Done antNetN _ γ.net $$ [$Hsync $Hdone] as Htok
        try wp_auto
        iframe Htok
      · simp only [Bool.not_false]
        try wp_auto
        ihave #Hnj := nodeRO_of γ ns j $$ [$Hn0 $Hn1 $Hn2]
        icases msgPtsC_msgPtsCC ml _ _ _ st $$ Hm with ⟨%cm', Hm, %Hcm'⟩
        wp_apply wp_deliver c γ (ns[j.val]!) j _ $$ [$Hpkg $Hc $Hnj Hm Htlb]
        · iunfold inputOk
          ileft
          isplitr
          · ipureintro; rfl
          iexists st, m
          iunfold netMsg
          iframe Htlb Hism Hsent
          isplitl [Hm]
          · isplitl [Hm]
            · iexists cm'; iframe Hm; ipureintro; exact Hcm'
            ipureintro; exact Hnf
          ipureintro; exact hj
        try wp_auto
        wp_apply netJoin.wp_Done_of wp_Done antNetN _ γ.net $$ [$Hsync $Hdone] as Htok
        try wp_auto
        iframe Htok
  iapply HΦ
  iunfold netAdder
  iframe Had Htok

end proof

end AntHarness
end EtcdGrove
end Perennial
