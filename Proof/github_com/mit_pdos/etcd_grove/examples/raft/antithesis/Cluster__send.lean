/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__send.lean`. The message is
frozen read-only (`msgPtsCC_send_freeze`); a forwarded proposal the mode does not forward returns at
once; otherwise the network goroutine (added to `netWg` with the caller's thread token, forked with
a fresh one) draws `k ≤ MaxDeliveries`, and for each delivery clones the message
(`cloneMsg.law`) into an in-flight message to its destination (`netMsg`/`netXMsg` from the
original's persistent facts, `inputOk_of_clone`); delivered no time, it reports the destination
unreachable to the sender (`inputOk`'s arm 7). A node of the cluster is one of `0 … N-1`
(`nodeOf_some`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__node
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.CloneMsgLaw
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A message's protocol reading is addressed to its `To`. -/
theorem absMsgOf_dst {st : MsgSt} {m : Msg} (H : absMsgOf st = some m) :
    m.dst = st.msg.To' := by
  unfold absMsgOf at H
  split at H
  · cases H
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 H; rfl
  · cases H; rfl

/-- A node `c.node(id)` finds is node `j` of id `id`, for some `j < N`. -/
theorem nodeOf_some (ns : List Loc) (N : Nat) (hl : ns.length = N) (id : w64)
    (h : nodeOf ns id ≠ null) : ∃ j : Fin N, nodeOf ns id = ns[j.val]! ∧ AntSim.nodeId j = id := by
  unfold nodeOf at *
  split at h
  · exact absurd rfl h
  · rename_i hc
    have h0 : id ≠ W64 0 := fun e => hc (Or.inl e)
    have h1 : uint.nat id ≤ ns.length := by have := fun e => hc (Or.inr e); omega
    have hpos : 1 ≤ uint.nat id := by
      rcases Nat.eq_zero_or_pos (uint.nat id) with e | e
      · exfalso; apply h0; word
      · exact e
    refine ⟨⟨uint.nat id - 1, by omega⟩, ?_, ?_⟩
    · simp only [hc, ↓reduceIte]
    · unfold AntSim.nodeId; simp only
      have : ((uint.nat id - 1 : Nat) : Int) + 1 = uint.Z id := by
        have : (uint.nat id : Int) = uint.Z id := by word
        omega
      rw [this]; word

/-- `InScope`'s deliveries: one, or two with duplication. -/
theorem maxDel_of_inScope {s : H.Scope} {m : H.Mode} (h : InScope s m) :
    m.MaxDeliveries' = W64 1 ∨ m.MaxDeliveries' = W64 2 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := h
  rcases h8 with h | ⟨-, h⟩ <;> simp [h]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [sync_sem : sync.Assumptions]

/-- **A clone of a sendable message to node `j`** (its `To`) is an input `j` takes (`inputOk`'s
arm 0), from the original's persistent facts. -/
theorem inputOk_of_clone (h_tlb : rnTermLB_persistent.law (GF := GF)) (γ : AntNames) (j : Fin γ.R.N) (st : MsgSt) (cm : MsgC) (inp : H.input)
    (hk : inp.kind' = W64 0) (hc : cm.model = st ∧ cm.csUfNil) (hj : AntSim.nodeId j = st.msg.To') :
    ((∃ m : Msg, ⌜NetFacts γ.R st m⌝ ∗ □ isMessage γ.raft.raftNames m ∗ rnTermLB γ.raft st.msg.Term' ∗
        sentW γ m) ∨
      (∃ x : XMsg, ⌜XNetFacts γ.R st x⌝ ∗ rnTermLB γ.raft st.msg.Term' ∗ xsentW γ x)) ∗
    msgPtsCC (GF := GF) inp.msg' (DFrac.own 1) (DFrac.own 1) true cm ⊢ |==> inputOk γ j inp := by
  haveI := h_tlb
  iintro ⟨(⟨%m, %hf, #Hism, #Htlb, #Hsent⟩ | ⟨%x, %hf, #Htlb, #Hsent⟩), Hl⟩
  · imod netMsg_of_clone γ inp.msg' st m cm hc hf $$ [$Hl $Hism $Htlb $Hsent] with Hn
    imodintro
    iunfold inputOk
    ileft
    isplitr
    · ipureintro; exact hk
    iexists st
    ileft
    iexists m
    iframe Hn
    ipureintro; rw [absMsgOf_dst hf.2.2.2.2.1, hj]
  · imod netXMsg_of_clone γ inp.msg' st x cm hc hf $$ [$Hl $Htlb $Hsent] with Hn
    imodintro
    iunfold inputOk
    ileft
    isplitr
    · ipureintro; exact hk
    iexists st
    iright
    iexists x
    iframe Hn
    ipureintro; rw [hf.2.2.2.2.1, hj]

theorem Cluster.send.wp_proof
    (wp_deliver : Cluster.deliver.spec (GF := GF) (hG := hG))
    (wp_node : Cluster.node.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG))
    (h_tlb : rnTermLB_persistent.law (GF := GF)) :
    Cluster.send.spec (GF := GF) (hG := hG) := by
  intro _ c γ ml st q
  haveI := h_tlb
  haveI : Persistent (sendFacts (GF := GF) γ st) := by unfold sendFacts; infer_instance
  wp_start as ⟨#Hc, Had, Htok, Hm, %Hss⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  ihave #Hro' := Hro
  iunfold clusterRO at Hro'
  icases Hro' with ⟨%nsl, %ivl, #Hn, #Hns, %HN, #Hmd, #Hiv, #Hivs⟩
  ihave Hmd' := Hmd
  iStructNamed Hmd'
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  iunfold sendMsg at Hm
  icases Hm with ⟨⟨%cm, Hm, %Hcm⟩, #Hf⟩
  imod msgPtsCC_send_freeze ml _ cm $$ Hm with #Hm
  have hN : γ.R.N = ns.length := by rw [Hmode.2.1, HN]
  wp_auto
  ihave HmC := msgPtsCC_msgPtsC ml _ _ _ cm Hcm.2 $$ Hm
  rw [Hcm.1]
  wp_apply wp_GetType.1 ml _ _ _ st $$ [$Hpb $HmC] as -
  wp_if_destruct
  try wp_auto
  rcases hF : γ.mode.Forward' with _ | _
  simp only [Bool.not_false]
  try wp_auto
  iapply HΦ
  iframe Had Htok
  all_goals try simp only [Bool.not_true]
  all_goals try wp_auto
  all_goals
    iunfold sendFacts at Hf
    icases Hf with (%Hprop | #Hf)
    · exfalso; obtain ⟨h1, h2⟩ := Hprop; first | exact Hif h1 | simp_all
    iunfold netAdder at Had
    wp_apply netJoin.wp_Add_of wp_Add antNetN _ γ.net q $$ [$Hsync $Had $Htok] as ⟨Had, Hdone⟩
    try wp_auto
    wp_apply wp_fork_tok_self $$ [Hdone c m] as Htok
    · -- the network goroutine
      wp_auto
      have hMD := maxDel_of_inScope Hmode.1
      wp_apply wp_below (γ.mode.MaxDeliveries' + W64 1) (by rcases hMD with h | h <;> rw [h] <;> decide)
        $$ [$Hpkg] as %k %Hk
      wp_apply wp_GetTo.1 ml _ _ _ st $$ [$Hpb $HmC] as -
      wp_apply wp_node c ns γ.mode st.msg.To' $$ [$Hpkg $Hro]
      wp_apply wp_GetFrom.1 ml _ _ _ st $$ [$Hpb $HmC] as -
      wp_apply wp_node c ns γ.mode st.msg.From' $$ [$Hpkg $Hro]
      ihave %Hres : ⌜st.resps = []⌝ $$ [Hf]
      · icases Hf with (⟨%_, %hf, -⟩ | ⟨%_, %hf, -⟩)
        · ipureintro; exact hf.1.resps
        · ipureintro; exact hf.2.1.resps
      have hcr : cm.resps = [] := by
        have := Hres; rw [← Hcm.1] at this; simpa [MsgC.model] using this
      wp_join with [c m k dst]
      · -- `dst` a node: `k` clones delivered
        have hdn : nodeOf ns st.msg.To' ≠ null := by simpa using Hif
        obtain ⟨jd, hjd, hid⟩ := nodeOf_some ns γ.R.N hN.symm _ hdn
        ihave #Hnd : nodeRO c γ (nodeOf ns st.msg.To') jd $$ []
        · rw [hjd]; iapply nodeRO_lookup; iexact Hnodes
        ihave IH : iprop(∃ jv : w64, "j" ∷ j_ptr ↦ jv ∗ "c" ∷ c_ptr ↦ c ∗ "m" ∷ m_ptr ↦ ml ∗
            "k" ∷ k_ptr ↦ k ∗ "dst" ∷ dst_ptr ↦ nodeOf ns st.msg.To') $$ [j c m k dst]
        · iexists _; iframe
        wp_for IH
        wp_if_destruct
        · wp_apply (cloneMsg_law_of wp_Clone) ml cm hcr $$ [$Hproto $Hm] as %l' Hl'
          try wp_auto
          imod inputOk_of_clone h_tlb γ jd st cm
            ({ kind' := W64 0, msg' := l', data' := slice.nil, to' := 0, ok' := false } : H.input)
            rfl Hcm hid $$ [$Hf $Hl'] with Hinp
          wp_apply wp_deliver c γ _ jd _ $$ [$Hpkg $Hc $Hnd $Hinp]
          try wp_auto
          wp_for_post
          iframe
          iexists _
          iframe
        · try wp_auto
          have hlt : ¬ uint.Z jv < uint.Z k := by intro h; apply Hif; simp [h]
          simp [hlt]
          iframe
      by_cases hsrc : nodeOf ns st.msg.From' = null
      · rw [hsrc]
        wp_auto
        wp_apply netJoin.wp_Done_of wp_Done antNetN _ γ.net $$ [$Hsync $Hdone] as Htok
        try wp_auto
        iframe
      · rw [decide_eq_false hsrc]
        wp_auto
        obtain ⟨js, hjs, -⟩ := nodeOf_some ns γ.R.N hN.symm _ hsrc
        ihave #Hns' : nodeRO c γ (nodeOf ns st.msg.From') js $$ []
        · rw [hjs]; iapply nodeRO_lookup; iexact Hnodes
        wp_join with [c m k src]
        · wp_apply wp_GetTo.1 ml _ _ _ st $$ [$Hpb $HmC] as -
          wp_apply wp_deliver c γ _ js _ $$ [$Hpkg $Hc $Hns']
          · iunfold inputOk
            iright; iright; iright; iright; iright
            ipureintro; rfl
          try wp_auto
          wp_join_done
        rw [decide_eq_false hsrc]
        wp_auto
        rw [Hss]
        wp_auto
        wp_apply netJoin.wp_Done_of wp_Done antNetN _ γ.net $$ [$Hsync $Hdone] as Htok
        try wp_auto
        iframe
    iapply HΦ
    iunfold netAdder
    iframe Had Htok

end proof

end AntHarness
end EtcdGrove
end Perennial
