/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Cluster__send.lean`. Lean-first
(no Rocq counterpart).

`c.net.Add(1)` deposits the caller's thread token (`netJoin.wp_Add_of`); the `go` gives the caller a
fresh one (`wp_fork_tok_self`). The goroutine: its deferred `c.net.Done()` hands its slot's token
back (`netJoin.wp_Done_of`), the token it exits with. Before stepping, the message's token says it is
no `MsgSnap` (`trTok_type`, at a traced cluster), so both `ReportSnapshot` branches are dead. The
destination `c.replica(m.GetTo())` is the replica of that id (`replicaOf`); for a delivered message
`stepIn_intro` (with the token) makes the message `node.Step`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__send
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import Spec.context.WithTimeoutBackground
public import Perennial.Proof.time.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 ProbeA

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

omit [StorageModel GF] package_sem sem in
/-- A replica found by `replicaOf` is the slice's element at its id's position. -/
theorem replicaOf_some (rs : List Loc) (id : w64) (h : replicaOf rs id ≠ null) :
    rs[uint.nat id - 1]? = some (replicaOf rs id) ∧ W64 ((uint.nat id - 1 : Nat) + 1) = id := by
  unfold replicaOf at h ⊢
  by_cases hc : uint.Z id = 0 ∨ (rs.length : Int) < uint.Z id
  · simp only [hc, ↓reduceIte] at h; exact absurd rfl h
  · simp only [hc, ↓reduceIte] at h ⊢
    have hlt : uint.nat id - 1 < rs.length := by word
    rw [List.getElem?_eq_getElem hlt]
    refine ⟨rfl, ?_⟩
    have : uint.Z id ≠ 0 := fun h' => hc (.inl h')
    word

theorem Cluster.send.wp_proof
    (wp_replica : Cluster.replica.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_WT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_Step : node.Step.spec (GF := GF) (hG := hG))
    (wp_RU : node.ReportUnreachable.spec (GF := GF) (hG := hG)) :
    Cluster.send.spec (GF := GF) (hG := hG) := by
  intro _ c W src sid ml st delay drop q
  wp_start as ⟨#Hw, #Hsrc, Hm, #Hs, Hcr, Htok, Had, Htt⟩
  ihave #Hw' := Hw
  iunfold tcWorld at Hw'
  icases Hw' with ⟨#HcTick, #HcMax, #HcDrop, #HcSnap, %Hpure, #Hstop, #Hsc, #Hrs, #Hnodes, #Hnj, #Hiso, #HcP, #HcD, #HcX, #HcR,
    #HcC, #Hcl, #Hops, #Hpol, #Hsn, #Hboot⟩
  ihave #Hsy : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  -- the message is no `MsgSnap` (its token, at the traced cluster)
  icases trTok_type W.cl st $$ Htok with ⟨Htok, %Hty0⟩
  have Hty : st.msg.Type' ≠ W32 7 := Hty0 (by rw [Hpure.2.2.1]; simp)
  ihave #Hsrc' := Hsrc
  iunfold repNode at Hsrc'
  icases Hsrc' with ⟨%ns, #Hsfield, #Hsn0⟩
  wp_auto
  wp_apply netJoin.wp_Add_of sync.WaitGroup.wp_Add tcNetN _ W.nj q $$ [$Hsy $Had $Htt]
    as ⟨Had, Hdone⟩
  try wp_auto
  wp_apply wp_fork_tok_self $$ [-Had HΦ] [Had HΦ]
  · try inext
    wp_auto
    wp_apply wp_with_defer as %defer defer
    try wp_auto
    wp_apply time.wp_Sleep
    wp_apply wp_GetTo.1 ml (DFrac.own 1) (DFrac.own 1) true _ $$ [$Hm] as Hm
    wp_apply wp_replica c W.rs _ $$ [$Hpkg $Hrs] as %dst %Hdst
    try wp_auto
    wp_apply wp_GetType.1 ml (DFrac.own 1) (DFrac.own 1) true _ $$ [$Hm] as Hm
    wp_apply wp_GetTo.1 ml (DFrac.own 1) (DFrac.own 1) true _ $$ [$Hm] as Hm
    try wp_auto
    wp_apply iso_wp_Load _ $$ [] as %iso -
    · iframe Hiso
    try wp_auto
    wp_join iprop(∃ d : Bool, drop_ptr ↦ d ∗ msgPtsC ml (DFrac.own 1) (DFrac.own 1) true
        ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗ iso_ptr ↦ iso ∗ to_ptr ↦ st.msg.To' ∗ m_ptr ↦ ml)
      with [drop Hm iso to m] as ⟨%d, drop, Hm, iso, to, m⟩
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_join_done
      · wp_apply wp_GetFrom.1 ml (DFrac.own 1) (DFrac.own 1) true _ $$ [$Hm] as Hm
        try wp_auto
        wp_if_destruct
        · try wp_auto
          wp_join_done
        · try wp_auto
          wp_join_done
    · try wp_auto
      wp_join iprop(∃ dv : Bool, delivered_ptr ↦ dv ∗ dst_ptr ↦ dst ∗ drop_ptr ↦ d ∗ m_ptr ↦ ml)
        with [delivered dst drop m Hm Hcr Htok] as ⟨%dv, delivered, dst, drop, m⟩
      · cases d
        · -- stepped into the destination's node
          obtain ⟨Hlook, Hid⟩ := replicaOf_some W.rs st.msg.To' (by rw [← Hdst]; exact Hif)
          rw [← Hdst] at Hlook
          ihave #Hdn := BigSepL.bigSepL_lookup
            (Φ := fun i r => repNode (GF := GF) W.cl r (W64 (i + 1))) Hlook $$ Hnodes
          rw [Hid]
          iunfold repNode at Hdn
          icases Hdn with ⟨%nd, #Hdf, #Hdnode⟩
          ihave #Hcx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
          · iPkgInit
          ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
          · iapply context.isClosedchanInit_of_init
            iexact Hcx
          try wp_auto
          wp_apply context.wp_Background
          wp_apply wp_WT _ $$ [$Hcx $Hcci] as %ctx %cd %cancel ⟨#Hcancel, #Hctx⟩
          try wp_auto
          ihave #Hloc := snapLocalMsg_noDir (GF := GF) W.cl st.msg.To'
            (by rw [Hpure.2.2.2.1]) st
          imod stepIn_intro W.cl tcRaftN st.msg.To' ml sid st rfl $$ [Hm Hcr Htok] with Hstep
          · iframe Hs Hm Hcr Hloc Htok
          wp_apply wp_Step nd W.cl tcRaftN st.msg.To' ml ctx cd $$ [Hstep] as %err -
          · iframe Hdnode Hstep
            iunfold nodeCtx
            iright; iexact Hctx
          cases err <;>
          · try wp_auto
            wp_apply Hcancel
            try wp_auto
            wp_join_done
        · try wp_auto
          wp_join_done
      · try wp_auto
        cases dv
        · -- not delivered
          try wp_auto
          wp_apply ctr_wp_Add _ _ $$ [$HcX] as %_ -
          try wp_auto
          wp_apply wp_RU ns W.cl tcRaftN sid _ $$ [$Hsn0]
          try wp_auto
          rw [decide_eq_false Hty]
          try wp_auto
          wp_apply netJoin.wp_Done_of sync.WaitGroup.wp_Done tcNetN _ W.nj $$ [$Hsy $Hdone] as Htt
          try wp_auto
          iframe Htt
        · try wp_auto
          wp_apply ctr_wp_Add _ _ $$ [$HcD] as %_ -
          try wp_auto
          rw [decide_eq_false Hty]
          try wp_auto
          wp_apply netJoin.wp_Done_of sync.WaitGroup.wp_Done tcNetN _ W.nj $$ [$Hsy $Hdone] as Htt
          try wp_auto
          iframe Htt
  · try inext
    iintro Htt
    wp_auto
    iapply HΦ
    iframe Had Htt

end proof

end TraceCheck
end EtcdGrove
end Perennial
