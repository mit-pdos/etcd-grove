/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__reportCause.lean`: with the
cause cell set (the drain's `recv` not reported yet), the `recv` report is recorded, its atomic update
(`recv_au`) opening the run's invariant (open: the run is not over, the caller holds its `live`
token) and taking the checker's step `antSim_recv`, the view's `told` set (`antRun_recv`); the cell
is `nil` after. With the cell `nil`, nothing.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Recv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The new stream's pure facts -/

section pure
variable [GooseExts]

private theorem weight_sum (evs : List AntCheck.Event) :
    (evs.map AntCheck.Event.weight).sum = (evs.map AntCheck.Event.size).sum + 2 * evs.length := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, AntCheck.Event.weight, ih]
    omega

/-- A `recv` report carries no entry that changes a name. -/
private theorem chgOk_evRecv (id : w64) (m : Msg) : (AntSim.evRecv id m).ChgOk 0 := by
  intro l hl e he
  simp only [AntSim.evRecv, AntCheck.Event.entryLists, AntSim.msgOf, AntCheck.Msg.entryLists,
    Option.getD_none, Option.map_some, Option.getD_some, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp at he
  · simp only [AntSim.logOf, List.mem_map] at he
    obtain ⟨x, -, rfl⟩ := he
    unfold AntSim.entOf
    split <;> simp [AntCheck.Entry.chgSize]

/-- **The run after a `recv` report**: the checker's step (`antSim_recv`) and the stream's bounds
(the receipts' fit, the report's numbers, no configuration change). -/
private theorem antRun_recv (GF : BundledGFunctors) [ReceiptGS GF] {evs : List AntCheck.Event}
    {S : AntCheck.State} {V : Fin 3 → AntSim.NodeView} {net : List Msg} {G : AntSim.RaftFacts}
    {j : Fin 3} {m : Msg}
    (hR : AntRun evs S V net) (hL : AntSim.RaftLaws G) (hG : AntSim.GlobalOk S net G)
    (hlogs : ∀ i : Fin 3, (V i).ps.log ∈ G.logs)
    (hm : m ∈ net) (hd : m.dst = AntSim.nodeId j) (hc : (V j).cause = some m)
    (hnums : (AntSim.evRecv (AntSim.nodeId j) m).NumsOk)
    (hfit : Stream.Fits GF (evs ++ [AntSim.evRecv (AntSim.nodeId j) m])) (hrf : antRunFits GF) :
    ∃ S', AntRun (evs ++ [AntSim.evRecv (AntSim.nodeId j) m]) S'
        (AntSim.setV V j { V j with told := true }) net ∧
      AntSim.GlobalOk S' net G ∧ ∀ i : Fin 3, (AntSim.setV V j { V j with told := true } i).ps.log ∈ G.logs := by
  obtain ⟨hP, hA, hB, -, hC⟩ := hR
  obtain ⟨S', hP', hA', hG'⟩ := AntSim.antSim_recv S V net evs G j m hP hA hL hG hm hd hc
  refine ⟨S', ⟨hP', hA', ?_, ?_, ?_⟩, hG', ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold Stream.Fits at hfit
      unfold antRunFits at hrf
      rw [weight_sum] at hfit
      simp only [List.length_append, List.length_singleton, AntCheck.numBound] at hfit ⊢
      push_cast
      omega
    · intro ev hev
      rcases List.mem_append.1 hev with h | h
      · exact hB.2 ev h
      · rw [List.mem_singleton.1 h]; exact hnums
  · refine ⟨0, ?_, ?_⟩
    · intro ev hev
      rcases List.mem_append.1 hev with h | h
      · exact hC ev h
      · rw [List.mem_singleton.1 h]; exact chgOk_evRecv _ m
    · rw [AntSim.cfg3_initVoters, AntSim.namesL_three]
      simp
  · intro ev hev
    rcases List.mem_append.1 hev with h | h
    · exact hC ev h
    · rw [List.mem_singleton.1 h]; exact chgOk_evRecv _ m
  · intro i
    unfold AntSim.setV
    split
    · subst_vars; exact hlogs _
    · exact hlogs i

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **The `recv` report's atomic update**: the run's invariant opened (open: the caller's `live`
token excludes the run being over), the stream's half given to the recorder, and at the commit the
checker's step (`antRun_recv`) taken, the view's `told` set. -/
private theorem recv_au (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (m : Msg)
    (hc : v.cause = some m) (hd : m.dst = AntSim.nodeId j)
    (hnums : (AntSim.evRecv (AntSim.nodeId j) m).NumsOk) (hrf : antRunFits GF) :
    iprop(inv antN (antInv (GF := GF) γ) ∗ sentW γ m) ∗ iprop(viewFrag γ j v ∗ nodeLive γ j) ⊢
      AU <{ ∃∃ evs, recAuth (GF := GF) γ.strm evs }> @ ⊤, ∅
        <{ recAuth γ.strm (evs ++ [AntSim.evRecv (AntSim.nodeId j) m]) ∗
            ⌜Stream.Fits GF (evs ++ [AntSim.evRecv (AntSim.nodeId j) m])⌝,
          COMM viewFrag γ j { v with told := true } ∗ nodeLive γ j }> := by
  refine sep_and.trans (aupd_intro ?_)
  iintro ⟨⟨#Hinv, #Hs⟩, ⟨Hv, Hl⟩⟩
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %G, Hstr, H0, H1, H2, Hnet, %Hpure, #HF⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists ⟨evs, ⟨⟩⟩
    simp only [Std.Tele.app]
    unfold recAuth
    iframe Hstr
    isplit
    · iintro Hstr
      imod Hmask with -
      imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
      · inext
        iunfold antInv
        ileft
        iunfold antOpen
        iexists evs, S, V, net, G
        iframe Hstr H0 H1 H2 Hnet HF
        ipureintro; exact Hpure
      imodintro
      iframe Hv Hl
    · iintro %y ⟨Hstr, %Hfit⟩
      imod Hmask with -
      ihave #Hs' := Hs
      iunfold sentW at Hs'
      icases Hs' with ⟨%i, #Hidx⟩
      ihave %Hlk := mono_list_auth_idx_lookup (GF := GF) γ.sent 1 net i m $$ Hnet Hidx
      have hm : m ∈ net := List.mem_of_getElem? Hlk
      imod view_update _ γ j V v { v with told := true } $$ [Hv H0 H1 H2] with ⟨%HVj, Hv, H0, H1, H2⟩
      · iframe Hv H0 H1 H2
      obtain ⟨S', hR', hG', hlogs'⟩ := antRun_recv GF Hpure.1 Hpure.2.1 Hpure.2.2.1 Hpure.2.2.2 hm hd
        (by rw [HVj]; exact hc) hnums Hfit hrf
      rw [HVj] at hR' hlogs'
      imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
      · inext
        iunfold antInv
        ileft
        iunfold antOpen
        iexists evs ++ [AntSim.evRecv (AntSim.nodeId j) m], S',
          AntSim.setV V j { v with told := true }, net, G
        iframe Hstr H0 H1 H2 Hnet HF
        ipureintro; exact ⟨hR', Hpure.2.1, hG', hlogs'⟩
      imodintro
      iframe Hv Hl
  · iexfalso
    iapply nodeLive_over γ j
    iframe Hl Hover

theorem Cluster.reportCause.wp_proof
    (wp_record : Recorder.record.spec (GF := GF) (hG := hG)) :
    Cluster.reportCause.spec (GF := GF) (hG := hG) := by
  intro c γ n j v cl
  by_cases hp : v.byE = go!"recv" ∧ v.told = false
  · have hco : causeOwn (GF := GF) γ j v cl = iprop(∃ (m : Msg) (g : AntCheck.G.Msg),
        ⌜v.cause = some m ∧ m.dst = AntSim.nodeId j ∧ (AntSim.evRecv (AntSim.nodeId j) m).NumsOk⌝ ∗
        cl ↦ g ∗ AntCheck.msgRO g (AntSim.msgOf m (AntSim.nodeId j)) ∗ sentW γ m ∗
        ⧗ (AntSim.evRecv (AntSim.nodeId j) m).weight) := by
      unfold causeOwn; simp only [hp, and_self, ↓reduceIte]
    have hrv : reportedView v = { v with told := true } := by
      unfold reportedView; simp only [hp, and_self, ↓reduceIte]
    rw [hco, hrv]
    wp_start as ⟨#Hc, #Hn, Hcell, ⟨%m, %g, %Hm, Hg, #Hmsg, #Hs, Hrc⟩, Hv, Hl⟩
    iunfold antCluster at Hc
    icases Hc with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, #Hr, #Hrec, #Hro, %Hlen, #Hn0, #Hn1, #Hn2,
      #Hstop, #Hbc, #Hnj, #Hinv, %Hfits⟩
    iunfold nodeRO at Hn
    icases Hn with ⟨%ch, #Hid, #Hname, #Hin, #Hbag⟩
    ihave %Hnn := typedPointsto_not_null $$ Hg
    wp_auto
    simp only [Hnn, _root_.decide_false, Bool.not_false]
    try wp_auto
    ipersist «$a0»
    ihave #Hev : AntCheck.eventRO «$a0_ptr» (AntSim.evRecv (AntSim.nodeId j) m) $$ []
    · iunfold AntCheck.eventRO
      iexists _
      iframe «$a0»
      simp only [AntSim.evRecv, AntCheck.fieldRO]
      isplitr
      · ipureintro
        simp only [AntCheck.fieldRel, AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy,
          AntCheck.fRole, AntCheck.fTerm, AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst,
          AntCheck.fLastIndex, AntCheck.fLastTerm, AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW,
          AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
        and_intros <;> first | rfl | decide
      simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing,
        AntCheck.fMsg, AntCheck.fCause]
      iframe Hmsg
      ipureintro
      and_intros <;> decide
    ihave HAU := recv_au γ j v m Hm.1 Hm.2.1 Hm.2.2 Hfits $$ [Hv Hl]
    · iframe Hinv Hs Hv Hl
    wp_apply wp_record γ.strm r «$a0_ptr» (AntSim.evRecv (AntSim.nodeId j) m) _
      $$ [$Hpkg $Hrec $Hev $Hrc $HAU] as ⟨Hv, Hl⟩
    iapply HΦ
    iframe Hcell Hv Hl
    unfold causeOwn
    simp only [Bool.true_eq_false, and_false, ↓reduceIte]
    ipureintro; trivial
  · have hco : causeOwn (GF := GF) γ j v cl = iprop(⌜cl = null⌝) := by
      unfold causeOwn; simp only [hp, ↓reduceIte]
    have hrv : reportedView v = v := by
      unfold reportedView; simp only [hp, ↓reduceIte]
    rw [hco, hrv]
    wp_start as ⟨#Hc, #Hn, Hcell, %Hnil, Hv, Hl⟩
    subst Hnil
    wp_auto
    iapply HΦ
    iframe Hcell Hv Hl
    unfold causeOwn
    simp only [hp, ↓reduceIte]
    ipureintro; trivial

end proof

end AntHarness
end EtcdGrove
end Perennial
