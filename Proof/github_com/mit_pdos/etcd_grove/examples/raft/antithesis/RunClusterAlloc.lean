/-
Lean-first (no Rocq counterpart). #33 S4, `RunCluster`'s proof: **the run's ghost state and its
start**, what `RunCluster.wp_proof` (`RunCluster.lean`) allocates and establishes before its node
goroutines run:
- **raft's cluster**, through `clusterAllocFacts.law`: raft's `cluster_alloc` at an empty bootstrap
  log with the facts about the names `nodeRaft` states (the configuration the voters, no bootstrap
  log, raft's namespace `N.@"raft"`, untraced, no data bound). An **interim law** (a hypothesis of
  `RunCluster.wp_proof`, passed by the `Link`): raft's allocation has these facts
  (`cluster_alloc_dec_impl`'s `Hcfg`, `HbootL`, `HNs`) but does not export them yet; once it does,
  the law is proved from it.
- **the run's names** (`antGhosts_alloc`): the stream's ghost variable, the three views (at
  `antView0`, the boot drain's view: a fresh node, `by = boot`), the three `live` tokens, the sent
  list;
- **the invariant** (`antInv_alloc`): open, at the empty stream, the views `antView0`, nothing sent,
  raft's facts `antG0` (the empty log certified and committed: `rawNode_logRecs`,
  `rawNode_committed` of the first node), through `antSim_init`;
- **a node at its boot drain** (`nodeOwn_boot`): `NewRawNode`'s post, the node's fields and its
  storage, the view and the token, at `.loop [] pInit` (`Reach.stay`);
- **the boot report** (`boot_step`, `report_au`'s step): `antSim_boot`;
- **the run's end** (`antInv_close`): the three tokens back, the invariant swapped to its closed
  arm, the stream out (accepted: `Prefix.accepts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunClusterStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.PropMint
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReports
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Boot
public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The pure start -/

section pure
variable [GooseExts]

/-- **A node's view at its boot drain**: a fresh node (`pInit`), nothing delivered, idle, the drain's
`by` `boot`. -/
def antView0 : AntSim.NodeView := { ps := pInit, delivered := [], byE := go!"boot" }

/-- **Raft's facts at the start**: the empty log, certified and committed. -/
def antG0 : AntSim.RaftFacts := ⟨[], [], [[]], [], [], []⟩

theorem pInit_PInit : AntSim.PInit pInit := by
  unfold AntSim.PInit
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem antView0_ok :
    AntSim.PInit antView0.ps ∧ antView0.delivered = [] ∧ antView0.Idle ∧ antView0.told = false ∧
      antView0.cause = none :=
  ⟨pInit_PInit, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩

theorem antView0_log : antView0.ps.log = [] := rfl

theorem antG0_laws : AntSim.RaftLaws antG0 := by
  unfold AntSim.RaftLaws antG0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [AntSim.CampTermsOk]

theorem antView0_normal : ViewNormal antView0 := by
  refine ⟨?_, ?_⟩
  · intro e he; simp [antView0_log] at he
  · intro m hm; cases hm

/-- **The run's pure start**: the checker at its initial state, related to the three views `antView0`
and nothing sent, raft's facts `antG0`. -/
theorem antRun0 : ∃ S : AntCheck.State,
    AntRun [] S (fun _ => antView0) [] ∧ AntSim.RaftLaws antG0 ∧ AntSim.GlobalOk S [] antG0 ∧
      ∀ j : Fin 3, ((fun _ => antView0) j : AntSim.NodeView).ps.log ∈ antG0.logs := by
  obtain ⟨S, hP, hA, hG⟩ := AntSim.antSim_init (fun _ => antView0) (fun _ => antView0_ok)
  refine ⟨S, ⟨hP, hA, ?_, ?_, ?_⟩, antG0_laws, hG antG0 (by simp [antG0]), ?_⟩
  · refine ⟨?_, ?_⟩
    · simp [AntCheck.numBound]
    · intro ev hev; cases hev
  · refine ⟨0, ?_, ?_⟩
    · intro ev hev; cases hev
    · simp [AntSim.cfg3_initVoters, AntSim.namesL_three]
  · intro ev hev; cases hev
  · intro j; simp [antG0, antView0_log]

/-- **The boot report's step** (`report_au`'s, the view unchanged, nothing sent): `antSim_boot`. -/
theorem boot_step (GF : BundledGFunctors) [ReceiptGS GF] (hrf : antRunFits GF) (j : Fin 3) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → AntSim.NodeView)
      (net : List Msg) (G : AntSim.RaftFacts),
      AntRun evs S V net → AntSim.RaftLaws G → AntSim.GlobalOk S net G →
      (∀ i : Fin 3, (V i).ps.log ∈ G.logs) → V j = antView0 → (fun _ => True) G → [] <+: net →
      Stream.Fits GF (evs ++ [AntSim.evBoot (AntSim.nodeId j)]) →
      ∃ S', AntRun (evs ++ [AntSim.evBoot (AntSim.nodeId j)]) S' (AntSim.setV V j antView0)
          (net ++ []) ∧
        AntSim.GlobalOk S' (net ++ []) G ∧ antView0.ps.log ∈ G.logs := by
  intro evs S V net G hR hL hG hlogs hV _ _ hfit
  have hset : AntSim.setV V j antView0 = V := by
    funext i; unfold AntSim.setV; split
    · next h => subst h; exact hV.symm
    · rfl
  obtain ⟨hpi, hdel, hidle, htold, -⟩ := antView0_ok
  rw [← hV] at hpi hdel hidle htold
  obtain ⟨S', hP', hA', hG'⟩ := AntSim.antSim_boot S V net evs G j hR.1 hR.2.1 hL hG hpi hdel hidle
    htold
  refine ⟨S', ?_, by rw [List.append_nil]; exact hG', ?_⟩
  · rw [hset, List.append_nil]
    refine antRun_snoc GF hR hP' hA' ?_ ?_ hfit hrf
    · unfold AntSim.evBoot AntCheck.Event.NumsOk
      simp [AntCheck.optNumOk, AntCheck.numOk, AntCheck.numBound]
    · unfold AntSim.evBoot AntCheck.Event.ChgOk
      simp [AntCheck.Event.entryLists]
  · rw [← hV]; exact hlogs j

end pure

/-! ## Raft's allocation, with the names' facts (interim law) -/

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **Raft's `cluster_alloc` at an empty bootstrap log, with the names' facts** `nodeRaft` states
(interim; see the file header): the configuration the voters `vs`, no bootstrap log, raft's
namespace `N.@"raft"`, untraced and with no data bound at the names. -/
abbrev clusterAllocFacts.law : Prop :=
  ∀ (N : Namespace) (vs : List w64) (E : CoPset),
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ⊢ |={E}=> ∃ γ : Cluster,
      ⌜γ.dup = false ∧ γ.bootLen = 0 ∧ γ.maxData = none ∧ ¬ clusterNoSnap γ ∧
        Cluster.trace γ = none⌝ ∗
      ⌜γ.raftNames.reCfg = GMap.listToSet vs ∧ γ.raftNames.reBoot = [] ∧
        γ.raftNames.reNs = N.@"raft" ∧ γ.raftNames.reTrace = none ∧ γ.raftNames.maxData = none⌝ ∗
      ownCommittedOps (GF := GF) γ [] ∗ isCluster γ N ∗
      confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗
      [∗list] id ∈ vs, raftState γ id RaftState.init ∗ nodeVacant γ id

end law

/-! ## The run's names and invariant -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- Three values as a function of `Fin 3`. -/
def fin3 {α : Type} (a b c : α) : Fin 3 → α := fun j => if j = 0 then a else if j = 1 then b else c

@[simp] theorem fin3_0 {α : Type} (a b c : α) : fin3 a b c 0 = a := rfl
@[simp] theorem fin3_1 {α : Type} (a b c : α) : fin3 a b c 1 = b := rfl
@[simp] theorem fin3_2 {α : Type} (a b c : α) : fin3 a b c 2 = c := rfl

/-- **The run's own ghost names** (see the file header): the stream (both halves at the empty
stream), each view (both halves at `antView0`), each `live` token, the sent list (empty). -/
theorem antGhosts_alloc :
    ⊢ |==> ∃ (strm sent : GName) (view live : Fin 3 → GName),
      ghostVar (GF := GF) strm (1 : Qp).half ([] : List AntCheck.Event) ∗
      ghostVar strm (1 : Qp).half ([] : List AntCheck.Event) ∗
      ghostVar (view 0) (1 : Qp).half antView0 ∗ ghostVar (view 0) (1 : Qp).half antView0 ∗
      ghostVar (view 1) (1 : Qp).half antView0 ∗ ghostVar (view 1) (1 : Qp).half antView0 ∗
      ghostVar (view 2) (1 : Qp).half antView0 ∗ ghostVar (view 2) (1 : Qp).half antView0 ∗
      dghostVar (live 0) (DFrac.own 1) () ∗ dghostVar (live 1) (DFrac.own 1) () ∗
      dghostVar (live 2) (DFrac.own 1) () ∗
      monoListAuthOwn sent 1 ([] : List Msg) ∗ monoListLbOwn sent ([] : List Msg) := by
  imod ghostVar_alloc (GF := GF) ([] : List AntCheck.Event) with ⟨%strm, Hs⟩
  imod ghostVar_alloc (GF := GF) antView0 with ⟨%v0, H0⟩
  imod ghostVar_alloc (GF := GF) antView0 with ⟨%v1, H1⟩
  imod ghostVar_alloc (GF := GF) antView0 with ⟨%v2, H2⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%l0, L0⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%l1, L1⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%l2, L2⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Msg) with ⟨%sent, Ha, Hlb⟩
  icases (ghostVar_split_half (GF := GF) strm 1 ([] : List AntCheck.Event)).1 $$ Hs with ⟨Hs1, Hs2⟩
  icases (ghostVar_split_half (GF := GF) v0 1 antView0).1 $$ H0 with ⟨H0a, H0b⟩
  icases (ghostVar_split_half (GF := GF) v1 1 antView0).1 $$ H1 with ⟨H1a, H1b⟩
  icases (ghostVar_split_half (GF := GF) v2 1 antView0).1 $$ H2 with ⟨H2a, H2b⟩
  imodintro
  iexists strm, sent, fin3 v0 v1 v2, fin3 l0 l1 l2
  simp only [fin3_0, fin3_1, fin3_2]
  iframe

/-- The empty log's facts give raft's facts `antG0`. -/
theorem raftFactsOwn_G0 (γ : RaftNames) :
    ⊢ isCommitted (GF := GF) γ [] -∗ logRecs γ base0 [] -∗ raftFactsOwn γ antG0 := by
  iintro #Hc #Hl
  unfold raftFactsOwn antG0
  simp only [BigSepL.bigSepL_nil, BigSepL.bigSepL_cons]
  iframe Hc Hl
  isplitr; · iempintro
  isplitr; · iempintro
  isplitr
  · isplitr; · ipureintro; intro k e h; simp at h
    iempintro
  isplitr; · iempintro
  iempintro

/-- **The run's invariant, allocated open** (see the file header). -/
theorem antInv_alloc (γ : AntNames) (E : CoPset) :
    ⊢ ghostVar (GF := GF) γ.strm (1 : Qp).half ([] : List AntCheck.Event) -∗
      ghostVar (γ.view 0) (1 : Qp).half antView0 -∗ ghostVar (γ.view 1) (1 : Qp).half antView0 -∗
      ghostVar (γ.view 2) (1 : Qp).half antView0 -∗ monoListAuthOwn γ.sent 1 ([] : List Msg) -∗
      isCommitted γ.raft.raftNames [] -∗ logRecs γ.raft.raftNames base0 [] ={E}=∗
      inv antN (antInv γ) := by
  iintro Hs H0 H1 H2 Ha #Hc #Hl
  obtain ⟨S, hR, hL, hG, hlogs⟩ := antRun0
  iapply inv_alloc antN E
  inext
  iunfold antInv
  ileft
  iunfold antOpen
  iexists [], S, (fun _ => antView0), [], antG0
  iframe Hs H0 H1 H2 Ha
  isplitr
  · ipureintro; exact ⟨hR, hL, hG, hlogs⟩
  iapply raftFactsOwn_G0 $$ Hc Hl

/-- **The run's end** (see the file header): with the three `live` tokens, the invariant's stream
taken out, accepted, and the invariant closed. -/
theorem antInv_close (γ : AntNames) :
    ⊢ inv antN (antInv (GF := GF) γ) -∗ nodeLive γ 0 -∗ nodeLive γ 1 -∗ nodeLive γ 2 ={⊤}=∗
      ∃ evs : List AntCheck.Event, recDone γ.strm evs ∗
        ⌜AntCheck.Accepts AntSim.cfg3 evs ∧ AntCheck.Stream.Bounded evs ∧
          AntCheck.Stream.ConfBounded AntSim.cfg3 evs⌝ := by
  iintro #Hinv L0 L1 L2
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %G, Hs, -, -, -, -, %Hp, -⟩
    obtain ⟨⟨hP, -, hB, hC, -⟩, -⟩ := Hp
    imod Hclose $$ [L0 L1 L2] with -
    · inext; iunfold antInv; iright; iframe L0 L1 L2
    imodintro
    iexists evs
    unfold recDone recAuth
    iframe Hs
    ipureintro; exact ⟨hP.accepts, hB, hC⟩
  · iexfalso
    iapply nodeLive_over (GF := GF) γ 0 $$ [L0 Hover]
    iframe L0 Hover

end ghost

/-! ## A node at its boot drain -/

section node
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [AntStor GF]
attribute [local instance] antStorageModelNC

/-- **Node `j` at its boot drain** (see the file header): what `NewRawNode` gave (the node at
`pInit`, its generation view and batch slot, its durable state at `RaftState.init`), its storage
(registered, its lock, its hard state's metadata), its fields as the composite literal and the boot
drain leave them, its view at `antView0` and its token. -/
theorem nodeOwn_boot (h_open : raftState_open_rn.law (GF := GF)) (c : Loc) (γ : AntNames)
    (j : Fin 3) (n rn ms si : Loc) (γs : MemStorNames) (sn : StorNames) (x : CrashNames) (g : Nat)
    (hfacts : γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = AntSim.voters3 ∧
      γ.raft.raftNames.maxData = none ∧ γ.raft.raftNames.reBoot = [] ∧
      (↑(raftN γ.raft.raftNames) : CoPset) ⊆ ⊤ \ ↑antN)
    (hsz : γs.sz = false) :
    ⊢ n.[H.node, go!"rn"] ↦□ rn -∗ n.[H.node, go!"storage"] ↦□ ms -∗
      bootStorRec si ms [W64 1, W64 2, W64 3] -∗ antStorRec si ms γs -∗ memStorLock ms γs -∗
      memStorMeta ms γs hsZero -∗
      rawNode γ.raft.raftNames rn (AntSim.nodeId j)
        (rawNodeRestarted γ.raft [] (antStorIface si) sn hsZero RaftState.init
          (Membership.simple AntSim.voters3) 0) pInit [] 0 -∗
      genView γ.raft.raftNames (AntSim.nodeId j) x 1 g -∗
      slotFree γ.raft.raftNames (AntSim.nodeId j) g -∗
      raftState γ.raft (AntSim.nodeId j) RaftState.init -∗
      n.[H.node, go!"role"] ↦ go!"follower" -∗ n.[H.node, go!"term"] ↦ W64 0 -∗
      n.[H.node, go!"vote"] ↦ W64 0 -∗ n.[H.node, go!"commit"] ↦ W64 0 -∗
      n.[H.node, go!"applied"] ↦ W64 0 -∗ n.[H.node, go!"cause"] ↦ null -∗
      viewFrag γ j antView0 -∗ nodeLive γ j -∗ sentLb γ [] -∗
      nodeOwn c γ j n antView0 (.loop [] pInit) := by
  iintro #Hrn #Hst #Hboot #Hrec #Hlock Hmeta Hr Hgv Hsf Hrs Hrole Hterm Hvote Hcommit Happ Hcause
    Hv Hl #Hlb
  icases (h_open γ.raft (AntSim.nodeId j) RaftState.init).1 $$ Hrs with ⟨Hdur, Htlb, Hbud⟩
  iunfold nodeOwn
  iexists rn, ms, si,
    rawNodeRestarted γ.raft [] (antStorIface si) sn hsZero RaftState.init
      (Membership.simple AntSim.voters3) 0,
    pInit, [], 0, null, W64 0
  rw [show antView0.ps.term = W64 0 from rfl, show antView0.ps.vote = W64 0 from rfl,
    show antView0.ps.commit = W64 0 from rfl]
  iframe Hrn Hst Hr Hterm Hvote Hcommit Happ Hcause Hv Hl
  isplitl [Hmeta]
  · iunfold nodeStor
    iframe Hboot
    iexists γs
    iframe Hlock Hmeta
    isplitl []
    · ihave Hb := antNC_bridge si ms γs $$ Hrec
      iExactEq Hb; rfl
    ipureintro; exact hsz
  isplitr
  · ipureintro; rfl
  isplitl [Hgv Hsf Hdur Htlb Hbud]
  · iunfold nodeRaft
    iexists x, g
    iframe Hgv Hsf Hbud
    isplitl [Hdur]; · iExactEq Hdur; rfl
    isplitl [Htlb]; · iExactEq Htlb; rfl
    ipureintro; exact hfacts
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitl [Hrole]
  · iExactEq Hrole; rfl
  isplitr
  · ipureintro; exact antView0_normal
  isplitr
  · ipureintro
    exact ⟨rfl, AntSim.Reach.stay antView0 antView0_ok.2.2.1, rfl, rfl, Or.inl rfl⟩
  isplitr; · iexact Hlb
  unfold causeOwn
  rw [if_neg (fun h => by simp [antView0] at h)]
  ipureintro; rfl

end node

end AntHarness
end EtcdGrove
end Perennial
