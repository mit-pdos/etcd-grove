/-
Lean-first (no Rocq counterpart). #33 parity B1: the run's ghost start and end for
`RunCluster.lean` (S4's `RunClusterAlloc.lean` over `Fin R.N`):

- `bigSepL_alloc_fun`: a family of names, one per node, from a per-node allocation;
- `antGhosts_alloc`: the run's own ghost names (the stream's two halves at `[]`, each view's two
  halves at the node's fresh view, each `live` token, the sent lists' authorities at `[]`, the read
  contexts' authority at `∅`);
- `antInv_alloc`: the run's invariant allocated open, at the empty stream, over fresh views and raft's
  facts `G` (the Sim's initial state, `antSim_init`, relates them: `G` with the run's boot facts);
- `antInv_close`: with every node's `live` token, the invariant's stream taken out, accepted at
  `R.cfg` and within `check.Run`'s bounds, and the invariant closed (over);
- `antRaft_alloc`: raft's cluster at the run's `R` (raft's `cluster_alloc_run` at the voters
  `1..K`, the ids `1..N`, the boot log `bootLog R` the driver writes): the static facts `nodeRaft`
  and `nodeDownRaft` state, the cluster, its receipts' fit, the client log's invariant (`opsInv`),
  the configuration of no entry, raft's initial facts `bootFacts0 R` (`raftFactsOwn`: the boot log,
  certified and committed), each node's vacant slot and durable state at `downDur R`;
  `propMinter_intro`: the proposer's minting from the cluster and `opsInv` (raft's
  `rawNode_prop_mint`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.PropMint
public import Proof.go_etcd_io.raft.v3.ClusterAllocRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **A name per node**: from an allocation for each node, one for every node of a list without
duplicates, as a function of the node. -/
theorem bigSepL_alloc_fun {N : Nat} (P : Fin N → GName → IProp GF)
    (h : ∀ j, ⊢ |==> ∃ g, P j g) :
    ∀ (l : List (Fin N)), l.Nodup → ⊢ |==> ∃ f : Fin N → GName, [∗list] j ∈ l, P j (f j)
  | [], _ => by
    imodintro; iexists (fun _ => 0)
    simp only [BigSepL.bigSepL_nil]; iempintro
  | x :: l, hnd => by
    rw [List.nodup_cons] at hnd
    imod bigSepL_alloc_fun P h l hnd.2 with ⟨%f, Hl⟩
    imod h x with ⟨%g, Hx⟩
    imodintro
    iexists (fun k => if k = x then g else f k)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hx]
    · simp only [eq_self_iff_true, ite_true]; iexact Hx
    iapply BigSepL.bigSepL_impl $$ Hl
    iintro !> %k %y %hy Hy
    have hyx : y ≠ x := fun e => hnd.1 (e ▸ List.mem_of_getElem? hy)
    simp only [hyx, ite_false]
    iexact Hy

/-- **The run's own ghost names** (see the file header), at the views `V`. -/
theorem antGhosts_alloc {N : Nat} (V : Fin N → AntSim.NodeView) :
    ⊢ |==> ∃ (strm sent xsent rctx : GName) (view live : Fin N → GName),
      ghostVar (GF := GF) strm (1 : Qp).half ([] : List AntCheck.Event) ∗
      ghostVar strm (1 : Qp).half ([] : List AntCheck.Event) ∗
      ([∗list] j ∈ List.finRange N, ghostVar (view j) (1 : Qp).half (V j) ∗
        ghostVar (view j) (1 : Qp).half (V j)) ∗
      ([∗list] j ∈ List.finRange N, dghostVar (live j) (DFrac.own 1) ()) ∗
      monoListAuthOwn sent 1 ([] : List Msg) ∗ monoListAuthOwn xsent 1 ([] : List XMsg) ∗
      authSetAuth rctx (∅ : GSet (List w8)) := by
  imod ghostVar_alloc (GF := GF) ([] : List AntCheck.Event) with ⟨%strm, Hs⟩
  icases (ghostVar_split_half (GF := GF) strm 1 ([] : List AntCheck.Event)).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod bigSepL_alloc_fun (GF := GF)
    (fun j g => iprop(ghostVar g (1 : Qp).half (V j) ∗ ghostVar g (1 : Qp).half (V j)))
    (fun j => by
      imod ghostVar_alloc (GF := GF) (V j) with ⟨%g, Hg⟩
      icases (ghostVar_split_half (GF := GF) g 1 (V j)).1 $$ Hg with ⟨Ha, Hb⟩
      imodintro; iexists g; iframe Ha Hb)
    (List.finRange N) (List.nodup_finRange N) with ⟨%view, Hv⟩
  imod bigSepL_alloc_fun (GF := GF) (fun _ g => dghostVar g (DFrac.own 1) ())
    (fun _ => dghostVar_alloc (GF := GF) ()) (List.finRange N) (List.nodup_finRange N)
    with ⟨%live, Hl⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Msg) with ⟨%sent, Ha, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List XMsg) with ⟨%xsent, Hxa, -⟩
  imod auth_set_init (GF := GF) (A := List w8) with ⟨%rctx, Hr⟩
  imodintro
  iexists strm, sent, xsent, rctx, view, live
  iframe Hs1 Hs2 Hv Hl Ha Hxa Hr

/-- The empty stream is within `check.Run`'s bounds at the run's configuration. -/
theorem antRun_nil_bounds (R : AntSim.RunCfg) :
    AntCheck.Stream.Bounded [] ∧ AntCheck.Stream.ConfBounded R.cfg [] ∧
      ∀ ev ∈ ([] : List AntCheck.Event), ev.ChgOk 0 := by
  have hK := R.hK
  have h1 := AntCheck.setOf_length_le (AntSim.namesL R.K)
  have l1 : (AntSim.namesL R.K).length = R.K := by simp [AntSim.namesL]
  refine ⟨⟨by simp [AntCheck.numBound], fun _ h => by simp at h⟩, ⟨0, fun _ h => by simp at h, ?_⟩,
    fun _ h => by simp at h⟩
  unfold AntSim.RunCfg.cfg
  simp only [List.length_nil, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
  omega

/-- **The run's invariant, allocated open** (see the file header). -/
theorem antInv_alloc (γ : AntNames) (V : Fin γ.R.N → AntSim.NodeView) (G : AntSim.RaftFacts)
    (E : CoPset) (hV : ∀ j, AntSim.FreshView γ.R (V j)) (hB : AntSim.BootFacts γ.R G)
    (hL : AntSim.RaftLaws G) (hlogs : ∀ j, (V j).r.full ∈ G.logs) :
    ⊢ ghostVar (GF := GF) γ.strm (1 : Qp).half ([] : List AntCheck.Event) -∗
      ([∗list] j ∈ List.finRange γ.R.N, ghostVar (γ.view j) (1 : Qp).half (V j)) -∗
      monoListAuthOwn γ.sent 1 ([] : List Msg) -∗ monoListAuthOwn γ.xsent 1 ([] : List XMsg) -∗
      raftFactsOwn γ.raft.raftNames G ={E}=∗ inv antN (antInv γ) := by
  iintro Hs Hv Ha Hxa #Hf
  obtain ⟨S, hP, hS, hG⟩ := AntSim.antSim_init γ.R γ.dec V hV
  obtain ⟨hb, hcb, hchg⟩ := antRun_nil_bounds γ.R
  iapply inv_alloc antN E
  inext
  iunfold antInv
  ileft
  iunfold antOpen
  iexists [], S, V, [], [], G
  iframe Hs Hv Ha Hxa Hf
  ipureintro
  exact ⟨⟨hP, hS, hb, hcb, hchg⟩, hL, hG G hB, hlogs⟩

/-- **The run's end** (see the file header). -/
theorem antInv_close (γ : AntNames) :
    ⊢ inv antN (antInv (GF := GF) γ) -∗ ([∗list] j ∈ List.finRange γ.R.N, nodeLive γ j) ={⊤}=∗
      ∃ evs : List AntCheck.Event, recDone γ.strm evs ∗
        ⌜AntCheck.Accepts γ.R.cfg evs ∧ AntCheck.Stream.Bounded evs ∧
          AntCheck.Stream.ConfBounded γ.R.cfg evs⌝ := by
  iintro #Hinv Hls
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hs, -, -, -, %Hp, -⟩
    obtain ⟨⟨hP, -, hB, hC, -⟩, -⟩ := Hp
    imod Hclose $$ [Hls] with -
    · inext; iunfold antInv; iright; iexact Hls
    imodintro
    iexists evs
    unfold recDone recAuth
    iframe Hs
    ipureintro; exact ⟨hP.accepts, hB, hC⟩
  · have hN : 0 < γ.R.N := by have := γ.R.hK; omega
    let j0 : Fin γ.R.N := ⟨0, hN⟩
    icases (BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ k => nodeLive (GF := GF) γ k)
      (finRange_getElem? j0)) $$ Hls with ⟨Hl, -⟩
    iexfalso
    iapply nodeLive_over (GF := GF) γ j0 $$ [Hl Hover]
    iframe Hl Hover

end ghost

section raftAlloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- The namespace `RunCluster` gives raft's cluster. -/
abbrev antRaftN : Namespace := nroot.@"raft"

theorem antRaftNs_mask : (↑(antRaftN.@"raft") : CoPset) ⊆ ⊤ \ ↑antN := by
  intro x hx
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  unfold antN at h'
  exact ndot_ne_disjoint nroot (show "raft" ≠ "antithesis" by decide) x
    ⟨nclose_subseteq _ _ x hx, h'⟩

theorem antOpsNs_mask : (↑antOpsN : CoPset) ⊆ ⊤ \ ↑antRaftN := by
  intro x hx
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  unfold antOpsN at hx
  exact ndot_ne_disjoint nroot (show "antithesis_ops" ≠ "raft" by decide) x ⟨hx, h'⟩

/-- The client entries of the run's boot log (`node.start`'s write). -/
def bootOps (R : AntSim.RunCfg) : List LogEntry :=
  if R.boot then [⟨W64 1, W32 0, AntSim.bootData⟩] else []

theorem bootOps_norm (R : AntSim.RunCfg) : NormBoot (bootOps R) := by
  unfold bootOps NormBoot
  split
  · right; exact ⟨AntSim.bootData, by simp [AntSim.bootData], rfl⟩
  · left; rfl

theorem bootOps_entries (R : AntSim.RunCfg) :
    LogEntry.toEntries (bootOps R) 0 = AntSim.bootLog R := by
  unfold bootOps AntSim.bootLog
  split
  · rfl
  · rfl

theorem bootOps_nil (R : AntSim.RunCfg) : bootOps R = [] ↔ R.boot = false := by
  unfold bootOps; by_cases h : R.boot = true <;> simp [h]

/-- **Raft's facts at the start of the run**: the boot log, certified, and committed. -/
def bootFacts0 (R : AntSim.RunCfg) : AntSim.RaftFacts :=
  { leaders := [], votes := [], logs := [AntSim.bootLog R], camps := [],
    committed := AntSim.bootLog R, commits := [] }

theorem bootFacts0_ok (R : AntSim.RunCfg) :
    AntSim.BootFacts R (bootFacts0 R) ∧ AntSim.RaftLaws (bootFacts0 R) := by
  refine ⟨⟨by simp [bootFacts0], fun _ _ _ h => by simp [bootFacts0] at h⟩, ?_⟩
  refine ⟨fun a h => by simp [bootFacts0] at h, fun a h => by simp [bootFacts0] at h,
    fun a ha b hb k e f _ _ _ => ?_, by simp [bootFacts0], fun p h => by simp [bootFacts0] at h,
    fun x h => by simp [bootFacts0] at h, fun p h => by simp [bootFacts0] at h⟩
  simp only [bootFacts0, List.mem_singleton] at ha hb
  rw [ha, hb]

theorem bootLog_idx (R : AntSim.RunCfg) : AntSim.LogIdx (AntSim.bootLog R) := by
  unfold AntSim.bootLog AntSim.LogIdx
  split
  · intro k e h
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
    | succ k => simp at h
  · intro k e h; simp at h

/-- The run's voters, `1, …, K`. -/
def votersL (R : AntSim.RunCfg) : List w64 := (List.range R.K).map fun (i : Nat) => W64 ((i : Int) + 1)

theorem votersL_ok (R : AntSim.RunCfg) :
    votersL R ≠ [] ∧ (votersL R).Nodup ∧ W64 0 ∉ votersL R ∧ ((votersL R).length : Int) < 2 ^ 62 := by
  have hK := R.hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold votersL; intro h
    have := congrArg List.length h; simp at this; omega
  · unfold votersL
    unfold List.Nodup; rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hne hab => hne ?_) List.nodup_range
    simp only [List.mem_range] at ha hb
    have : uint.Z (W64 ((a : Int) + 1)) = uint.Z (W64 ((b : Int) + 1)) := by rw [hab]
    rw [uint_Z_W64 _ (by omega) (by omega), uint_Z_W64 _ (by omega) (by omega)] at this
    omega
  · unfold votersL; intro h
    obtain ⟨a, ha, he⟩ := List.mem_map.mp h
    simp only [List.mem_range] at ha
    have : uint.Z (W64 ((a : Int) + 1)) = uint.Z (W64 0) := by rw [he]
    rw [uint_Z_W64 _ (by omega) (by omega)] at this
    rw [show uint.Z (W64 0) = 0 from rfl] at this; omega
  · unfold votersL; simp; omega

theorem nodeIds_ok (R : AntSim.RunCfg) :
    ((List.finRange R.N).map AntSim.nodeId).Nodup ∧ W64 0 ∉ (List.finRange R.N).map AntSim.nodeId := by
  have hK := R.hK
  refine ⟨?_, ?_⟩
  · unfold List.Nodup; rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} _ _ hne hab => hne ?_) (List.nodup_finRange R.N)
    unfold AntSim.nodeId at hab
    have : uint.Z (W64 ((a.val : Int) + 1)) = uint.Z (W64 ((b.val : Int) + 1)) := by rw [hab]
    have ha := a.isLt; have hb := b.isLt
    rw [uint_Z_W64 _ (by omega) (by omega), uint_Z_W64 _ (by omega) (by omega)] at this
    exact Fin.ext (by omega)
  · intro h
    obtain ⟨a, -, he⟩ := List.mem_map.mp h
    unfold AntSim.nodeId at he
    have ha := a.isLt
    have : uint.Z (W64 ((a.val : Int) + 1)) = uint.Z (W64 0) := by rw [he]
    rw [uint_Z_W64 _ (by omega) (by omega)] at this
    rw [show uint.Z (W64 0) = 0 from rfl] at this; omega

/-- **Raft's cluster at the run's `R`** (see the file header). -/
theorem antRaft_alloc (R : AntSim.RunCfg) (Hfits : antRunFits GF) :
    ⊢ |={⊤}=> ∃ γr : Cluster,
      ⌜γr.dup = true ∧ ¬ clusterNoSnap γr ∧ Cluster.trace γr = none ∧ γr.maxData = none ∧
        γr.bootLen = (AntSim.bootLog R).length ∧
        γr.raftNames.reTrace = none ∧ γr.raftNames.reCfg = R.voters0 ∧
        γr.raftNames.maxData = none ∧ γr.raftNames.reBoot = AntSim.bootLog R ∧
        (↑(raftN γr.raftNames) : CoPset) ⊆ ⊤ \ ↑antN ∧
        -- (antithesis parity B1, group E) an acknowledging node is a server
        (∀ a : w64, (γr.raftNames.reAcks !! a).isSome → ∃ j : Fin R.N, a = AntSim.nodeId j)⌝ ∗
      isCluster (GF := GF) γr antRaftN ∗ readyFits γr antRaftN ∗ opsInv γr ∗
      confAt γr 0 (Membership.simple R.voters0) ∗ raftFactsOwn γr.raftNames (bootFacts0 R) ∗
      [∗list] j ∈ List.finRange R.N,
        nodeVacant γr (AntSim.nodeId j) ∗ raftState γr (AntSim.nodeId j) (downDur R) := by
  have Hrb : receiptBound GF ≤ 2 ^ 64 - 2 := by unfold antRunFits at Hfits; omega
  obtain ⟨Hvne, Hvnd, Hvnz, Hvlen⟩ := votersL_ok R
  obtain ⟨Hind, Hinz⟩ := nodeIds_ok R
  imod cluster_alloc_run (GF := GF) antRaftN (votersL R) ((List.finRange R.N).map AntSim.nodeId)
      (bootOps R) true ⊤ (fun _ _ => CoPset.mem_full) Hrb Hvne Hvnd Hvnz Hvlen Hind Hinz (bootOps_norm R)
    with ⟨%γr, %Hd, %Hnm, Hops, #Hcl, #Hca, #Hcb, #Hrecs, Hfs⟩
  obtain ⟨Hdup, Hbl, Hmd, Hns, Htr⟩ := Hd
  obtain ⟨Hcfg, Hboot, HreNs, HreTr, HreMd, Hacks⟩ := Hnm
  rw [bootOps_entries] at Hboot
  imod opsInv_alloc γr (bootOps R) ⊤ $$ Hops with #Hopsi
  have Hbl' : γr.bootLen = (AntSim.bootLog R).length := by
    rw [Hbl, ← bootOps_entries R, ApiImpl.toEntries_length]
  have Hb1 : (AntSim.bootLog R).length ≤ 1 := by unfold AntSim.bootLog; split <;> simp
  ihave #Hrfit := readyFits_intro (GF := GF) γr antRaftN
    (by rw [Hbl']; unfold antRunFits at Hfits; omega)
  imodintro
  iexists γr
  isplitr
  · ipureintro
    refine ⟨Hdup, Hns, Htr, Hmd, Hbl', HreTr, Hcfg, HreMd, Hboot, ?_, fun a ha => ?_⟩
    · unfold raftN; rw [HreNs]; exact antRaftNs_mask
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 ha
      have h1 := GMap.elem_of_dom_2 _ a u hu
      rw [Hacks] at h1
      obtain ⟨j, -, hj⟩ := List.mem_map.1 ((GMap.elem_of_list_to_set _ _).1 h1)
      exact ⟨j, hj.symm⟩
  rw [show R.voters0 = GMap.listToSet (votersL R) from rfl]
  iframe Hcl Hrfit Hopsi Hca
  isplitr
  · unfold raftFactsOwn bootFacts0
    rw [← Hboot]
    simp only [BigSepL.bigSepL_nil, BigSepL.bigSepL_cons]
    iframe Hcb Hrecs
    isplitr; · iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr; · iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · isplitr; · ipureintro; rw [Hboot]; exact bootLog_idx R
      iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr; · iapply (BigSepL.bigSepL_nil).2; iempintro
    iapply (BigSepL.bigSepL_nil).2; iempintro
  irevert Hfs
  rw [BigSepL.bigSepL_map]
  iintro Hfs
  iapply BigSepL.bigSepL_impl $$ Hfs
  imodintro
  iintro %k %j %_ ⟨Hrs, Hvac⟩
  iframe Hvac
  have Hdd : (if bootOps R = [] then RaftState.init else bootDurState γr.raftNames.reBoot) =
      downDur R := by
    unfold downDur bootDurState
    rw [Hboot]
    cases hR : R.boot
    · rw [if_pos ((bootOps_nil R).2 hR)]; rfl
    · rw [if_neg (fun h => by rw [(bootOps_nil R).1 h] at hR; cases hR)]; rfl
  rw [Hdd]
  iexact Hrs

/-- **The proposer's minting** (`propMinter`), from the cluster and the client log's invariant, with
no bound on proposed data (raft's `rawNode_prop_mint`; any `dup`: the run's is on). -/
theorem propMinter_intro (γ : AntNames) (Hmd : γ.raft.raftNames.maxData = none) :
    ⊢ isCluster (GF := GF) γ.raft antRaftN -∗ opsInv γ.raft -∗ propMinter γ := by
  iintro #Hcl #Hops
  unfold propMinter
  imodintro
  iintro %data
  iapply propOk_mint (fun γ N data E HE => rawNode_prop_mint γ N data E HE) γ antRaftN data ⊤
    (fun _ _ => CoPset.mem_full) antOpsNs_mask Hmd $$ Hcl Hops

end raftAlloc

end AntHarness
end EtcdGrove
end Perennial
