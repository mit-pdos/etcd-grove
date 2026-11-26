/-
Lean-first (no Rocq counterpart). #33 parity B1: the run's ghost start and end for
`RunCluster.lean` (S4's `RunClusterAlloc.lean` over `Fin R.N`):

- `bigSepL_alloc_fun`: a family of names, one per node, from a per-node allocation;
- `antGhosts_alloc`: the run's own ghost names (the stream's two halves at `[]`, each view's two
  halves at the node's fresh view, each `live` token, the sent lists' authorities at `[]`, the read
  contexts' authority at `∅`);
- `antInv_alloc`: the run's invariant allocated open, at the empty stream, over fresh views and raft's
  facts `G` (the Sim's initial state, `antSim_init`, relates them: `G` with the run's boot facts and no
  acknowledgement);
- `antInv_close`: with every node's `live` token, the invariant's stream taken out, accepted at
  `R.cfg` and within `check.Run`'s bounds, and the invariant closed (over).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

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
    (hA : G.acks = []) (hL : AntSim.RaftLaws G) (hlogs : ∀ j, (V j).r.full ∈ G.logs) :
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
  exact ⟨⟨hP, hS, hb, hcb, hchg⟩, hL, hG G hB hA, hlogs⟩

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

end AntHarness
end EtcdGrove
end Perennial
