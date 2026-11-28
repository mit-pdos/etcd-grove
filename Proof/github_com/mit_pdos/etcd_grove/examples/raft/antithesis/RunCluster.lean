/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/RunCluster.lean`, over its callees'
specs (`driver.go`'s `RunCluster`, in its order):

- the cluster `c` (its recorder's lock at the empty stream, its stop channel a broadcast);
- the initial voters `1, …, Voters` (`c.initVoters`);
- the nodes `1, …, Nodes`, each with its input channel and a fresh disk (`nodeMade`: every field the
  composite literal leaves zero), appended to `c.nodes`, and `c.down` all `false`;
- the ghost start: the run's configuration `R` of the mode (`runCfgOf`, `ModeRun`), raft's cluster at
  `R` with `dup` on (`antRaft_alloc`: the driver duplicates deliveries, forwarded `MsgProp`s too),
  the run's own names (`antGhosts_alloc` at the fresh views `viewInit R`), each node's input bag
  (`inputOk`), the wait groups (`nodesWg`, `behWg` as joins, `netWg` as the network's), the `down`
  lock, the run's invariant (`antInv_alloc` over raft's initial facts `bootFacts0 R`) and the
  proposer's minting (`propMinter_intro`): `antCluster`; each node's `nodeRO` and `nodeOwn … .down`
  (`nodeMade_own`);
- the `go c.run(n)` loop: `nodesWg.Add(1)` with the node's `nodeExit` at the network's adders' share
  `qh (j + 1)` (the shares halve: `qh`), the goroutine forked with a fresh token
  (`wp_fork_tok_body`), which `Cluster.run` gives back;
- the behaviours spawned (`Cluster.spawn`, the method values `c.proposer`, `c.campaigner`, with reads
  `c.reader` (the reader's contexts at none), with transfers `c.transferer`; B2/B3's are off);
- the stop: `time.Sleep`, `close(c.stop)`, `behWg.Wait()`, `nodesWg.Wait()` (every `nodeExit` back),
  the network's adders joined (`adders_join`) and closed (`njClose`), `netWg.Wait()`, and the run's
  invariant closed (`antInv_close`): `runOver`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.AntStorageStart
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__spawn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__proposer
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__campaigner
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__reader
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__transferer
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunClusterAlloc
public import Perennial.Spec.time.Sleep
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Wait

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

attribute [-instance] pure_wp_slice_for_range

/-! ## The run's configuration and fresh views -/

section cfg
variable [GooseExts]

/-- **The run's configuration of a mode drawn within B1's mask** (`ModeRun`'s `R`). -/
def runCfgOf (m : H.Mode) (h : InScope b1Scope m) : AntSim.RunCfg where
  N := uint.nat m.Nodes'
  K := uint.nat m.Voters'
  boot := m.Boot'
  k := fun _ => modeK m
  md := scopeMd b1Scope
  drv := modeDrv m
  hK := by
    have h3 : uint.nat (W64 3) = 3 := rfl
    have h5 : uint.nat (W64 5) = 5 := rfl
    obtain ⟨hN, hV, -⟩ := h
    rcases hV with hV | ⟨-, hN', hV⟩
    · rw [hV]; rcases hN with hN | hN <;> rw [hN] <;> omega
    · rw [hV, hN']; omega
  hpv := fun _ _ => rfl

theorem modeRun_runCfgOf (m : H.Mode) (h : InScope b1Scope m) :
    ModeRun b1Scope m (runCfgOf m h) :=
  ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

/-- A node's raft state at the run's start (`PInitR`). -/
def rInit (R : AntSim.RunCfg) : RState :=
  { p := { term := W64 (if R.boot then 1 else 0), vote := W64 0, lead := W64 0, role := .follower,
           votes := ∅, outbox := [], base := base0, log := AntSim.bootLog R, commit := W64 0,
           matched := ∅ },
    applied := W64 0, pci := W64 0, snap := false, cidx := 0, cfg := R.c0, fp := [] }

/-- **A node's view at the run's start** (`FreshView`): not running, nothing delivered, its disk its
state's. -/
def viewInit (R : AntSim.RunCfg) : AntSim.NodeView :=
  { r := rInit R, delivered := [], dur := AntSim.durOf (rInit R), conf := R.c0, alive := false,
    byE := go!"boot" }

/-- A mode within B1's mask: `1 ≤ Voters ≤ Nodes ≤ 5`. -/
theorem inScope_b1_sizes {m : H.Mode} (h : InScope b1Scope m) :
    1 ≤ uint.Z m.Voters' ∧ uint.Z m.Voters' ≤ uint.Z m.Nodes' ∧ uint.Z m.Nodes' ≤ 5 := by
  obtain ⟨hN, hV, -⟩ := h
  rcases hV with hV | ⟨-, hN5, hV3⟩
  · rw [hV]; rcases hN with hN | hN <;> rw [hN] <;> decide
  · rw [hN5, hV3]; decide

theorem viewInit_fresh (R : AntSim.RunCfg) : AntSim.FreshView R (viewInit R) := by
  unfold AntSim.FreshView AntSim.PInitR AntSim.NodeView.Idle
  and_intros <;> rfl

theorem viewInit_full (R : AntSim.RunCfg) : (viewInit R).r.full = AntSim.bootLog R := rfl

theorem viewInit_normal (R : AntSim.RunCfg) : ViewNormal (viewInit R) := by
  refine ⟨?_, fun m h => by cases h⟩
  rw [viewInit_full]
  unfold AntSim.bootLog
  split
  · intro e he; simp only [List.mem_singleton] at he; subst he; rfl
  · intro e he; cases he

/-- The network adders' shares: node `j` takes `qh (j + 1)`, and `qh i` is what is left after `i`
nodes (`qh i = qh (i + 1) + qh (i + 1)`). -/
def qh : Nat → Qp
  | 0 => 1
  | n + 1 => (qh n).half

theorem qh_succ (n : Nat) : qh (n + 1) + qh (n + 1) = qh n := Qp.half_add_half _

end cfg

/-! ## List lemmas over `finRange` -/

theorem finRange_take_succ {N : Nat} (i : Nat) (hi : i < N) :
    (List.finRange N).take (i + 1) = (List.finRange N).take i ++ [⟨i, hi⟩] := by
  rw [List.take_add_one]
  congr
  simp [hi]

theorem finRange_drop_cons {N : Nat} (i : Nat) (hi : i < N) :
    (List.finRange N).drop i = ⟨i, hi⟩ :: (List.finRange N).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp

section lists
variable {GF : BundledGFunctors}

/-- A big separating conjunction over a list of length `N`, indexed, as one over `finRange N`. -/
theorem bigSepL_finRange_of {A : Type} [Inhabited A] :
    ∀ (l : List A) (Φ : Nat → A → IProp GF) (N : Nat), l.length = N →
      ([∗list] i ↦ x ∈ l, Φ i x) ⊢ [∗list] j ∈ List.finRange N, Φ j.val l[j.val]!
  | [], Φ, N, hl => by
    subst hl
    simp only [List.length_nil, List.finRange_zero]
    iintro -
    iapply (BigSepL.bigSepL_nil).2; iempintro
  | a :: l, Φ, N, hl => by
    subst hl
    rw [List.length_cons, List.finRange_succ]
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, Hl⟩
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Ha]
    · simp only [Fin.val_zero, List.getElem!_cons_zero]; iexact Ha
    rw [BigSepL.bigSepL_map]
    ihave Hl' := bigSepL_finRange_of l (fun i x => Φ (i + 1) x) l.length rfl $$ Hl
    iapply BigSepL.bigSepL_impl $$ Hl'
    iintro !> %k %j %_ H
    simp only [Fin.val_succ, List.getElem!_cons_succ]
    iexact H

theorem bigSepL_fupd {A : Type} [hG : InvGS GF] (E : CoPset) (Φ : A → IProp GF) :
    ∀ l : List A, ([∗list] x ∈ l, |={E}=> Φ x) ⊢ |={E}=> [∗list] x ∈ l, Φ x
  | [] => by
    iintro -; imodintro; iapply (BigSepL.bigSepL_nil).2; iempintro
  | a :: l => by
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, Hl⟩
    imod Ha with Ha
    imod (bigSepL_fupd E Φ l) $$ Hl with Hl
    imodintro
    iapply (BigSepL.bigSepL_cons).2
    iframe Ha Hl

theorem map_fst_getElem! {A B : Type} [Inhabited A] [Inhabited B] (l : List (A × B)) (i : Nat)
    (hi : i < l.length) : (l.map Prod.fst)[i]! = (l[i]!).1 := by
  rw [getElem!_pos (l.map Prod.fst) i (by simpa using hi), getElem!_pos l i hi]
  simp

end lists

section made
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **Node `i`'s goroutine's memory as `RunCluster` makes it** (`&node{c, id: i + 1, name, in, disk}`,
before the run's names exist): the read-only fields (its input channel's at `γch`, empty), the
logger's cell in its invariant, a fresh disk, and every other field zero. -/
def nodeMade (c n : Loc) (i : Nat) (γch : ChanNames) : IProp GF :=
  iprop(∃ (ch d : Loc),
    n.[H.node, go!"c"] ↦□ c ∗ n.[H.node, go!"id"] ↦□ W64 ((i : Int) + 1) ∗
    n.[H.node, go!"name"] ↦□ AntSim.nameOf (W64 ((i : Int) + 1)) ∗ n.[H.node, go!"in"] ↦□ ch ∗
    isChan ch γch H.input ∗ ownChan γch H.input (ChanState.Buffered []) ∗
    n.[H.node, go!"disk"] ↦□ d ∗ inv antLogN (∃ k : w64, n.[H.node, go!"autoLeft"] ↦ k) ∗
    diskOwn d ⟨W64 0, W64 0, W64 0, []⟩ ∗ nodeMemB1 n ∗
    n.[H.node, go!"rn"] ↦ null ∗ n.[H.node, go!"store"] ↦ null ∗
    n.[H.node, go!"role"] ↦ (zero_val GoString) ∗ n.[H.node, go!"hs"] ↦ null ∗
    n.[H.node, go!"cause"] ↦ null ∗ n.[H.node, go!"applied"] ↦ W64 0 ∗
    n.[H.node, go!"conf"] ↦ null)

/-- **A made node, in the run** (`γ` its names, `γ.inCh j` its channel's): its read-only record (the
channel a bag of `inputOk` inputs) and its goroutine's state before `start`, at the fresh view. -/
theorem nodeMade_own (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) :
    ⊢ nodeMade (GF := GF) c n j.val (γ.inCh j) -∗ viewFrag γ j (viewInit γ.R) -∗ nodeLive γ j -∗
      nodeDownRaft γ j ={⊤}=∗ nodeRO c γ n j ∗ nodeOwn c γ j n (viewInit γ.R) .down := by
  iintro Hm Hv Hl Hdr
  iunfold nodeMade at Hm
  icases Hm with ⟨%ch, %d, #Hc, #Hid, #Hname, #Hin, #Hich, Hoch, #Hd, #Hlog, Hdisk, Hmem, Hrn, Hst,
    Hrole, Hhs, Hcause, Happ, Hconf⟩
  imod start_bag (V := H.input) (inputOk γ j) (ChanState.Buffered []) ch (γ.inCh j) trivial
    $$ Hich Hoch with #Hbag
  imodintro
  isplitr
  · iunfold nodeRO
    iexists ch, d
    iframe Hc Hin Hbag Hd Hlog
    rw [show AntSim.nodeId j = W64 ((j.val : Int) + 1) from rfl]
    isplitr
    · iexact Hid
    iexact Hname
  · iunfold nodeOwn
    iexists d, null, null, null, null, null, zero_val GoString, W64 0
    dsimp only
    iframe Hd Hmem Hrn Hst Hrole Hhs Hcause Happ Hconf Hv Hl Hdr Hdisk
    isplitr
    · ipureintro; exact viewInit_normal γ.R
    ipureintro
    exact ⟨viewInit_fresh γ.R, rfl⟩

/-- **The network adders' shares joined**: what is left after `i` nodes and the shares of those `i`
nodes make the whole right. -/
theorem adders_join (c : Loc) (γ : AntNames) :
    ∀ i, i ≤ γ.R.N → netAdder (GF := GF) c γ (qh i) ∗
      ([∗list] j ∈ (List.finRange γ.R.N).take i, netAdder c γ (qh (j.val + 1))) ⊢ netAdder c γ 1
  | 0, _ => by
    simp only [List.take_zero]
    rw [show qh 0 = 1 from rfl]
    iintro ⟨H, -⟩; iexact H
  | i + 1, hi => by
    rw [finRange_take_succ i (by omega)]
    iintro ⟨H, Hl⟩
    icases (BigSepL.bigSepL_snoc).1 $$ Hl with ⟨Hl, Hi⟩
    iapply adders_join c γ i (by omega)
    iframe Hl
    unfold netAdder
    rw [← qh_succ i]
    iapply njAdder_join
    iframe H Hi

end made

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A range loop over a slice the loop only reads** (a copy of
`idNames.lean`'s `wp_slice_for_range_ro`, private there). -/
private theorem wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

theorem RunCluster.wp_proof
    (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_run : ∀ [AntStor GF], letI : StorageModel GF := antStorageModelNC
      Cluster.run.spec (GF := GF) (hG := hG))
    (wp_spawn : ∀ [AntStor GF], letI : StorageModel GF := antStorageModelNC
      Cluster.spawn.spec (GF := GF) (hG := hG))
    (wp_proposer : ∀ [AntStor GF], letI : StorageModel GF := antStorageModelNC
      Cluster.proposer.spec (GF := GF) (hG := hG))
    (wp_campaigner : ∀ [AntStor GF], letI : StorageModel GF := antStorageModelNC
      Cluster.campaigner.spec (GF := GF) (hG := hG))
    (wp_reader : ∀ [AntStor GF], letI : StorageModel GF := antStorageModelNC
      Cluster.reader.spec (GF := GF) (hG := hG))
    (wp_transferer : ∀ [AntStor GF], letI : StorageModel GF := antStorageModelNC
      Cluster.transferer.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (h_drain : drainB1_of_inScope.law) :
    RunCluster.spec (GF := GF) (hG := hG) := by
  intro _ Hfits cfg mode Hcok Hsc
  wp_start as Htok
  -- the storage registry (`node.start` registers its `bootStorage` there), the run's storage model
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := AntStorRecT) with ⟨%γreg, Hreg⟩
  letI : AntStor GF := ⟨γreg⟩
  imod inv_alloc antStorN ⊤ antStorInvBody $$ [Hreg] with #HstInv
  · inext
    iunfold antStorInvBody
    iexists ∅
    iframe Hreg
    iapply (BigSepM.bigSepM_empty).2; iempintro
  ihave #HstInv' : antStorInv (GF := GF) $$ []
  · iunfold antStorInv; iexact HstInv
  letI : StorageModel GF := antStorageModelNC
  have wp_run : Cluster.run.spec (GF := GF) (hG := hG) := wp_run
  have wp_spawn : Cluster.spawn.spec (GF := GF) (hG := hG) := wp_spawn
  have wp_proposer : Cluster.proposer.spec (GF := GF) (hG := hG) := wp_proposer
  have wp_campaigner : Cluster.campaigner.spec (GF := GF) (hG := hG) := wp_campaigner
  have wp_reader : Cluster.reader.spec (GF := GF) (hG := hG) := wp_reader
  have wp_transferer : Cluster.transferer.spec (GF := GF) (hG := hG) := wp_transferer
  ihave #Hsy : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  try wp_auto
  -- the stop channel, a broadcast
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsch, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsch Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  try wp_auto
  -- the recorder, at the empty stream
  iStructNamedPrefix «$v2» "R"
  iStructNamedPrefix «$r0» "C"
  generalize «$r0_ptr» = cl at *
  generalize «$v2_ptr» = rp at *
  iStructNamedPrefix mode "M"
  iStructNamedPrefix cfg "G"
  obtain ⟨HV1, HVN, HN5⟩ := inScope_b1_sizes Hsc
  generalize HR : runCfgOf mode Hsc = R
  have HMR : ModeRun b1Scope mode R := HR ▸ modeRun_runCfgOf mode Hsc
  imod antGhosts_alloc (GF := GF) (fun _ : Fin R.N => viewInit R) with
    ⟨%strm, %sent, %xsent, %rctx, %view, %live, Hs1, Hs2, Hvs, Hls, Hsa, Hxa, Hra⟩
  imod receipt_zero (GF := GF) with Hr0
  imod sync.init_Mutex (recLockInv strm rp) ⊤ _ $$ Rmu [Revents Hs2 Hr0] with #Hrec
  · inext
    iunfold recLockInv
    iexists slice.nil, []
    iframe Revents Hs2
    isplitr
    · iunfold AntCheck.eventsRO
      iexists []
      isplitr
      · iapply ownSlice_nil
      iapply (BigSepL2.bigSepL2_nil).2; iempintro
    isplitr
    · iapply ownSliceCap_nil
    iExactEq Hr0; simp
  ihave #HisRec : isRecorder strm rp $$ []
  · iunfold isRecorder; iexact Hrec
  ipersist Ccfg
  ipersist Cmode
  ipersist Crec
  ipersist Cstop
  ipersist MNodes
  ipersist MVoters
  ipersist MReads
  ipersist MTransfer
  ipersist MConfChanges
  ipersist MSnapshots
  ipersist MRestarts
  ipersist MBatch
  ipersist MAsync
  ipersist GSettle
  iclear R_ C_ M_ G_ MBoot MPreVote MCheckQuorum MStepDownOnRemoval MMaxInflightMsgs MMaxSizePerMsg
    MForward MMaxDeliveries MParallel MSplit MSnapStatus MAnchor GTick GPace GRestartPace
    GElectionPace GNoHoldVote
  -- the initial voters
  ihave IHv : iprop(∃ (k : w64) (sl : GoSlice),
      "i" ∷ i_ptr ↦ k ∗
      "CinitVoters" ∷ cl.[H.Cluster, go!"initVoters"] ↦ sl ∗
      "Hsl" ∷ sl ↦* ((List.range (uint.nat k - 1)).map fun j : Nat => W64 ((j : Int) + 1)) ∗
      "Hcap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜1 ≤ uint.Z k ∧ uint.Z k ≤ uint.Z mode.Voters' + 1⌝)
    $$ [i CinitVoters]
  · iexists W64 1, slice.nil
    iframe i CinitVoters
    rw [show uint.nat (W64 1) - 1 = 0 from rfl]
    isplitl []
    · simp only [List.range_zero, List.map_nil]; iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for IHv
  wp_if_destruct
  · try wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint64) [k]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.uint64 #k)] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Htmp, -⟩
    wp_apply wp_slice_append (V := w64) (t := go.uint64) sl _ _ [k] (DFrac.own 1)
      $$ [Hsl Hcap Htmp] as %sl' ⟨Hsl', Hcap', -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, sl'
    have Hk1 : uint.nat (k + W64 1) - 1 = (uint.nat k - 1) + 1 := by word
    have HkW : W64 (((uint.nat k - 1 : Nat) : Int) + 1) = k := by word
    rw [Hk1, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [HkW]
    iframe
    ipureintro; constructor <;> word
  have HkV : uint.nat k - 1 = uint.nat mode.Voters' := by word
  rw [HkV]
  try wp_auto
  imod ownSlice_persist sl _ _ $$ Hsl with #Hsl
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ CinitVoters with #CinitVoters
  -- the nodes
  ihave IHn : iprop(∃ (k : w64) (nsl dsl : GoSlice) (ds : List (Loc × ChanNames)),
      "i" ∷ i_ptr ↦ k ∗
      "Cnodes" ∷ cl.[H.Cluster, go!"nodes"] ↦ nsl ∗ "Hnsl" ∷ nsl ↦* ds.map Prod.fst ∗
      "Hncap" ∷ ownSliceCap Loc nsl (DFrac.own 1) ∗
      "Cdown" ∷ cl.[H.Cluster, go!"down"] ↦ dsl ∗
      "Hdsl" ∷ dsl ↦* List.replicate ds.length false ∗ "Hdcap" ∷ ownSliceCap Bool dsl (DFrac.own 1) ∗
      "Hdone" ∷ ([∗list] j ↦ d ∈ ds, nodeMade cl d.1 j d.2) ∗
      "%Hk" ∷ ⌜1 ≤ uint.Z k ∧ uint.Z k ≤ uint.Z mode.Nodes' + 1 ∧ ds.length = uint.nat k - 1⌝)
    $$ [i Cnodes Cdown]
  · iexists W64 1, slice.nil, slice.nil, []
    iframe i Cnodes Cdown
    simp only [List.map_nil, List.length_nil, List.replicate_zero]
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for IHn
  wp_if_destruct
  · try wp_auto
    wp_apply wp_Name
    wp_apply (chan.wp_make2 (V := H.input) (W64 1024)) as %ch %γch ⟨#Hich, %_, Hoch⟩
    · ipureintro; constructor <;> decide
    try wp_auto
    -- node `k`'s memory
    iStructNamedPrefix «$r0» "N"
    iStructNamedPrefix «$v4» "D"
    generalize «$r0_ptr» = nd at *
    ipersist Nc
    ipersist Nid
    ipersist Nname
    ipersist Nin'
    ipersist Ndisk
    imod inv_alloc antLogN ⊤ iprop(∃ k : w64, nd.[H.node, go!"autoLeft"] ↦ k) $$ [NautoLeft]
      with #Hlog
    · inext; iexists _; iexact NautoLeft
    imod hsRO_of_struct «$v0_ptr» (zero_val raftpb.HardState) (HardStateM.mk (W64 0) (W64 0) (W64 0))
      ⊤ rfl $$ [«$v0»] with #Hhs
    · iframe «$v0»
      repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
      iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
    rw [show (0 : w64) = W64 0 from rfl]
    ihave Hmade : nodeMade cl nd ds.length γch $$
        [Nrn Nstore Nrole Nhs Ncause Napplied Nconf Nitems Nmhs Nrhs Nwrites Ninflight Napplies
          Napplying Nrestoring Nwip Naip Nconfs NconfBase Nfuse Ndead Hoch Dhs Dsnap Dents]
    · iunfold nodeMade
      iexists ch, «$v4_ptr»
      have HkW : W64 ((ds.length : Int) + 1) = k := by rw [Hk.2.2]; word
      rw [HkW]
      iframe Nc Nid Nname Nin' Hich Hoch Ndisk Hlog Nrn Nstore Nhs Ncause Napplied Nconf
      isplitl [Dhs Dsnap Dents]
      · iunfold diskOwn
        iexists «$v0_ptr», slice.nil
        iframe Dhs Dsnap Dents Hhs
        isplitl []
        · iunfold entsPts; iexists []
          isplitl []
          · iapply ownSlice_nil
          iapply (BigSepL2.bigSepL2_nil).2; iempintro
        iapply ownSliceCap_nil
      isplitl [Nitems Nmhs Nrhs Nwrites Ninflight Napplies Napplying Nrestoring Nwip Naip Nconfs NconfBase
          Nfuse Ndead]
      · iunfold nodeMemB1
        iexists null, null
        iframe Nitems Nmhs Nrhs Nwrites Ninflight Napplies Napplying Nrestoring Nwip Naip Nconfs NconfBase
        iunfold emitOk
        iframe Nfuse Ndead
      iexact Nrole
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc)
      (t := go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty) [nd]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)
      #nd)] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Htmp, -⟩
    wp_apply wp_slice_append (V := Loc)
        (t := go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)
        nsl _ _ [nd] (DFrac.own 1)
      $$ [Hnsl Hncap Htmp] as %nsl' ⟨Hnsl', Hncap', -⟩
    · iframe
    try wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.bool))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Bool) (t := go.bool) [false]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.bool #false)] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %bsl_ptr ⟨Htmp, -⟩
    wp_apply wp_slice_append (V := Bool) (t := go.bool) dsl _ _ [false] (DFrac.own 1)
      $$ [Hdsl Hdcap Htmp] as %dsl' ⟨Hdsl', Hdcap', -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, nsl', dsl', ds ++ [(nd, γch)]
    iframe
    simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_cons,
      List.length_nil, List.replicate_succ']
    iframe
    isplitl [Hmade]
    · iapply (BigSepL.bigSepL_singleton).2; simp only [Nat.zero_add]; iexact Hmade
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [Hk.2.2]; word
  -- the nodes made
  have HkN : uint.nat k - 1 = R.N := by
    rw [HMR.1]
    have : ¬ uint.Z k ≤ uint.Z mode.Nodes' := by simpa using Hif
    word
  have Hdl : ds.length = R.N := by rw [Hk.2.2, HkN]
  try wp_auto
  imod ownSlice_persist nsl _ _ $$ Hnsl with #Hnsl
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Cnodes with #Cnodes
  -- raft's cluster, the wait groups
  imod antRaft_alloc (GF := GF) R Hfits with ⟨%γr, %Hγr, #Hcl, #Hrfit, #Hopsi, HU, #Hca, #Hrf, Hnds⟩
  obtain ⟨-, Hns, Htr, Hmd, Hbl, HreTr, HreCfg, HreMd, HreBoot, HrN, Hacks, Hwins, Hacks'⟩ := Hγr
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ CnodesWg with ⟨%γnw, Hnw⟩
  imod sync.join.init _ γnw $$ Hnw with Hnadder
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ CbehWg with ⟨%γbw, Hbw⟩
  imod sync.join.init _ γbw $$ Hbw with Hbadder
  imod sync.init_WaitGroup (antNetN.@"wg") _ $$ CnetWg with ⟨%γwg, Hwg⟩
  imod nj_init antNetN _ γwg ⊤ $$ Hwg with ⟨%γnj, Had⟩
  icases njAdder_isNetJoin antNetN _ γnj 1 $$ Had with ⟨Had, #Hnj⟩
  -- the run's names
  haveI : Inhabited ChanNames := ⟨γsc⟩
  let γ : AntNames := ⟨R, fun _ _ => none, b1Scope, mode, γr, strm, view, live, sent, xsent, rctx, γnj,
    fun j => (ds[j.val]!).2, γsc⟩
  have HγR : γ.R = R := rfl
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hvs with ⟨HvA, HvB⟩
  obtain ⟨hB, hL⟩ := bootFacts0_ok R
  imod antInv_alloc γ (fun _ => viewInit R) (bootFacts0 R) ⊤ (fun _ => viewInit_fresh R) hB hL
    (fun _ => by rw [viewInit_full]; simp [bootFacts0]) $$ Hs1 HvA Hsa Hxa Hrf with #Hinv
  ihave #Hpm := propMinter_intro (GF := GF) γ HreMd $$ Hcl Hopsi
  ihave #Hrdm : rdMinter (GF := GF) γ $$ []
  · iunfold rdMinter
    imodintro
    iintro H1
    iapply isCluster_rdMint (GF := GF) γr antRaftN ⊤ (fun _ _ => CoPset.mem_full) $$ Hcl H1
  -- the `down` lock
  imod sync.init_Mutex (downInv cl γ) ⊤ _ $$ Cmu [Cdown Hdsl] with #Hmu
  · inext
    iunfold downInv
    iexists dsl, List.replicate ds.length false
    iframe Cdown Hdsl
    ipureintro
    refine ⟨by rw [List.length_replicate, Hdl], fun _ b hb => (List.eq_of_mem_replicate hb)⟩
  -- each node's record and state before `start`
  ihave Hdone := bigSepL_finRange_of ds (fun j d => nodeMade (GF := GF) cl d.1 j d.2) R.N Hdl $$ Hdone
  ihave Hall := (BigSepL.bigSepL_sep_eqv_symm).1 $$ [Hdone HvB]
  · iframe Hdone HvB
  ihave Hall := (BigSepL.bigSepL_sep_eqv_symm).1 $$ [Hall Hls]
  · iframe Hall Hls
  ihave Hall := (BigSepL.bigSepL_sep_eqv_symm).1 $$ [Hall Hnds]
  · iframe Hall Hnds
  ihave Hall : iprop([∗list] j ∈ List.finRange R.N,
      |={⊤}=> nodeRO (GF := GF) cl γ (ds[j.val]!).1 j ∗ nodeOwn cl γ j (ds[j.val]!).1 (viewInit R) .down)
    $$ [Hall]
  · iapply BigSepL.bigSepL_impl $$ Hall
    iintro !> %k %j %_ ⟨⟨⟨Hm, Hv⟩, Hl⟩, ⟨Hvac, Hrs⟩⟩
    iapply nodeMade_own cl γ j ((ds[j.val]!).1) $$ Hm [Hv] [Hl] [Hvac Hrs]
    · iunfold viewFrag; iexact Hv
    · iunfold nodeLive; iexact Hl
    · iunfold nodeDownRaft
      iframe Hvac Hrs Hca
      isplitr
      · iexists antRaftN; iframe Hcl Hrfit
      ipureintro; exact ⟨Hns, Htr, Hmd, Hbl, HreTr, HreCfg, HreMd, HreBoot, HrN⟩
  imod bigSepL_fupd ⊤ _ (List.finRange R.N) $$ Hall with Hall
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hall with ⟨#HRO, HOwn⟩
  have Hns' : ∀ j : Fin R.N, (ds.map Prod.fst)[j.val]! = (ds[j.val]!).1 :=
    fun j => map_fst_getElem! ds j.val (by rw [Hdl]; exact j.isLt)
  ihave #Hc : antCluster cl γ $$ []
  · iunfold antCluster
    iexists cfg, rp, ds.map Prod.fst, sc
    iframe Ccfg Crec Cstop Hunk Hnj Hmu Hinv Hpm Hrdm HstInv'
    isplitr
    · ipureintro; exact Hcok
    isplitr
    · ipureintro; exact ⟨Hsc, HMR⟩
    isplitr
    · iexact HisRec
    isplitr
    · iunfold clusterRO
      iexists nsl, sl
      iframe Cnodes Hnsl Cmode CinitVoters Hsl
      ipureintro; rw [List.length_map, Hdl, HMR.1]
    isplitr
    · iapply BigSepL.bigSepL_impl $$ HRO
      iintro !> %k %j %_ H
      rw [Hns' j]
      iexact H
    isplitr
    · ipureintro; exact Hfits
    ipureintro; exact ⟨Hacks, Hwins, Hacks'⟩
  -- the node goroutines
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ c with #c
  ihave Hnadder := sync.join.ownAdder_wand
    ([∗list] j ∈ (List.finRange R.N).take 0, nodeExit cl γ j (qh (j.val + 1))) _ _ _ $$ [] Hnadder
  · iintro -; simp only [List.take_zero]; iapply (BigSepL.bigSepL_nil).2; iempintro
  wp_apply (wp_slice_for_range_ro (V := Loc) _ nsl (ds.map Prod.fst) DFrac.discard _
    (fun i => iprop(threadTok ∗ (∃ x : Loc, n_ptr ↦ x) ∗
      sync.join.ownAdder (cl.[H.Cluster, go!"nodesWg"]) (W32 (i : Int))
        ([∗list] j ∈ (List.finRange R.N).take i, nodeExit cl γ j (qh (j.val + 1))) ∗
      netAdder cl γ (qh i) ∗
      [∗list] j ∈ (List.finRange R.N).drop i, nodeOwn cl γ j (ds[j.val]!).1 (viewInit R) .down)))
    $$ Hnsl [Htok n Hnadder Had HOwn]
  · iframe Htok Hnadder
    isplitl [n]
    · iexists _; iexact n
    simp only [List.drop_zero]
    iframe HOwn
    iunfold netAdder; rw [show qh 0 = 1 from rfl]; iexact Had
  · iintro !> %i %x %hx ⟨Htk, ⟨%x0, Hn⟩, Hadder, Hq, HO⟩ #Hs
    have hi : i < R.N := by
      have := (List.getElem?_eq_some_iff.1 hx).1; simpa [Hdl] using this
    have hxe : x = (ds[i]!).1 := by
      rw [← map_fst_getElem! ds i (by rw [Hdl]; exact hi)]
      rw [getElem!_pos _ i (by simpa [Hdl] using hi)]
      exact ((List.getElem?_eq_some_iff.1 hx).2).symm
    subst hxe
    rw [finRange_drop_cons i hi]
    icases (BigSepL.bigSepL_cons).1 $$ HO with ⟨HOi, HO⟩
    ihave #HRi : nodeRO cl γ (ds[i]!).1 ⟨i, hi⟩ $$ []
    · iapply (BigSepL.bigSepL_lookup (Φ := fun _ (j : Fin R.N) => nodeRO (GF := GF) cl γ (ds[j.val]!).1 j)
        (finRange_getElem? (⟨i, hi⟩ : Fin R.N))) $$ HRO
    try wp_auto
    rw [← qh_succ i]
    iunfold netAdder at Hq
    icases njAdder_split _ _ _ _ _ $$ Hq with ⟨Hq1, Hq2⟩
    wp_apply (sync.join.WaitGroup.wp_Add_of wp_Add (nodeExit cl γ ⟨i, hi⟩ (qh (i + 1))) _ _
        (W32 (i : Int))) $$ [Hadder] as ⟨Hadder, Hdone⟩
    · iframe Hadder; ipureintro
      have : R.N ≤ 5 := by rw [HMR.1]; word
      word
    try wp_auto
    wp_apply wp_fork_tok_body $$ [HOi Hq1 Hdone]
    · iintro Htt
      wp_apply (wp_run cl γ ((ds[i]!).1) ⟨i, hi⟩ (viewInit R) (qh (i + 1)))
        $$ [$Hpkg $Hc $HRi $HOi $Htt $Hdone Hq1] as Htt
      · iunfold netAdder; iframe Hq1; ipureintro; exact h_drain mode Hsc
      iframe Htt; ipureintro; simp
    try wp_auto
    iframe Hs Htk HO
    isplitr
    · ipureintro; rfl
    isplitl [Hn]
    · iexists _; iexact Hn
    isplitl [Hadder]
    · have hw : W32 (i : Int) + W32 1 = W32 ((i + 1 : Nat) : Int) := by word
      rw [← hw]
      iapply sync.join.ownAdder_wand $$ [] Hadder
      iintro ⟨Hp, He⟩
      rw [finRange_take_succ i hi]
      iapply (BigSepL.bigSepL_snoc).2
      iframe Hp He
    iunfold netAdder; iexact Hq2
  iintro ⟨Htok, -, Hnadder, Hq, -⟩ #-
  rw [List.length_map, Hdl, List.take_of_length_le (by simp)]
  try wp_auto
  -- the behaviours
  wp_apply (wp_spawn cl (methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty) go!"proposer" #cl) (W32 0)
      iprop(True) (by decide)) $$ [$Hpkg $Hbadder $Htok] as ⟨Hbadder, Htok⟩
  · iintro Htt
    wp_apply wp_proposer cl γ $$ [$Hpkg $Hc $Htt] as Htt
    iframe Htt; ipureintro; rfl
  try wp_auto
  wp_apply (wp_spawn cl (methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty) go!"campaigner" #cl)
      (W32 0 + W32 1) _ (by decide)) $$ [$Hpkg $Hbadder $Htok] as ⟨Hbadder, Htok⟩
  · iintro Htt
    wp_apply wp_campaigner cl γ $$ [$Hpkg $Hc $Htt] as Htt
    iframe Htt; ipureintro; rfl
  ihave Hbeh : iprop(∃ k : w32, sync.join.ownAdder (cl.[H.Cluster, go!"behWg"]) k iprop(True) ∗
      ⌜uint.Z k ≤ 2⌝) $$ [Hbadder]
  · iexists _
    isplitl [Hbadder]
    · iapply sync.join.ownAdder_wand $$ [] Hbadder; iintro -; itrivial
    ipureintro; decide
  try wp_auto
  -- with reads, the reader (its contexts: none handed out yet)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ threadTok ∗ ∃ k : w32,
      sync.join.ownAdder (cl.[H.Cluster, go!"behWg"]) k iprop(True) ∗ ⌜uint.Z k ≤ 3⌝)))
    $$ [Htok Hbeh Hra HU]
  · icases Hbeh with ⟨%k, Hbeh, %Hk⟩
    cases Hif : mode.Reads'
    rotate_left
    · try wp_auto
      wp_apply (wp_spawn cl (methods (go.GoType.PointerType
          github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty) go!"reader" #cl)
          k _ (by word)) $$ [$Hpkg $Hbeh $Htok Hra HU] as ⟨Hbeh, Htok⟩
      · iintro Htt
        wp_apply wp_reader cl γ $$ [$Hpkg $Hc $Htt Hra HU] as Htt
        · iunfold readerOwn
          rw [show uint.nat (W64 1) - 1 = 0 from rfl]
          isplitl [Hra HU]
          · isplitl [Hra]
            · iExactEq Hra; rfl
            isplitl [HU]
            · iExactEq HU; rfl
            iexists antRaftN; iexact Hcl
          ipureintro; exact Hif
        iframe Htt; ipureintro; rfl
      try wp_auto
      iframe Htok
      isplitr
      · ipureintro; rfl
      iexists _
      isplitl [Hbeh]
      · iapply sync.join.ownAdder_wand $$ [] Hbeh; iintro -; itrivial
      ipureintro; word
    · try wp_auto
      iframe Htok
      isplitr
      · ipureintro; rfl
      iexists k
      iframe Hbeh
      ipureintro; word
  iintro %v ⟨%hv, Htok, Hbeh⟩
  subst hv
  try wp_auto
  -- with transfers, the transferer
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ threadTok ∗ ∃ k : w32,
      sync.join.ownAdder (cl.[H.Cluster, go!"behWg"]) k iprop(True) ∗ ⌜uint.Z k ≤ 4⌝)))
    $$ [Htok Hbeh]
  · icases Hbeh with ⟨%k, Hbeh, %Hk⟩
    cases Hif : mode.Transfer'
    rotate_left
    · try wp_auto
      wp_apply (wp_spawn cl (methods (go.GoType.PointerType
          github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty) go!"transferer" #cl)
          k _ (by word)) $$ [$Hpkg $Hbeh $Htok] as ⟨Hbeh, Htok⟩
      · iintro Htt
        wp_apply wp_transferer cl γ $$ [$Hpkg $Hc $Htt] as Htt
        · ipureintro; exact Hif
        iframe Htt; ipureintro; rfl
      try wp_auto
      iframe Htok
      isplitr
      · ipureintro; rfl
      iexists _
      isplitl [Hbeh]
      · iapply sync.join.ownAdder_wand $$ [] Hbeh; iintro -; itrivial
      ipureintro; word
    · try wp_auto
      iframe Htok
      isplitr
      · ipureintro; rfl
      iexists k
      iframe Hbeh
      ipureintro; word
  iintro %v ⟨%hv, Htok, Hbeh⟩
  subst hv
  -- B2/B3's behaviours are off
  obtain ⟨hBa, hAs, -, -, -, hRe, -, -⟩ := h_drain mode Hsc
  have hSn : mode.Snapshots' = false := by
    have h := Hsc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cases hm : mode.Snapshots'
    · rfl
    · exact absurd (h hm) (by simp [b1Scope])
  have hCC : mode.ConfChanges' = false := by
    have h := Hsc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cases hm : mode.ConfChanges'
    · rfl
    · exact absurd (h hm) (by simp [b1Scope])
  try wp_auto
  rw [hCC]
  try wp_auto
  rw [hSn]
  try wp_auto
  rw [hRe]
  try wp_auto
  rw [hBa]
  try wp_auto
  rw [hAs]
  try wp_auto
  -- the stop
  wp_apply wp_Sleep
  try wp_auto
  wp_apply wp_broadcast_chan_close sc γ.stopCh iprop(True) $$ [$Hpend] as -
  · iintro !>; itrivial
  try wp_auto
  icases Hbeh with ⟨%kb, Hbeh, -⟩
  wp_apply (sync.join.WaitGroup.wp_Wait_of wp_Wait _ _ _) $$ [$Hsy $Hbeh] as -
  try wp_auto
  wp_apply (lc := 1) (sync.join.WaitGroup.wp_Wait_of wp_Wait _ _ _) $$ [$Hsy $Hnadder]
    as ⟨Hex, -⟩
  imod lc_fupd_elim_later $$ Hlc1 Hex with Hex
  unfold nodeExit
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hex with ⟨Hlives, Hads⟩
  ihave Hall := adders_join cl γ R.N (Nat.le_refl _) $$ [Hq Hads]
  · rw [List.take_of_length_le (by simp only [List.length_finRange]; exact Nat.le_refl _)]
    iframe Hq Hads
  iunfold netAdder at Hall
  imod njClose antNetN _ γ.net $$ Hall with ⟨Hw0, #Hnj'⟩
  -- the run is over
  imod antInv_close γ $$ Hinv Hlives with ⟨%evs, Hdone, %Hacc⟩
  try wp_auto
  wp_apply netJoin.wp_Wait_of wp_Wait antNetN _ γ.net $$ [$Hsy $Hw0 $Hnj']
  try wp_auto
  iapply HΦ
  iframe Htok
  iunfold runOver
  iexists rp, strm, evs, mode, R
  iframe Crec HisRec Hdone Cmode
  ipureintro
  exact ⟨Hsc, HMR, Hacc⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
