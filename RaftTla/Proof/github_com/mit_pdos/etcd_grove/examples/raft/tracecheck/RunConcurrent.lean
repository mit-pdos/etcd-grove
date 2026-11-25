/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/RunConcurrent.lean`. Lean-first
(no Rocq counterpart). Trace-check's layer D (the harness, 2026-11-12; `notes/trace-check-design.md`
§2.2).
-/
module

public import RaftTla.Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent
public import RaftTla.Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__app
public import RaftTla.Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__TraceEvent
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Logger
public import RaftTla.Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import RaftTla.Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.below
public import RaftTla.Spec.go_etcd_io.raft.v3.node__Propose
public import RaftTla.Spec.go_etcd_io.raft.v3.node__Stop
public import Spec.strconv.Itoa
public import Spec.context.WithTimeoutBackground
public import Perennial.Proof.time.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
public import RaftTla.Proof.go_etcd_io.raft.v3.InvTraceLogger

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 ProbeA TraceSim

/-- The first `m` peers `Peer{ID: i}` (`i = 1 … m`, `Context` nil). -/
def tcPeers [GooseExts] (m : Nat) : List Peer :=
  (List.range m).map fun j => ⟨W64 ((j : Nat) + 1), slice.nil⟩

theorem tcPeers_succ [GooseExts] (m : Nat) :
    tcPeers (m + 1) = tcPeers m ++ [⟨W64 ((m : Nat) + 1), slice.nil⟩] := by
  unfold tcPeers; rw [List.range_succ, List.map_append]; rfl

theorem tcPeers_ids [GooseExts] (m : Nat) : (tcPeers m).map Peer.ID' = tcVoters m := by
  unfold tcPeers tcVoters tracecheck.bootVoters; rw [List.map_map]; rfl

theorem tcPeers_length [GooseExts] (m : Nat) : (tcPeers m).length = m := by
  simp [tcPeers]

/-- The first voter heads the list. -/
theorem tcVoters_cons [GooseExts] (nv : Nat) (h : 1 ≤ nv) :
    tcVoters nv = W64 1 :: (tcVoters nv).drop 1 := by
  have h0 : (tcVoters nv)[0]? = some (W64 1) := by
    simp [tcVoters, tracecheck.bootVoters, show 0 < nv by omega]
  cases hl : tcVoters nv with
  | nil => rw [hl] at h0; simp at h0
  | cons a t => rw [hl] at h0; simp at h0; subst h0; rfl

/-- `sint.Z` of a voter count (at most `maxNodes`). -/
theorem tc_sZ [GooseExts] (nv : Nat) (h : nv ≤ 5) :
    sint.Z (W64 nv) = nv ∧ sint.Z (W64 nv + W64 0) = nv := by
  rcases (by omega : nv = 0 ∨ nv = 1 ∨ nv = 2 ∨ nv = 3 ∨ nv = 4 ∨ nv = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem tc_peers_succ [GooseExts] (k : w64) (h1 : 1 ≤ sint.Z k) (h2 : sint.Z k ≤ 5) :
    W64 ((sint.nat k - 1 : Nat) + 1) = k ∧ sint.nat (k + W64 1) - 1 = (sint.nat k - 1) + 1 := by
  constructor <;> word

section logger
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- The harness's `quietLogger{}` meets raft's `Logger` contract: its formatting methods return. -/
theorem tcLogger_isLogger :
    ⊢ isLogger (GF := GF) ⟨github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.quietLogger.ty,
        #(zero_val github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.quietLogger)⟩ := by
  unfold isLogger
  iintro %meth %Hmeth %format %args
  simp only [logMethods, List.mem_cons, List.not_mem_nil, or_false] at Hmeth
  rcases Hmeth with rfl | rfl | rfl | rfl <;>
  · dsimp only
    imodintro
    iintro %Φ - HΦ
    wp_method_call
    wp_auto
    iapply HΦ
    itrivial

/-- The peers' contexts: none (`Peer{ID: i}`: each `nil`). -/
theorem tcPeers_ctx0 [StorageModel GF] (m : Nat) :
    ⊢ [∗list] p ∈ tcPeers m,
        iprop(p.Context' ↦*□ ([] : List w8) ∗ ⌜([] : List w8) = [] → p.Context' = slice.nil⌝ : IProp GF) := by
  induction m with
  | zero =>
    unfold tcPeers; simp only [List.range_zero, List.map_nil]
    iintro
    iapply (BigSepL.bigSepL_nil).2; iempintro
  | succ m ih =>
    rw [tcPeers_succ]
    iintro
    iapply (BigSepL.bigSepL_append).2
    isplitl []
    · iapply ih
    iapply (BigSepL.bigSepL_cons).2
    isplitl []
    · isplitl []
      · iapply ownSlice_nil
      · ipureintro; intro _; rfl
    iapply (BigSepL.bigSepL_nil).2; iempintro

theorem tcPeers_ctx [StorageModel GF] (m : Nat) : ⊢ peersCtx (GF := GF) (tcPeers m) (tcCtxs m) := by
  unfold peersCtx
  have h := (tcPeers_ctx0 (GF := GF) m).trans (BigSepL2.bigSepL2_replicate_right
    (Φ := fun _ (p : Peer) (ctx : List w8) =>
      iprop(p.Context' ↦*□ ctx ∗ ⌜ctx = [] → p.Context' = slice.nil⌝ : IProp GF))
    (l := tcPeers m) (x := ([] : List w8))).2
  rw [tcPeers_length] at h
  exact h

/-- `StartNode`'s update over the voter's durable state, fired at once (the state is `init`). -/
theorem tc_startAu [StorageModel GF] (γ : Cluster) (N : Namespace) (id : w64) :
    ⊢ raftState (GF := GF) γ id RaftState.init -∗
      AU <{ ∃∃ (S : RaftState), raftState γ id S ∗ ⌜S = RaftState.init⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ id S, COMM raftState γ id RaftState.init }> := by
  iintro Hrs
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑N from Std.LawfulSet.empty_subset)
  iintro Hclose
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists RaftState.init
  iframe Hrs
  isplitr
  · ipureintro; rfl
  isplit
  · iintro ⟨Hrs, -⟩
    imod Hclose with -
    imodintro
    iexact Hrs
  · iintro Hrs
    imod Hclose with -
    imodintro
    iexact Hrs

end logger

section repstart
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [MemStorReg GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

attribute [local instance] memStorageModel

/-- **A replica as `RunConcurrent` made it**, before its `app` starts: its read-only part, its
fields, its storage's metadata, its node idle at the start, and its completion witness. -/
def repStart (nv : Nat) (γ : Cluster) (r : Loc) (id : w64) (ms : Loc) : IProp GF :=
  iprop(∃ (n : NodeH) (γs : MemStorNames) (K : GName),
    repInfo γ r id n ms γs ∗ repOwn r ∗ memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
    nodeDriver n γ tcRaftN (NodeDriverState.init (memStorIface ms) K) ∗
    raftState γ id RaftState.init ∗ nodeConfig n γ tcRaftN ⟨0, tcMem nv⟩ ∗
    nodeRunning n γ tcRaftN 1 ∗ startDone γ id)

/-- A storage registered for a replica made is not fresh. -/
theorem repStart_fresh (nv : Nat) (γ : Cluster) (ds : List (Loc × Loc)) (ms : Loc) (γs : MemStorNames)
    (hs : HardStateM) (h : ms ∈ ds.map Prod.snd) :
    ⊢ ([∗list] j ↦ d ∈ ds, repStart (GF := GF) nv γ d.1 (W64 ((j : Nat) + 1)) d.2) -∗
      memStorMeta ms γs hs -∗ False := by
  iintro Hd Hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
  obtain ⟨j, hj, hjd⟩ := List.getElem_of_mem hd
  ihave Hj := BigSepL.bigSepL_lookup
    (Φ := fun j d => repStart (GF := GF) nv γ d.1 (W64 ((j : Nat) + 1)) d.2)
    (List.getElem?_eq_some_iff.2 ⟨hj, hjd⟩) $$ Hd
  iunfold repStart at Hj
  icases Hj with ⟨%n, %γs', %K, -, -, Hm', -⟩
  iapply memStorMeta_excl d.2 γs γs' hs _ $$ Hm Hm'

/-- A replica made has its node. -/
theorem repStart_node (nv : Nat) (γ : Cluster) (r : Loc) (id : w64) (ms : Loc) :
    repStart (GF := GF) nv γ r id ms ⊢ repNode γ r id ∗ repStart nv γ r id ms := by
  iintro H
  iunfold repStart at H
  icases H with ⟨%n, %γs, %K, #Hri, Hrest⟩
  ihave #Hri' := Hri
  iunfold repInfo at Hri'
  icases Hri' with ⟨-, #Hnf, -, #Hn, -⟩
  isplitr
  · iunfold repNode
    iexists n
    iframe Hnf Hn
  iunfold repStart
  iexists n, γs, K
  iframe Hri Hrest

/-- The replicas made have their nodes. -/
theorem repStarts_nodes (nv : Nat) (γ : Cluster) (ds : List (Loc × Loc)) :
    ([∗list] j ↦ d ∈ ds, repStart (GF := GF) nv γ d.1 (W64 ((j : Nat) + 1)) d.2) ⊢
      ([∗list] j ↦ r ∈ ds.map Prod.fst, repNode γ r (W64 ((j : Nat) + 1))) ∗
      [∗list] j ↦ d ∈ ds, repStart nv γ d.1 (W64 ((j : Nat) + 1)) d.2 := by
  rw [BigSepL.bigSepL_map]
  refine (BigSepL.bigSepL_mono_of_forall ?_).trans BigSepL.bigSepL_sep_eqv.1
  intro j d
  exact repStart_node nv γ d.1 (W64 ((j : Nat) + 1)) d.2

/-- The replicas made have their completion witnesses. -/
theorem repStarts_dones (nv : Nat) (γ : Cluster) (ds : List (Loc × Loc)) :
    ([∗list] j ↦ d ∈ ds, repStart (GF := GF) nv γ d.1 (W64 ((j : Nat) + 1)) d.2) ⊢
      ([∗list] j ↦ _d ∈ ds, startDone γ (W64 ((j : Nat) + 1))) ∗
      [∗list] j ↦ d ∈ ds, repStart nv γ d.1 (W64 ((j : Nat) + 1)) d.2 := by
  refine (BigSepL.bigSepL_mono_of_forall ?_).trans BigSepL.bigSepL_sep_eqv.1
  intro j _
  iintro H
  iunfold repStart at H
  icases H with ⟨%n, %γs, %K, Hri, Hown, Hm, Hd, Hr, Hc, Hrun, #Hsd⟩
  isplitr
  · iexact Hsd
  iunfold repStart
  iexists n, γs, K
  iframe Hri Hown Hm Hd Hr Hc Hrun Hsd

/-- The `StartNode`s' witnesses, at the voters. -/
theorem tc_startDones (γ : Cluster) (ds : List (Loc × Loc)) (nv : Nat) (hl : ds.length = nv) :
    □ ([∗list] j ↦ _d ∈ ds, startDone (GF := GF) γ (W64 ((j : Nat) + 1))) ⊢
      [∗list] i ∈ tcVoters nv, startDone γ i := by
  refine BigSepL.bigSepL_intro fun k x hx => ?_
  have hk : k < nv := by
    have := (List.getElem?_eq_some_iff.1 hx).1; rwa [tcVoters_length] at this
  have hxk : W64 ((k : Nat) + 1) = x := by
    simpa [tcVoters, tracecheck.bootVoters, List.getElem?_map, List.getElem?_range, hk] using hx
  subst hxk
  obtain ⟨d, hd⟩ : ∃ d, ds[k]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  exact intuitionistically_elim.trans
    (BigSepL.bigSepL_lookup (Φ := fun j (_ : Loc × Loc) => startDone (GF := GF) γ (W64 ((j : Nat) + 1))) hd)

end repstart

/-- The configuration `RunConcurrent` starts replica `id` with, on the storage `ms`, logging to the
recorder `rec`. -/
abbrev tcConfig [GooseExts] [GoGlobalContext] (id : w64) (ms rl : Loc) : Config :=
  { ID' := id, ElectionTick' := W64 10, HeartbeatTick' := W64 1,
    Storage' := interface.mkOk (go.GoType.PointerType MemoryStorage.ty) #ms, Applied' := 0,
    AsyncStorageWrites' := false, MaxSizePerMsg' := ~~~W64 0, MaxCommittedSizePerReady' := 0,
    MaxUncommittedEntriesSize' := 0, MaxInflightMsgs' := W64 256, MaxInflightBytes' := 0,
    CheckQuorum' := false, PreVote' := false, ReadOnlyOption' := 0,
    Logger' := interface.mkOk github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.quietLogger.ty
      #(zero_val github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.quietLogger),
    DisableProposalForwarding' := false, DisableConfChangeValidation' := false,
    StepDownOnRemoval' := false,
    TraceLogger' := interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder.ty)
      #rl }

theorem tcConfig_valid [GooseExts] [GoGlobalContext] (id : w64) (ms rl : Loc)
    (h1 : 1 ≤ sint.Z id) (h2 : sint.Z id ≤ 5) : ConfigValid (tcConfig id ms rl) := by
  unfold ConfigValid
  refine ⟨?_, ?_, ?_, ⟨by show (0 : Int) < sint.Z (W64 1); decide, by show sint.Z (W64 1) < sint.Z (W64 10); decide⟩, by simp, by show (0 : Int) < sint.Z (W64 256); decide, Or.inl rfl, by simp, Or.inl rfl⟩
    <;> (intro h; subst h; revert h1 h2; decide)

theorem tcVoters_drop [GooseExts] (nv : Nat) (k : w64) (h1 : 1 ≤ sint.Z k) (h2 : sint.Z k ≤ nv)
    (h5 : nv ≤ 5) :
    (tcVoters nv).drop (sint.nat k - 1) = k :: (tcVoters nv).drop (sint.nat k) := by
  have hlt : sint.nat k - 1 < (tcVoters nv).length := by rw [tcVoters_length]; word
  rw [List.drop_eq_getElem_cons hlt]
  have hk : sint.nat k - 1 + 1 = sint.nat k := by word
  rw [hk]
  congr 1
  simp only [tcVoters, tracecheck.bootVoters, List.getElem_map, List.getElem_range]
  word

theorem tc_rep_step [GooseExts] (nv : Nat) (h5 : nv ≤ 5) (k : w64) (h1 : 1 ≤ sint.Z k)
    (h2 : sint.Z k ≤ nv) :
    (tcVoters nv).drop (sint.nat k - 1) = k :: (tcVoters nv).drop (sint.nat k) ∧
      sint.nat (k + W64 1) - 1 = sint.nat k ∧ 1 ≤ sint.Z (k + W64 1) ∧
      sint.Z (k + W64 1) ≤ nv + 1 ∧ W64 ((sint.nat k - 1 : Nat) + 1) = k ∧
      sint.nat k - 1 + 1 = sint.nat k :=
  ⟨tcVoters_drop nv k h1 h2 h5, by word, by word, by word, by word, by word⟩

theorem tc_rep_le [GooseExts] (nv : Nat) (h5 : nv ≤ 5) (k : w64) (n x : w64) (hn : n = W64 nv)
    (hx : x = W64 0) (h : sint.Z k ≤ sint.Z (n + x)) : sint.Z k ≤ nv := by
  subst hn hx; rw [(tc_sZ nv h5).2] at h; exact h

theorem tc_reps_end [GooseExts] (nv : Nat) (h5 : nv ≤ 5) (k n x : w64) (hn : n = W64 nv)
    (hx : x = W64 0) (h1 : sint.Z k ≤ nv + 1) (h2 : ¬ sint.Z k ≤ sint.Z (n + x)) :
    sint.nat k - 1 = nv := by
  subst hn hx; rw [(tc_sZ nv h5).2] at h2; word

/-- Halves: `1, 1/2, 1/4, …`. -/
def halves : Nat → Qp
  | 0 => 1
  | k + 1 => (halves k).half

theorem halves_succ_add (k : Nat) : halves (k + 1) + halves (k + 1) = halves k := by
  simp only [halves, Qp.half_add_half]

/-- The shares of the network join's adders' right the `nv` `app`s hold: `1/2, 1/4, …`, the last two
equal (at three voters `1/2, 1/4, 1/4`, as until 2026-11-24). -/
def tcQ (nv j : Nat) : Qp := if j + 1 < nv then halves (j + 1) else halves j

theorem tc_apps_step [GooseExts] (nv : Nat) (h5 : nv ≤ 5) (k : w64) (len : w64) (h0 : 0 ≤ sint.Z k)
    (h : sint.Z k < sint.Z len) (hl : sint.nat len = nv) :
    sint.nat k < nv ∧ 0 ≤ sint.Z (k + W64 1) ∧ sint.nat (k + W64 1) = sint.nat k + 1 ∧
      sint.Z (k + W64 1) ≤ nv ∧ (sint.Z k).toNat = sint.nat k ∧ W64 ((sint.nat k : Nat) + 1) = k + W64 1 ∧
      sint.Z k < 2 ^ 31 - 1 := by
  refine ⟨by word, by word, by word, by word, by word, by word, by word⟩

theorem tc_na_succ [GooseExts] (na : w32) (k : w64) (h : sint.Z na = sint.Z k)
    (h1 : sint.Z k < 2 ^ 31 - 1) (h0 : 0 ≤ sint.Z k) : sint.Z (na + W32 1) = sint.Z (k + W64 1) := by
  word

theorem tc_apps_end [GooseExts] (nv : Nat) (k len : w64) (h1 : sint.Z k ≤ nv)
    (h : ¬ sint.Z k < sint.Z len) (hl : sint.nat len = nv) : sint.nat k = nv := by word

theorem tc_len [GooseExts] (nv : Nat) (h1 : 1 ≤ nv) (len : w64) {α : Type} (l : List α)
    (h : l.length = sint.nat len) (hn : l.length = nv) : sint.Z len = nv := by
  rw [hn] at h; word

theorem tc_pick [GooseExts] (nv : Nat) (b len : w64) (h0 : 0 ≤ sint.Z b) (h1 : sint.Z b < nv)
    (_hl : sint.Z len = nv) :
    ∃ j : Nat, j < nv ∧ (sint.Z b).toNat = j ∧ W64 ((j : Nat) + 1) = b + W64 1 :=
  ⟨sint.nat b, by word, by word, by word⟩

/-- The drivers' join. -/
def tcDrvN : Namespace := nroot.@"tc_drivers"

theorem tc_peers_end [GooseExts] (nv : Nat) (h5 : nv ≤ 5) (k : w64) (h1 : sint.Z k ≤ nv + 1)
    (h2 : ¬ sint.Z k ≤ sint.Z (W64 nv)) : sint.nat k - 1 = nv := by
  rw [(tc_sZ nv h5).1] at h2; word

section apps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- The `app`s' shares, split off a share `halves k`. -/
theorem njAdder_split_all (N : Namespace) (wg : Loc) (γ : NetJoinNames) (nv : Nat) (d : Nat) :
    ∀ k, k + d + 1 = nv → njAdder (GF := GF) N wg γ (halves k) ⊢
      [∗list] j ∈ List.range' k (nv - k), njAdder N wg γ (tcQ nv j) := by
  induction d with
  | zero =>
    intro k hk
    rw [show nv - k = 0 + 1 by omega, List.range'_succ, List.range'_zero]
    iintro H
    iapply (BigSepL.bigSepL_cons).2
    isplitl [H]
    · simp only [tcQ, show ¬ (k + 1 < nv) by omega, ite_false]; iexact H
    iapply (BigSepL.bigSepL_nil).2; iempintro
  | succ d ih =>
    intro k hk
    rw [show nv - k = (nv - (k + 1)) + 1 by omega, List.range'_succ]
    iintro H
    icases njAdder_split N wg γ (halves (k + 1)) (halves (k + 1)) $$ [H] with ⟨H1, H2⟩
    · rw [halves_succ_add]; iexact H
    iapply (BigSepL.bigSepL_cons).2
    isplitl [H1]
    · simp only [tcQ, show k + 1 < nv by omega, ite_true]; iexact H1
    iapply ih (k + 1) (by omega) $$ H2

/-- The `app`s' shares, joined back into `halves k`. -/
theorem njAdder_join_all (N : Namespace) (wg : Loc) (γ : NetJoinNames) (nv : Nat) (d : Nat) :
    ∀ k, k + d + 1 = nv → ([∗list] j ∈ List.range' k (nv - k), njAdder (GF := GF) N wg γ (tcQ nv j)) ⊢
      njAdder N wg γ (halves k) := by
  induction d with
  | zero =>
    intro k hk
    rw [show nv - k = 0 + 1 by omega, List.range'_succ, List.range'_zero]
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨H, -⟩
    simp only [tcQ, show ¬ (k + 1 < nv) by omega, ite_false]; iexact H
  | succ d ih =>
    intro k hk
    rw [show nv - k = (nv - (k + 1)) + 1 by omega, List.range'_succ]
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨H1, H2⟩
    ihave H2 := ih (k + 1) (by omega) $$ H2
    have Hj := njAdder_join (GF := GF) N wg γ (halves (k + 1)) (halves (k + 1))
    rw [halves_succ_add] at Hj
    iapply Hj
    isplitl [H1]
    · simp only [tcQ, show k + 1 < nv by omega, ite_true]; iexact H1
    iexact H2

theorem njAdder_split_one (N : Namespace) (wg : Loc) (γ : NetJoinNames) (nv : Nat) (h : 1 ≤ nv) :
    njAdder (GF := GF) N wg γ 1 ⊢ [∗list] j ∈ List.range' 0 nv, njAdder N wg γ (tcQ nv j) := by
  have := njAdder_split_all (GF := GF) N wg γ nv (nv - 1) 0 (by omega)
  rw [Nat.sub_zero] at this
  exact this

theorem njAdder_join_one (N : Namespace) (wg : Loc) (γ : NetJoinNames) (nv : Nat) (h : 1 ≤ nv) :
    ([∗list] j ∈ List.range nv, njAdder (GF := GF) N wg γ (tcQ nv j)) ⊢ njAdder N wg γ 1 := by
  have := njAdder_join_all (GF := GF) N wg γ nv (nv - 1) 0 (by omega)
  rw [Nat.sub_zero] at this
  rw [List.range_eq_range']
  exact this

/-- The first voter's part, and the others'. -/
theorem tcVoters_head (Φ : w64 → IProp GF) (nv : Nat) (h : 1 ≤ nv) :
    ([∗list] i ∈ tcVoters nv, Φ i) ⊣⊢ Φ (W64 1) ∗ [∗list] i ∈ (tcVoters nv).drop 1, Φ i := by
  obtain ⟨rest, hr⟩ : ∃ rest, tcVoters nv = W64 1 :: rest := ⟨_, tcVoters_cons nv h⟩
  rw [hr, List.drop_one, List.tail_cons]
  exact BigSepL.bigSepL_cons

end apps

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

theorem RunConcurrent.wp_proof
    (wp_StartNode : ∀ [StorageModel GF], StartNode.tracedSpec (GF := GF))
    (wp_app : ∀ [MemStorReg GF], Cluster.app.spec (GF := GF) (hG := hG))
    (wp_TraceEvent : SyncRecorder.TraceEvent.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_Propose : ∀ [StorageModel GF], node.Propose.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ [StorageModel GF], node.Stop.spec (GF := GF) (hG := hG))
    (wp_Itoa : strconv.Itoa.spec (GF := GF) (hG := hG))
    (wp_WT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    RunConcurrent.spec (GF := GF) (hG := hG) := by
  intro _ Hrb0 nv boot Hbf cfg Hwl
  have Hrb := Hrb0.le
  wp_start as ⟨#Hcc, #Hprem⟩
  ihave #Hsy : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  try wp_auto
  -- the stop channel, a broadcast
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsch, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsch Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  try wp_auto
  -- the cluster's fields
  icases typedPointsto_split _ _ _ $$ «$r0» with Hcl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcl with ⟨Fcfg, Frec, Freps, Fstop, Fiso, Fapps, Fnet, FP, FD, FX, FR, FC, FS, -⟩
  generalize «$r0_ptr» = cl
  -- the configuration's fields, read-only
  icases typedPointsto_split _ _ _ $$ cfg with Hcf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcf with ⟨CNodes, CExtra, CProps, CConfs, CGap, CSettle, CTick, CMax, CDrop, CSnap, CIso,
    CIsoFor, -⟩
  ipersist CNodes
  ipersist CExtra
  ipersist CProps
  ipersist CConfs
  ipersist CGap
  ipersist CSettle
  ipersist CTick
  ipersist CMax
  ipersist CDrop
  ipersist CSnap
  ipersist CIso
  ipersist CIsoFor
  obtain ⟨HN3, HX0, HC0, HS0, HM0, HM1, HT0, H1, H5⟩ := Hwl
  have H5' : nv ≤ 5 := H5
  -- the peers
  ihave IHp : iprop(∃ (k : w64) (sl : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "peers" ∷ peers_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* tcPeers (sint.nat k - 1) ∗
      "Hcap" ∷ ownSliceCap Peer sl (DFrac.own 1) ∗ "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ nv + 1⌝)
    $$ [i peers]
  · iexists W64 1, zero_val GoSlice
    iframe i peers
    rw [show sint.nat (W64 1) - 1 = 0 from rfl]
    isplitl
    · unfold tcPeers; simp only [List.range_zero, List.map_nil]; iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    ipureintro
    have : sint.Z (W64 1) = 1 := by decide
    constructor <;> omega
  wp_for IHp
  wp_if_destruct
  · try wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Peer.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Peer) (t := Peer.ty) [⟨k, slice.nil⟩]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression Peer.ty #(⟨k, slice.nil⟩ : Peer))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Htmp, -⟩
    wp_auto
    wp_apply wp_slice_append (V := Peer) (t := Peer.ty) sl _ _ [⟨k, slice.nil⟩] (DFrac.own 1)
      $$ [Hsl Hcap Htmp] as %sl' ⟨Hsl', Hcap', -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    have Hle : sint.Z k ≤ nv := by rw [HN3, (tc_sZ nv H5').1] at Hif; exact Hif
    obtain ⟨Hk1, Hk2⟩ := tc_peers_succ k Hk.1 (by omega)
    iexists k + W64 1, sl'
    rw [Hk2, tcPeers_succ, Hk1]
    iframe
    ipureintro; constructor <;> word
  · -- the peers built: the `nv` voters'
    have Hk3 : sint.nat k - 1 = nv := tc_peers_end nv H5' k Hk.2 (by
      intro h; apply Hif; rw [HN3]; simp only [h])
    ihave Hsl : sl ↦* tcPeers nv $$ [Hsl]
    · rw [← Hk3]; iexact Hsl
    try wp_auto
    -- the recorder and its trace
    ihave Hra := syncRecorder_alloc «$v1_ptr» ⊤ $$ Hpkg
    imod Hra $$ «$v1» with ⟨%γt, #Hrec, Hfr⟩
    ihave #Htl := isSyncRecorder_traceLogger wp_TraceEvent γt «$v1_ptr» $$ Hrec
    -- the storage registry
    imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%γreg, Hreg⟩
    letI : MemStorReg GF := ⟨γreg⟩
    letI : StorageModel GF := memStorageModel
    -- the traced cluster, with the harness's invariants
    imod probeA_alloc tcRaftN nv H1 H5 boot γt ⊤ (fun _ _ => CoPset.mem_full) (by omega) Hbf $$ Hprem Hfr
      with ⟨%γ, %γd, %tn, %Hγ, #Hdir, #Hsim, #Hcl, #Hops, #Hpol, #Hsn, #Hca0, #Hboot, Hvs⟩
    obtain ⟨Htr, Htn, Hvoters, Hsl0, Hdup, Hbl, Hmd⟩ := Hγ
    ihave #Hlog := tcLogger_isLogger (GF := GF)
    icases (tcVoters_head (fun i => voterStart (GF := GF) γ tcRaftN (tcVoters nv) (tcCtxs nv) tn i)
        nv H1).1 $$ Hvs with ⟨Hv1, Hvs⟩
    iunfold voterStart at Hv1
    icases Hv1 with ⟨#Hnb1, Hv1⟩
    ihave Hvs := (tcVoters_head (fun i =>
        voterStart (GF := GF) γ tcRaftN (tcVoters nv) (tcCtxs nv) tn i) nv H1).2 $$ [Hv1 Hvs]
    · iframe Hvs
      iunfold voterStart
      iframe Hnb1 Hv1
    -- the replicas
    ihave IHr : iprop(∃ (k : w64) (rsl : GoSlice) (ds : List (Loc × Loc))
        (M : GMap Loc MemStorNamesRec),
        "i" ∷ i_ptr ↦ k ∗
        "Freps" ∷ cl.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster,
          go!"replicas"] ↦ rsl ∗
        "Hrsl" ∷ rsl ↦* ds.map Prod.fst ∗ "Hrcap" ∷ ownSliceCap Loc rsl (DFrac.own 1) ∗
        "Hreg" ∷ memStorRegAuth M ∗ "Hsl" ∷ sl ↦* tcPeers nv ∗
        "Hdone" ∷ ([∗list] j ↦ d ∈ ds, repStart nv γ d.1 (W64 ((j : Nat) + 1)) d.2) ∗
        "Htodo" ∷ ([∗list] id ∈ (tcVoters nv).drop (sint.nat k - 1),
          voterStart γ tcRaftN (tcVoters nv) (tcCtxs nv) tn id) ∗
        "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ nv + 1 ∧ ds.length = sint.nat k - 1 ∧
          ∀ l, M.lookup l ≠ none → l ∈ ds.map Prod.snd⌝)
      $$ [i Freps Hreg Hsl Hvs]
    · iexists W64 1, slice.nil, [], ∅
      iframe i Freps Hsl
      rw [show sint.nat (W64 1) - 1 = 0 from rfl, List.drop_zero]
      iframe Hvs
      isplitl []
      · simp only [List.map_nil]; iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      isplitl [Hreg]
      · unfold memStorRegAuth; iexact Hreg
      isplitl []
      · iapply (BigSepL.bigSepL_nil).2; iempintro
      ipureintro
      have : sint.Z (W64 1) = 1 := by decide
      refine ⟨by omega, by omega, rfl, fun l h => absurd (GMap.lookup_empty l) h⟩
    wp_for IHr
    wp_if_destruct
    · -- one more replica: its storage, registered
      try wp_auto
      wp_apply wp_NewMemoryStorage false as %ms %γs ⟨%Hsz, #Hlock, #Hlog0, Hend, -, Hmeta, Hfresh⟩
      cases HM : M.lookup ms with
      | some x =>
        iexfalso
        iapply repStart_fresh nv γ ds ms γs _ (Hk.2.2.2 ms (by rw [HM]; simp)) $$ Hdone Hmeta
      | none =>
      imod memStorReg_register M ms γs HM $$ Hreg with ⟨Hreg, #Hrg⟩
      try wp_auto
      have Hk3 : sint.Z k ≤ nv := tc_rep_le nv H5' k cfg.Nodes' cfg.ExtraNodes' HN3 HX0 Hif
      obtain ⟨Hdrop, Hk1, Hs1, Hs4, HkW, Hkk⟩ := tc_rep_step nv H5' k Hk.1 Hk3
      rw [Hdrop]
      icases Htodo with ⟨Hvk, Htodo⟩
      -- the voter's part, its trace logger
      ihave #Htl' : isTraceLogger tn.tr (tcConfig k ms «$v1_ptr»).TraceLogger' $$ []
      · rw [Htn]; iexact Htl
      have Hbln : boot.length = nv := by rw [Hbf.1]; exact tcVoters_length nv
      ihave Hsp := probeA_startPre nv H5 γ tcRaftN γd tn (tcConfig k ms «$v1_ptr») Htr Hvoters rfl rfl
        (by simp) (by rw [Hbl, Hbln]; omega) $$ Hvk Hdir Hsim Htl'
      icases Hsp with ⟨#Hnb, Hvac, Hrs0, Hstc⟩
      -- (2026-11-21, the crash invariant) the vacancy armed (the harness never crashes)
      imod nodeVacant_armD γ k ⊤ $$ Hvac with ⟨%x, Hvac⟩
      ihave Hau := tc_startAu γ tcRaftN k $$ Hrs0
      ihave Hboot := tc_bootStorage wp_InitialState wp_LastIndex wp_FirstIndex wp_Term wp_Entries
        wp_Snapshot ms γs γ (fun _ => memStorMeta ms γs tcBootContents.hs)
        (fun h => by simp [Hmd] at h)
        $$ Hrg Hlock Hfresh Hmeta Hlog0 Hend []
      · iintro %K Hm -; iexact Hm
      ihave #Hpctx := tcPeers_ctx (GF := GF) nv
      ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
      · iPkgInit
      wp_if_destruct
      · -- `StartNode`
        try wp_auto
        wp_apply (wp_StartNode γ tcRaftN (tcVoters nv) (tcCtxs nv) «$r0_ptr» (tcConfig k ms «$v1_ptr»)
            ⟨github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.quietLogger.ty,
              #(zero_val github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.quietLogger)⟩
            ⟨go.GoType.PointerType MemoryStorage.ty, #ms⟩ memSnapEmpty.Metadata'.ConfState'
            (raftState γ k RaftState.init) (fun _ => memStorMeta ms γs tcBootContents.hs)
            sl (DFrac.own 1) (tcPeers nv) (tcConfig_valid k ms «$v1_ptr» Hk.1 (by omega)) rfl rfl
            (by show sint.Z (W64 256) < 2 ^ 62; decide) rfl rfl rfl
            (Or.inr (by show ~~~W64 0 ≠ W64 0; decide)) rfl (fun h => absurd Hmd h)
            rfl rfl rfl rfl rfl rfl
            (tcPeers_ids nv).symm x)
          $$ [«$r0» Hau Hboot Hvac Hsl Hstc]
          as %nd ⟨%n, %K, %Hnd, -, #HisNode, Hdrv, Hncfg, Hrun, -, Hrs, Hmeta, Hsl, #Hsd⟩
        · iframe Hlog Hnb Hpctx «$r0» Hvac Hau Hsl Hstc
          iExactEq Hboot; rfl
        -- the replica's record, appended
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
          (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica.ty)))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := Loc)
          (t := go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica.ty)
          [«$sl0_ptr»]
        wp_auto
        rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression
          (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica.ty)
          #«$sl0_ptr»)] = 1 from rfl]
        isplitl []
        · ipureintro; rfl
        iintro %sl_ptr ⟨Htmp, -⟩
        -- the replica's fields
        icases typedPointsto_split _ _ _ $$ «$sl0» with Hrf
        simp only [TypedPointsto.typedPointstoDef]
        icases Hrf with ⟨Rid, Rnode, Rstor, Rappl, Rsi, Rcs, -⟩
        imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Rid with #Rid
        imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Rnode with #Rnode
        imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Rstor with #Rstor
        wp_auto
        wp_apply wp_slice_append (V := Loc)
            (t := go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica.ty)
            rsl _ _ [«$sl0_ptr»] (DFrac.own 1)
          $$ [Hrsl Hrcap Htmp] as %rsl' ⟨Hrsl', Hrcap', -⟩
        · iframe
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, rsl', ds ++ [(«$sl0_ptr», ms)], <[ms := γs.tuple]>M
        rw [Hk1]
        iframe i Freps Hreg Hsl Htodo
        isplitl [Hrsl']
        · iExactEq Hrsl'; simp
        isplitl [Hrcap']
        · iexact Hrcap'
        isplitl [Hdone Rappl Rsi Rcs Hdrv Hncfg Hrun Hrs Hmeta]
        · iapply (BigSepL.bigSepL_append (Φ := fun j (d : Loc × Loc) =>
            repStart (GF := GF) nv γ d.1 (W64 ((j : Nat) + 1)) d.2)).2
          iframe Hdone
          iapply (BigSepL.bigSepL_cons (Φ := fun j (d : Loc × Loc) =>
            repStart (GF := GF) nv γ d.1 (W64 ((j + ds.length : Nat) + 1)) d.2)).2
          isplitl
          · simp only [Nat.zero_add]
            rw [Hk.2.2.1, HkW]
            iunfold repStart
            iexists n, γs, K
            iframe Hrs Hrun Hsd Hmeta
            isplitr
            · iunfold repInfo
              subst Hnd
              iframe Rid Rnode Rstor HisNode Hrg Hlock
              ipureintro; exact Hsz
            isplitl [Rappl Rsi Rcs]
            · iunfold repOwn
              iexists _, _, _
              iframe Rappl Rsi Rcs
            isplitl [Hdrv]
            · iExactEq Hdrv; rfl
            iExactEq Hncfg; rfl
          iapply (BigSepL.bigSepL_nil).2; iempintro
        ipureintro
        refine ⟨Hs1, Hs4, by rw [List.length_append, Hk.2.2.1]; simpa using Hkk, ?_⟩
        intro l hl
        rw [List.map_append, List.mem_append]
        by_cases hlm : l = ms
        · subst hlm; right; simp
        · left; rw [GMap.lookup_insert_ne _ _ (Ne.symm hlm)] at hl; exact Hk.2.2.2 l hl
      · exfalso; apply Hif; rw [HN3, (tc_sZ nv H5').1]; exact Hk3
    · -- the replicas made: the world the goroutines share
      have Hk4 : sint.nat k - 1 = nv := tc_reps_end nv H5' k _ _ HN3 HX0 Hk.2.1 Hif
      have Hdl : ds.length = nv := by rw [Hk.2.2.1, Hk4]
      imod ownSlice_persist rsl _ _ $$ Hrsl with #Hrsl
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Freps with #Freps
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Fstop with #Fstop
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Frec with #Frec
      icases typedPointsto_split _ _ _ $$ Fcfg with Hcf2
      simp only [TypedPointsto.typedPointstoDef]
      icases Hcf2 with ⟨-, -, -, -, -, -, WTick, WMax, WDrop, WSnap, -, -, -⟩
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ WTick with #WTick
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ WMax with #WMax
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ WDrop with #WDrop
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ WSnap with #WSnap
      -- the network's join
      imod sync.init_WaitGroup (tcNetN.@"wg") _ $$ Fnet with ⟨%γwg, Hwg⟩
      imod nj_init tcNetN _ γwg ⊤ $$ Hwg with ⟨%γnj, Had⟩
      -- the `apps` join
      imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ Fapps with ⟨%γap, Hap⟩
      imod sync.join.init _ γap $$ Hap with Hadder
      -- the counters
      imod iso_alloc _ ⊤ $$ Fiso with #Hiso
      imod ctr_alloc _ ⊤ $$ FP with #HcP
      imod ctr_alloc _ ⊤ $$ FD with #HcD
      imod ctr_alloc _ ⊤ $$ FX with #HcX
      imod ctr_alloc _ ⊤ $$ FR with #HcR
      imod ctr_zero _ $$ FC with #HcC
      icases repStarts_nodes nv γ ds $$ Hdone with ⟨#Hnodes, Hdone⟩
      icases repStarts_dones nv γ ds $$ Hdone with ⟨#Hsds, Hdone⟩
      icases njAdder_isNetJoin tcNetN _ γnj 1 $$ Had with ⟨Had, #Hnj⟩
      have Hbl3 : boot.length = nv := by rw [Hbf.1]; exact tcVoters_length nv
      ihave #Hw : tcWorld cl ⟨γ, γd, cfg, sc, γsc, nv, ds.map Prod.fst, γnj, boot⟩ $$ []
      · unfold tcWorld
        iframe WTick WMax WDrop WSnap Fstop Hunk Hnodes Hiso HcP HcD HcX HcR HcC Hcl Hops Hpol Hsn
          Hboot
        isplitr
        · ipureintro
          refine ⟨⟨HN3, HX0, HC0, HS0, HM0, HM1, HT0, H1, H5⟩, HT0, Htr, Hsl0, Hbf, by simp [Hdl], ?_, Hmd⟩
          rw [Hbl, Hbl3]; omega
        isplitr
        · unfold replicasRO; iexists rsl; iframe Freps Hrsl
        iexact Hnj
      -- the `app`s, forked
      ihave %Hrlen := ownSlice_len $$ Hrsl
      simp only [List.length_map] at Hrlen
      ihave IHa : iprop(∃ (k : w64) (rv : Loc) (na : w32),
          "i" ∷ i_ptr ↦ k ∗ "r" ∷ r_ptr ↦ rv ∗
          "Hadder" ∷ sync.join.ownAdder (cl.[G.Cluster, go!"apps"]) na
            ([∗list] j ↦ d ∈ ds.take (sint.nat k),
              appDone cl ⟨γ, γd, cfg, sc, γsc, nv, ds.map Prod.fst, γnj, boot⟩ d.1
                (W64 ((j : Nat) + 1)) (tcQ nv j)) ∗
          "Hrest" ∷ ([∗list] j ↦ d ∈ ds.drop (sint.nat k),
            repStart nv γ d.1 (W64 ((sint.nat k + j : Nat) + 1)) d.2) ∗
          "Hqs" ∷ ([∗list] j ∈ List.range' (sint.nat k) (nv - sint.nat k),
            njAdder tcNetN (cl.[G.Cluster, go!"net"]) γnj (tcQ nv j)) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ nv ∧ sint.Z na = sint.Z k⌝)
        $$ [i r Hadder Hdone Had]
      · iexists W64 0, _, W32 0
        iframe i r
        simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero,
          Nat.zero_add]
        isplitl [Hadder]
        · iapply sync.join.ownAdder_wand $$ [] Hadder
          iintro -
          iapply (BigSepL.bigSepL_nil).2; iempintro
        iframe Hdone
        isplitl [Had]
        · simp only [Nat.sub_zero]
          iapply njAdder_split_one tcNetN _ γnj nv H1 $$ Had
        ipureintro
        have : sint.Z (W64 0) = 0 := by decide
        exact ⟨by omega, by omega, by decide⟩
      wp_for IHa
      wp_if_destruct
      · obtain ⟨Hlt, Hs0, Hs1, Hs3, HtoN, HW, Hna⟩ :=
          tc_apps_step nv H5' k rsl.len Hk.1 Hif (by rw [← Hrlen.1, Hdl])
        obtain ⟨d, Hd⟩ : ∃ d, ds[sint.nat k]? = some d :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have Hdl' : (ds.map Prod.fst)[sint.nat k]? = some d.1 := by
          rw [List.getElem?_map, Hd]; rfl
        simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rsl.len from ⟨Hk.1, Hif⟩,
          _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index rsl (sint.Z k) _ DFrac.discard d.1 Hk.1 $$ [] as -
        · iframe Hrsl; ipureintro; rw [HtoN]; exact Hdl'
        have Hdrop : ds.drop (sint.nat k) = d :: ds.drop (sint.nat k + 1) := by
          rw [List.drop_eq_getElem_cons (by omega)]
          rw [List.getElem?_eq_getElem (by omega)] at Hd
          rw [Option.some.inj Hd]
        rw [Hdrop]
        icases Hrest with ⟨Hd0, Hrest⟩
        simp only [Nat.add_zero]
        iunfold repStart at Hd0
        icases Hd0 with ⟨%n, %γs, %K, #Hri, Hown, Hmeta, Hdrv, Hrs, Hncfg, Hrun, #Hsd⟩
        have Hrng : List.range' (sint.nat k) (nv - sint.nat k) =
            sint.nat k :: List.range' (sint.nat k + 1) (nv - (sint.nat k + 1)) := by
          rw [show nv - sint.nat k = (nv - (sint.nat k + 1)) + 1 by omega, List.range'_succ]
        rw [Hrng]
        icases Hqs with ⟨Hq, Hqs⟩
        try wp_auto
        wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add
            (appDone cl ⟨γ, γd, cfg, sc, γsc, nv, ds.map Prod.fst, γnj, boot⟩ d.1 (W64 ((sint.nat k : Nat) + 1))
              (tcQ nv (sint.nat k))) _ _ na)
          $$ [Hadder] as ⟨Hadder, Happdone⟩
        · iframe Hadder
          ipureintro; rw [Hk.2.2]; exact Hna
        try wp_auto
        wp_apply wp_fork_tok_body $$ [Hown Hmeta Hdrv Hrs Hncfg Hrun Happdone Hq]
        · iintro Htt
          wp_apply (wp_app cl ⟨γ, γd, cfg, sc, γsc, nv, ds.map Prod.fst, γnj, boot⟩ d.1 n d.2 γs
              (W64 ((sint.nat k : Nat) + 1)) (NodeDriverState.init (memStorIface d.2) K) ⟨0, tcMem nv⟩
              _ (tcQ nv (sint.nat k)) rfl rfl ⟨rfl, Nat.zero_le _, fun _ _ _ h _ => absurd h (Nat.not_lt_zero _)⟩)
            $$ [Hown Hmeta Hdrv Hrs Hncfg Hrun Happdone Hq Htt] as Htt
          · iframe Hw Hri Hown Hmeta Hdrv Hncfg Hrun Happdone Hq Htt
            iExactEq Hrs; rfl
          iframe Htt
          ipureintro; simp
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, d.1, na + W32 1
        rw [Hs1]
        iframe
        isplitl [Hadder]
        · iapply sync.join.ownAdder_wand $$ [] Hadder
          iintro ⟨Hp, Hd1⟩
          rw [List.take_add_one, Hd, Option.toList_some]
          iapply (BigSepL.bigSepL_append).2
          iframe Hp
          iapply (BigSepL.bigSepL_cons).2
          isplitl [Hd1]
          · iExactEq Hd1
            simp only [List.length_take, Nat.min_eq_left (show sint.nat k ≤ ds.length by omega),
              Nat.zero_add]
          iapply (BigSepL.bigSepL_nil).2; iempintro
        isplitl [Hrest]
        · iapply (BigSepL.bigSepL_mono_of_forall ?_) $$ Hrest
          intro j x
          rw [show sint.nat k + (j + 1) = sint.nat k + 1 + j by omega]
        ipureintro
        exact ⟨Hs0, Hs3, tc_na_succ na k Hk.2.2 Hna Hk.1⟩
      · -- the `app`s all started
        have Hk3' : sint.nat k = nv := tc_apps_end nv k rsl.len Hk.2.1 Hif (by rw [← Hrlen.1, Hdl])
        rw [Hk3', List.take_of_length_le (by omega)]
        -- the drivers' join
        imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ c with #c
        try wp_auto
        imod sync.init_WaitGroup (tcDrvN.@"wg") _ $$ drivers with ⟨%γdw, #Hdwg, Hdwo, Hdww⟩
        wp_apply join3.wp_Add_of sync.WaitGroup.wp_Add tcDrvN _ γdw $$ [$Hsy $Hdwg $Hdwo $Hdww]
          as ⟨%γj3, Hd1, Hd2, Hd3, Hdw⟩
        try wp_auto
        -- the isolations
        wp_apply wp_fork $$ [Hd1]
        · try wp_auto
          wp_apply wp_with_defer as %defer defer
          try wp_auto
          ihave IHi : iprop(∃ kk : w64, "k" ∷ k_ptr ↦ kk) $$ [k]
          · iexists _; iexact k
          wp_for IHi
          wp_if_destruct
          · try wp_auto
            wp_apply time.wp_Sleep
            wp_apply wp_below rsl.len (by rw [tc_len nv H1 rsl.len _ Hrlen.1 Hdl]; omega) $$ [$Hpkg]
              as %b -
            try wp_auto
            wp_apply iso_wp_Store _ _ $$ [$Hiso]
            try wp_auto
            wp_apply time.wp_Sleep
            wp_apply iso_wp_Store _ _ $$ [$Hiso]
            try wp_auto
            wp_for_post
            iframe
            iexists _
            iframe
          · try wp_auto
            wp_apply join3.wp_Done_of sync.WaitGroup.wp_Done tcDrvN _ γj3 $$ [$Hsy $Hd1]
            try wp_auto
            ipureintro; simp
        try wp_auto
        -- the proposer
        wp_apply wp_fork $$ [Hd2]
        · try wp_auto
          wp_apply wp_with_defer as %defer defer
          try wp_auto
          ihave IHp : iprop(∃ kk : w64, "k" ∷ k_ptr ↦ kk) $$ [k]
          · iexists _; iexact k
          wp_for IHp
          wp_if_destruct
          · try wp_auto
            have Hl3 := tc_len nv H1 rsl.len _ Hrlen.1 Hdl
            wp_apply wp_below rsl.len (by rw [Hl3]; omega) $$ [$Hpkg] as %b %Hb
            obtain ⟨j, Hj3, HjZ, HjW⟩ := tc_pick nv b rsl.len Hb.1 (by rw [← Hl3]; exact Hb.2) Hl3
            obtain ⟨d, Hd⟩ : ∃ d, ds[j]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            have Hdl' : (ds.map Prod.fst)[j]? = some d.1 := by rw [List.getElem?_map, Hd]; rfl
            simp only [show 0 ≤ sint.Z b ∧ sint.Z b < sint.Z rsl.len from Hb, _root_.and_self,
              ↓reduceIte]
            wp_apply wp_load_slice_index rsl (sint.Z b) _ DFrac.discard d.1 Hb.1 $$ [] as -
            · iframe Hrsl; ipureintro; rw [HjZ]; exact Hdl'
            ihave #Hrn := BigSepL.bigSepL_lookup (Φ := fun i r => repNode (GF := GF) γ r (W64 ((i : Nat) + 1)))
              Hdl' $$ Hnodes
            iunfold repNode at Hrn
            icases Hrn with ⟨%nd, #Hnf, #Hnd⟩
            ihave #Hcx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
            · iPkgInit
            ihave #Hsc' : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
            · iPkgInit
            try wp_auto
            wp_apply context.wp_Background
            wp_apply wp_WT _ $$ [$Hcx $Hcc] as %ctx %cd %cancel ⟨#Hcancel, #Hctx, -⟩
            try wp_auto
            wp_apply wp_Itoa kk $$ [$Hsc'] as %str %Hstr
            try wp_auto
            wp_apply wp_string_to_bytes as %bsl ⟨Hbs, -⟩
            imod ownSlice_persist bsl _ _ $$ Hbs with #Hbs
            try wp_auto
            ihave Hau := tc_propAu γ boot ([118#8] ++ str) $$ Hops
            wp_apply wp_Propose nd γ tcRaftN (W64 ((j : Nat) + 1)) bsl ([118#8] ++ str) ctx cd
              $$ [Hau] as %err -
            · iframe Hnd Hbs
              isplitr
              · iunfold nodeCtx; iright; iexact Hctx
              isplitr
              · ipureintro; intro b h; simp [Hmd] at h
              rw [Hdup]
              iexact Hau
            try wp_auto
            wp_apply Hcancel
            try wp_auto
            wp_apply ctr_wp_Add _ _ $$ [$HcP] as %_ -
            try wp_auto
            wp_apply time.wp_Sleep
            try wp_auto
            wp_for_post
            iframe
            iexists _
            iframe
          · try wp_auto
            wp_apply join3.wp_Done_of sync.WaitGroup.wp_Done tcDrvN _ γj3 $$ [$Hsy $Hd2]
            try wp_auto
            ipureintro; simp
        try wp_auto
        -- the proposer of configuration changes: `ConfChanges = 0`, so its loop never runs
        wp_apply wp_fork $$ [Hd3]
        · try wp_auto
          wp_apply wp_with_defer as %defer defer
          try wp_auto
          wp_apply time.wp_Now as %tnow -
          try wp_auto
          wp_apply time.Time.wp_Add as %tdl -
          try wp_auto
          ihave IHc : iprop(True) $$ []
          · itrivial
          wp_for IHc
          wp_apply ctr_zero_wp_Load _ $$ [$HcC]
          try wp_auto
          rw [HC0]
          try wp_auto
          rw [ite_eq_right (by simp only [decide_eq_true_eq]; intro h; cases go.intoVal_inj (V := Bool) h)]
          try wp_auto
          rw [ite_eq_left (by simp)]
          try wp_auto
          wp_apply join3.wp_Done_of sync.WaitGroup.wp_Done tcDrvN _ γj3 $$ [$Hsy $Hd3]
          try wp_auto
          ipureintro; simp
        try wp_auto
        -- the drivers done; the stop
        wp_apply join3.wp_Wait_of sync.WaitGroup.wp_Wait tcDrvN _ γj3 $$ [$Hsy $Hdw]
        try wp_auto
        wp_apply time.wp_Sleep
        try wp_auto
        wp_apply wp_broadcast_chan_close sc γsc iprop(True) $$ [$Hpend] as -
        · iintro !>; itrivial
        try wp_auto
        -- the `app`s done
        wp_apply (lc := 1) (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ _ _)
          $$ [$Hsy $Hadder] as ⟨Hdones, -⟩
        imod lc_fupd_elim_later $$ Hlc1 Hdones with Hdones
        try wp_auto
        -- the nodes stopped
        ihave IHs : iprop(∃ (k : w64) (rv : Loc),
            "i" ∷ i_ptr ↦ k ∗ "r" ∷ r_ptr ↦ rv ∗
            "Hds" ∷ ([∗list] j ↦ d ∈ ds.drop (sint.nat k),
              appDone cl ⟨γ, γd, cfg, sc, γsc, nv, ds.map Prod.fst, γnj, boot⟩ d.1
                (W64 ((sint.nat k + j : Nat) + 1)) (tcQ nv (sint.nat k + j))) ∗
            "Hqs" ∷ ([∗list] j ∈ List.range (sint.nat k),
              njAdder tcNetN (cl.[G.Cluster, go!"net"]) γnj (tcQ nv j)) ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ nv⌝)
          $$ [i r Hdones]
        · iexists W64 0, _
          iframe i r
          simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, Nat.zero_add,
            List.range_zero]
          isplitl [Hdones]
          · iexact Hdones
          isplitl []
          · iapply (BigSepL.bigSepL_nil).2; iempintro
          ipureintro
          have : sint.Z (W64 0) = 0 := by decide
          exact ⟨by omega, by omega⟩
        wp_for IHs
        wp_if_destruct
        · obtain ⟨Hlt, Hs0, Hs1, Hs3, HtoN, HW, -⟩ :=
            tc_apps_step nv H5' k rsl.len Hk.1 Hif (by rw [← Hrlen.1, Hdl])
          obtain ⟨d, Hd⟩ : ∃ d, ds[sint.nat k]? = some d :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have Hdl' : (ds.map Prod.fst)[sint.nat k]? = some d.1 := by
            rw [List.getElem?_map, Hd]; rfl
          simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rsl.len from ⟨Hk.1, Hif⟩,
            _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index rsl (sint.Z k) _ DFrac.discard d.1 Hk.1 $$ [] as -
          · iframe Hrsl; ipureintro; rw [HtoN]; exact Hdl'
          have Hdrop : ds.drop (sint.nat k) = d :: ds.drop (sint.nat k + 1) := by
            rw [List.drop_eq_getElem_cons (by omega)]
            rw [List.getElem?_eq_getElem (by omega)] at Hd
            rw [Option.some.inj Hd]
          rw [Hdrop]
          icases Hds with ⟨Hd0, Hds⟩
          simp only [Nat.add_zero]
          iunfold appDone at Hd0
          icases Hd0 with ⟨%n, #Hnf, #Hnd, Hrun, Hq⟩
          try wp_auto
          wp_apply wp_Stop n γ tcRaftN (W64 ((sint.nat k : Nat) + 1)) $$ [$Hnd $Hrun] as -
          try wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, d.1
          rw [Hs1]
          iframe
          isplitl [Hds]
          · iapply (BigSepL.bigSepL_mono_of_forall ?_) $$ Hds
            intro j x
            rw [show sint.nat k + (j + 1) = sint.nat k + 1 + j by omega]
          isplitl [Hqs Hq]
          · rw [List.range_succ]
            iapply (BigSepL.bigSepL_append).2
            iframe Hqs
            iapply (BigSepL.bigSepL_cons).2
            iframe Hq
            iapply (BigSepL.bigSepL_nil).2; iempintro
          ipureintro; exact ⟨Hs0, Hs3⟩
        · -- the network's goroutines done
          have Hk3'' : sint.nat k = nv := tc_apps_end nv k rsl.len Hk.2 Hif (by rw [← Hrlen.1, Hdl])
          rw [Hk3'']
          ihave Had := njAdder_join_one tcNetN _ γnj nv H1 $$ Hqs
          imod njClose tcNetN _ γnj $$ Had with ⟨Hw0, #Hnj'⟩
          try wp_auto
          wp_apply netJoin.wp_Wait_of sync.WaitGroup.wp_Wait tcNetN _ γnj $$ [$Hsy $Hw0 $Hnj']
          try wp_auto
          iapply HΦ
          -- the run is over
          ihave #Hrec' : isSyncRecorder tn.tr «$v1_ptr» $$ []
          · rw [Htn]; iexact Hrec
          iapply probeA_end nv H1 H5 cl «$v1_ptr» γ tcRaftN γd tn (W64 1) Htr $$ Frec Hrec' Hnb1 Hdir Hsim
          iintro !>
          iapply tc_startDones γ ds nv Hdl
          iintro !>
          iexact Hsds

end proof

end TraceCheck
end EtcdGrove
end Perennial
