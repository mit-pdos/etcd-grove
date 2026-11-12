/-
Lean-first (no Rocq counterpart). Trace-check's layer D (the harness, 2026-11-12;
`notes/trace-check-design.md` §2; `notes/decisions.md`, "The harness (RunConcurrent)"): **what the
harness's goroutines share**, and **the node-API statements the harness takes as hypotheses**.

* `HarnessApi` (at a storage model): the traced node-API statement the harness's proof takes as a
  hypothesis, `StartNode.tracedSpec` (`TracedNodeApi.lean`; proved since trace-check step 5: raft's
  linked `wp_StartNode_traced`, through `StartNode.tracedSpec_of_gated`; `Results.lean`'s
  `harnessOpen`). The other traced statements it uses are raft's, proved
  since implementation step 1 (2026-11-12): `stepIn_intro` with the token and the law `trTok_type`
  (`TracedNodeApi.lean`), `isReadyChan_recvAu.tracedSpec_proof` and the linked
  `node.Advance.tracedSpec` (`TracedLinked.lean`). The law `Membership.applyChange_leaveJoint` is not
  used: the harness's view of the configuration is always the voters' simple membership, so a
  committed empty `ConfChangeV2` (at a joint configuration, `committed_emptyV2_joint`) is refuted
  instead of applied (`notes/decisions.md`, "The harness (RunConcurrent)").
* `tcWorld c W` (persistent): the cluster's fields as the goroutines read them, the stop channel, the
  replicas and their nodes, the network's join, the counters' invariants, and the traced cluster
  with the harness's invariants (`tcOpsInv`, `confPolicy`, `tcSnapsInv`, from `ProbeA.lean`).
* `repInfo`/`repOwn`: a replica's read-only fields and node, and the fields its `app` writes.
* `ViewOk`: the `app`'s view of its node's configuration: the voters' simple membership, applied up
  to a point of the delivered log past which no conf entry is delivered yet.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.HarnessStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.NetJoin
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.ProbeA
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__replica
public import Spec.go_etcd_io.raft.v3.StartNode
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim ProbeA

/-! ## Names -/

/-- Raft's namespace in the harness's cluster. -/
def tcRaftN : Namespace := nroot.@"tc_raft"
/-- The network's join. -/
def tcNetN : Namespace := nroot.@"tc_net"
/-- The atomic counters' invariants. -/
def tcCtrN : Namespace := nroot.@"tc_ctr"

/-- The harness's shared names and values. -/
structure TcW [GooseExts] where
  /-- the traced cluster -/
  cl : Cluster
  /-- its trace mode's directory -/
  γd : GName
  /-- the run's configuration -/
  cfg : G.CConfig
  /-- the stop channel -/
  sc : GoChan
  γsc : ChanNames
  /-- the replicas, of ids `1, 2, 3` -/
  rs : List Loc
  /-- the network's join -/
  nj : NetJoinNames
  /-- the bootstrap log -/
  boot : List LogEntry

/-- The voters. -/
abbrev tcVs : List w64 := tcVoters
/-- Their simple membership. -/
abbrev tcMem : Membership := Membership.simple (GMap.listToSet tcVoters)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- The `raft.Node` interface value of the node `n`. -/
abbrev nodeIface (n : Loc) : go_etcd_io.raft.v3.Node :=
  interface.mkOk (go.GoType.PointerType node.ty) #n

/-- An `atomic.Int64` counter the harness only adds to. -/
def ctrInv (l : Loc) : IProp GF := inv tcCtrN (∃ v : w64, sync.atomic.ownInt64 l (DFrac.own 1) v)

instance ctrInv_persistent (l : Loc) : Persistent (ctrInv (GF := GF) l) := by
  unfold ctrInv; infer_instance

/-- The isolated replica (`atomic.Uint64`), stored and loaded. -/
def isoInv (l : Loc) : IProp GF := inv tcCtrN (∃ v : w64, sync.atomic.ownUint64 l (DFrac.own 1) v)

instance isoInv_persistent (l : Loc) : Persistent (isoInv (GF := GF) l) := by
  unfold isoInv; infer_instance

instance ownInt64_discard_persistent (l : Loc) (v : w64) :
    Persistent (sync.atomic.ownInt64 (GF := GF) l DFrac.discard v) :=
  (sync.atomic.ownInt64_dfractional (GF := GF) l v).dfractional_persistent

/-- **A replica's node** (persistent): its `node` field, the node `n` of id `id`. -/
def repNode (γ : Cluster) (r : Loc) (id : w64) : IProp GF :=
  iprop(∃ n : Loc, r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"node"]
      ↦□ nodeIface n ∗ isNode n γ tcRaftN id)

instance repNode_persistent (γ : Cluster) (r : Loc) (id : w64) :
    Persistent (repNode (GF := GF) γ r id) := by
  unfold repNode; infer_instance

/-- **A replica's read-only part** (persistent): its id, node `n` and storage `ms` (registered, of
names `γs`). -/
def repInfo [MemStorReg GF] (γ : Cluster) (r : Loc) (id : w64) (n ms : Loc) (γs : MemStorNames) :
    IProp GF :=
  iprop(r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"id"] ↦□ id ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"node"] ↦□ nodeIface n ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"storage"] ↦□ ms ∗
    isNode n γ tcRaftN id ∗ memStorReg ms γs ∗ memStorLock ms γs)

instance repInfo_persistent [MemStorReg GF] (γ : Cluster) (r : Loc) (id : w64) (n ms : Loc)
    (γs : MemStorNames) : Persistent (repInfo (GF := GF) γ r id n ms γs) := by
  unfold repInfo; infer_instance

/-- **The fields a replica's `app` writes.** -/
def repOwn (r : Loc) : IProp GF :=
  iprop(∃ (a si : w64) (cs : Loc),
    r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"applied"] ↦ a ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"snapIndex"] ↦ si ∗
    r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"confState"] ↦ cs)

/-- **The harness's world** (persistent; see the file header). -/
def tcWorld (c : Loc) (W : TcW) : IProp GF :=
  iprop(c.[G.Cluster, go!"cfg"].[G.CConfig, go!"Tick"] ↦□ W.cfg.Tick' ∗
    c.[G.Cluster, go!"cfg"].[G.CConfig, go!"MaxDelay"] ↦□ W.cfg.MaxDelay' ∗
    c.[G.Cluster, go!"cfg"].[G.CConfig, go!"DropPct"] ↦□ W.cfg.DropPct' ∗
    c.[G.Cluster, go!"cfg"].[G.CConfig, go!"SnapshotEvery"] ↦□ W.cfg.SnapshotEvery' ∗
    ⌜Workload W.cfg ∧ 0 < sint.Z W.cfg.Tick' ∧ Cluster.trace W.cl = some W.γd ∧
      W.cl.snapLoc = (fun _ => none) ∧ BootLogFacts W.boot ∧ W.rs.length = 3 ∧
      receiptBound GF + W.cl.bootLen ≤ 2 ^ 61⌝ ∗
    c.[G.Cluster, go!"stop"] ↦□ W.sc ∗ ownBroadcastChan W.sc W.γsc iprop(True) .Unknown ∗
    replicasRO c W.rs ∗
    ([∗list] i ↦ r ∈ W.rs, repNode W.cl r (W64 (i + 1))) ∗
    isNetJoin tcNetN (c.[G.Cluster, go!"net"]) W.nj ∗
    isoInv (c.[G.Cluster, go!"isolated"]) ∗
    ctrInv (c.[G.Cluster, go!"Proposed"]) ∗ ctrInv (c.[G.Cluster, go!"Delivered"]) ∗
    ctrInv (c.[G.Cluster, go!"Dropped"]) ∗ ctrInv (c.[G.Cluster, go!"Readies"]) ∗
    sync.atomic.ownInt64 (c.[G.Cluster, go!"ConfChanges"]) DFrac.discard (W64 0) ∗
    isCluster W.cl tcRaftN ∗ tcOpsInv W.cl W.boot ∗ confPolicy W.cl tcConfN tcRule ∗
    tcSnapsInv W.cl ∗ isCommittedLogLb W.cl W.boot)

instance tcWorld_persistent (c : Loc) (W : TcW) : Persistent (tcWorld (GF := GF) c W) := by
  unfold tcWorld; infer_instance

end defs

/-- **The `app`'s view of its node's configuration** at the delivered log `D` (see the file header). -/
def ViewOk [GooseExts] (D : List LogEntry) (v : ConfigView) : Prop :=
  v.membership = tcMem ∧ v.applied ≤ D.length ∧ NoConfChangeIn D v.applied D.length

/-! ## The proposer's update -/

section propose
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem tcOpsN_raftN : (↑tcOpsN : CoPset) ⊆ ⊤ \ ↑tcRaftN :=
  mask_ndot_ne' nroot "tc_ops" "tc_raft" (by decide)

/-- **A proposal's update** (§2.2, `node.Propose.spec`'s, at `γ.dup = false`), from `tcOpsInv`: the
committed requested entries grow by a normal entry, which keeps the invariant's clause (past the
bootstrap log, only normal entries). -/
theorem tc_propAu (γ : Cluster) (boot : List LogEntry) (d : List w8) :
    ⊢ tcOpsInv (GF := GF) γ boot -∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑tcRaftN, ∅
        <{ ∀∀ (t : w64), ownCommittedOps γ (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]), COMM True }> := by
  iintro #Hinv
  iauintro
  unfold atomic_acc tcOpsInv
  have Hdisj := tcOpsN_raftN
  iinv Hinv with Hb Hclose
  iunfold tcOpsBody at Hb
  icases Hb with ⟨%ops, >Hops, >%Hok⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑tcRaftN) \ ↑tcOpsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops] with -
    · inext; unfold tcOpsBody; iexists ops; iframe Hops; ipureintro; exact Hok
    imodintro
    iempintro
  · iintro %t Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops] with -
    · inext
      unfold tcOpsBody
      iexists ops ++ [⟨t, W32 0, d⟩]
      iframe Hops
      ipureintro
      obtain ⟨Hpre, Hall⟩ := Hok
      refine ⟨Hpre.trans (List.prefix_append _ _), fun op hop => ?_⟩
      have hle : boot.length ≤ ops.length := Hpre.length_le
      rw [List.drop_append_of_le_length hle] at hop
      rcases List.mem_append.1 hop with h | h
      · exact Hall op h
      · simp only [List.mem_singleton] at h; subst h; rfl
    imodintro
    itrivial

end propose

/-! ## The counters -/

section counters
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- A zero counter, in its invariant. -/
theorem ctr_alloc (l : Loc) (E : CoPset) :
    ⊢ (l ↦ (zero_val sync.atomic.Int64) : IProp GF) ={E}=∗ ctrInv l := by
  have hz : (l ↦ (zero_val sync.atomic.Int64) : IProp GF) ⊢
      sync.atomic.ownInt64 l (DFrac.own 1) (W64 0) := by
    rw [sync.atomic.ownInt64_unseal]; unfold sync.atomic.ownInt64Def; exact .rfl
  iintro H
  unfold ctrInv
  iapply inv_alloc
  inext
  iexists W64 0
  iapply hz $$ H

/-- The isolated replica, in its invariant. -/
theorem iso_alloc (l : Loc) (E : CoPset) :
    ⊢ (l ↦ (zero_val sync.atomic.Uint64) : IProp GF) ={E}=∗ isoInv l := by
  have hz : (l ↦ (zero_val sync.atomic.Uint64) : IProp GF) ⊢
      sync.atomic.ownUint64 l (DFrac.own 1) (W64 0) := by
    rw [sync.atomic.ownUint64_unseal]; unfold sync.atomic.ownUint64Def; exact .rfl
  iintro H
  unfold isoInv
  iapply inv_alloc
  inext
  iexists W64 0
  iapply hz $$ H

/-- A counter never written: zero for good. -/
theorem ctr_zero (l : Loc) :
    ⊢ (l ↦ (zero_val sync.atomic.Int64) : IProp GF) ==∗
      sync.atomic.ownInt64 l DFrac.discard (W64 0) := by
  have hz : (l ↦ (zero_val sync.atomic.Int64) : IProp GF) ⊢
      sync.atomic.ownInt64 l (DFrac.own 1) (W64 0) := by
    rw [sync.atomic.ownInt64_unseal]; unfold sync.atomic.ownInt64Def; exact .rfl
  iintro H
  ihave H := hz $$ H
  iapply (sync.atomic.ownInt64_dfractional (GF := GF) l (W64 0)).dfractional_persist $$ H

/-- A counter's `Add`. -/
theorem ctr_wp_Add (l : Loc) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ ctrInv l }}
      (App (Val (l @!! go.GoType.PointerType sync.atomic.Int64.ty @!! go!"Add")) (Val #d))
    {{ (v : w64), RET #v; True }} := by
  iintro %Φ ⟨#Hat, #Hc⟩ HΦ
  iapply sync.atomic.Int64.wp_Add l d $$ Hat
  iunfold ctrInv at Hc
  iinv Hc with ⟨%v, >Hv⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑tcCtrN from Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  iapply HΦ
  itrivial

/-- A counter never written reads zero. -/
theorem ctr_zero_wp_Load (l : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
        sync.atomic.ownInt64 l DFrac.discard (W64 0) }}
      (App (Val (l @!! go.GoType.PointerType sync.atomic.Int64.ty @!! go!"Load")) (Val #()))
    {{ RET #(W64 0); True }} := by
  iintro %Φ ⟨#Hat, #Hc⟩ HΦ
  iapply sync.atomic.Int64.wp_Load l DFrac.discard $$ Hat
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists W64 0
  iframe Hc
  iintro -
  imod Hmask with -
  imodintro
  iapply HΦ
  itrivial

/-- The isolated replica's `Load`. -/
theorem iso_wp_Load (l : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ isoInv l }}
      (App (Val (l @!! go.GoType.PointerType sync.atomic.Uint64.ty @!! go!"Load")) (Val #()))
    {{ (v : w64), RET #v; True }} := by
  iintro %Φ ⟨#Hat, #Hc⟩ HΦ
  iapply sync.atomic.Uint64.wp_Load l (DFrac.own 1) $$ Hat
  iunfold isoInv at Hc
  iinv Hc with ⟨%v, >Hv⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑tcCtrN from Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  iapply HΦ
  itrivial

/-- The isolated replica's `Store`. -/
theorem iso_wp_Store (l : Loc) (w : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ isoInv l }}
      (App (Val (l @!! go.GoType.PointerType sync.atomic.Uint64.ty @!! go!"Store")) (Val #w))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hat, #Hc⟩ HΦ
  iapply sync.atomic.Uint64.wp_Store l w $$ Hat
  iunfold isoInv at Hc
  iinv Hc with ⟨%v, >Hv⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑tcCtrN from Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  iapply HΦ
  itrivial

end counters

/-! ## The node-API statements the harness takes as hypotheses -/

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The traced node-API statement the harness's proof takes** (see the file header). -/
abbrev HarnessApi : Prop :=
  StartNode.tracedSpec (GF := GF)

end api

end TraceCheck
end EtcdGrove
end Perennial
