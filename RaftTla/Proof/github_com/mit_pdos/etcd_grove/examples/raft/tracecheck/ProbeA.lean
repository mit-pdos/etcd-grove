/-
Lean-first (no Rocq counterpart). Trace-check's **Probe A** (`notes/trace-check-design.md` §8, revision 3;
`notes/spec-first-plan.md`, "Probe"; `notes/decisions.md`, "Probe A (harness glue)"): the harness-level
composition along the concrete path (`StartNode`, `Ready`, `handleReady`, `Advance`, then `send` →
`Step`), over the client statements, each post checked to supply the next pre.

A probe, not a result: nothing links it (no `Link`/`Results` imports it) and nothing here is used by a
proof. (2026-11-12, trace-check implementation step 1: the statements step 1 made real are used as they
now are: `readyToksClaim` and `readyToksClaim_nil`, `readyGotT` with the claim
(`isReadyChan_recvAu.tracedSpec`, proved: `isReadyChan_recvAu.tracedSpec_proof`), the linked
`node.Advance.tracedSpec` (`RaftLink.node.wp_Advance_traced`) and its instance `node.Advance.spec_of_traced`,
`stepIn_intro` with `trTok`, `trTok_type`, and the law `Membership.applyChange_leaveJoint`, which takes
`Restorable` (`confAt_restorable`) beside the design's premises.) The statements the design specifies
that do not exist in Lean yet are **hypotheses** here, each a `Prop` (or a parameter standing for a
sealed predicate the design adds), never an axiom or a `sorry`:

- `netJoin` (§6, Q34): parameters `njAdder`, `njDone` (sealed in the design's `NetJoin.lean`) and
  the `Add`/`Done` calls' expressions, with `NetJoinAdd`/`NetJoinDone` the two triples;
- the harness's own invariants (§2.2: `tcOpsInv`, `tcSnapsInv`, the rule `tcRule`) are **defined**
  here as the design writes them (they are the harness's, not raft's), and allocated (`probeA_alloc`).

Existing statements are used as they are: `harness_alloc`, `startTraceC_intro`, `StartNode.tracedSpec`'s
precondition, `runOver_intro`, `confPolicy_alloc`/`_decide`, `committed_emptyV2_joint`, `confAt_valid`,
`snapshotCert_made`, `snapMade_elem`, `ownCommittedOps_lb_prefix`, `readyMsgs_sent`, `msgOwn_persist`,
`sentMsg_shape`, `snapLocalMsg_noDir`, `proto.ClonePb.spec` at `pbMessage`, `node.Step.spec`,
`node.Advance.spec`, `wp_fork_tok_body`/`_self`.

**The probe's result** (the design's "Probe A (2026-11-11)" section, P1-P5): P1, the hypothesis
`LeaveJoint` (the empty `ConfChangeV2` applies at a valid joint membership: raft exports no law on joint
memberships, so A6's `ConfChangeV2` arm cannot meet `node.ApplyConfChange.spec`'s and
`confPolicy_decide`'s premise without it); P2, the claim's scope in `readyGotT` (inside its existentials,
at `readyRest`'s `ms`: `readyGotC`); P3, `tcOpsInv`'s parameter `boot`; P4, the conf arms need only
`tcOps_emptyV2`/`tcOps_v1_boot`, not `ConfShaped`; P5, the clone's glue (`clone_st`). The rest composes
as the design says.

The Goose code of `app`/`send`/`handleReady` is not modelled: the probe composes the specs, with the
goroutine's body, `send`'s `defer` and `handleReady`'s storage calls abstract (`probeA_round`'s
`Hwork`, `probeA_appToken`'s `hG`).
-/
module

public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.HarnessAlloc
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.HarnessEnd
public import RaftTla.Proof.go_etcd_io.raft.v3.ConfPolicy
public import RaftTla.Proof.go_etcd_io.raft.v3.InvPbMsg
public import RaftTla.Proof.go_etcd_io.raft.v3.PbMessage
public import RaftTla.Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PerTypeMessage
public import RaftTla.Spec.google_golang_org.protobuf.proto.ClonePb
public import RaftTla.Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2Empty
public import RaftTla.Spec.go_etcd_io.raft.v3.node__Advance
public import RaftTla.Spec.go_etcd_io.raft.v3.node__Step
public import RaftTla.Proof.go_etcd_io.raft.v3.TracedNodeApi
public import RaftTla.Proof.go_etcd_io.raft.v3.ConfchangeApi
public import RaftTla.Proof.go_etcd_io.raft.v3.InvTraceLogger
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Defs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck
namespace ProbeA

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

/-! ## The harness's vocabulary (§1.1, §2.2), as the design writes it -/

section defs
variable [GooseExts]

/-- The `n` voters (`concurrent.go`: `Peer{ID: i}` for `i = 1 … n`; 2026-11-24: `n` is `Main`'s draw,
until then `3`). -/
abbrev tcVoters (n : Nat) : List w64 := tracecheck.bootVoters n
/-- Their bootstrap contexts (nil). -/
abbrev tcCtxs (n : Nat) : List (List w8) := List.replicate n []

/-- `tracecheck.BootLogFacts` (§1.1). -/
abbrev BootLogFacts (n : Nat) (boot : List LogEntry) : Prop := tracecheck.BootLogFacts n boot

theorem tcVoters_length (n : Nat) : (tcVoters n).length = n := by
  simp [tcVoters, tracecheck.bootVoters]

theorem w32_2_ne_0 : W32 2 ≠ W32 0 := by decide
theorem w32_2_ne_1 : W32 2 ≠ W32 1 := by decide
theorem w32_1_ne_0 : W32 1 ≠ W32 0 := by decide

/-- The harness's namespaces (§2.2: outside raft's `N`). -/
def tcOpsN : Namespace := nroot.@"tc_ops"
def tcConfN : Namespace := nroot.@"tc_conf"
def tcSnapsN : Namespace := nroot.@"tc_snaps"

/-- The harness's conf rule (§2.2: kv's `kvRule`): apply what the entry decodes to. -/
def tcRule : ConfRule := fun _ _ e => ccDecode e

end defs

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `tcOpsInv`'s body (§2.2, revision 2's A6 clause): the committed operations, past the bootstrap log
the proposer's normal ones. **Probe finding (P3):** the clause names `boot`, so the invariant takes it
(the design writes `tcOpsInv γ`). -/
def tcOpsBody (γ : Cluster) (boot : List LogEntry) : IProp GF :=
  iprop(∃ ops : List LogEntry, ownCommittedOps γ ops ∗
    ⌜boot <+: ops ∧ ∀ op ∈ ops.drop boot.length, op.type = W32 0⌝)

instance tcOpsBody_timeless (γ : Cluster) (boot : List LogEntry) :
    Timeless (tcOpsBody (GF := GF) γ boot) := by unfold tcOpsBody; infer_instance

def tcOpsInv (γ : Cluster) (boot : List LogEntry) : IProp GF := inv tcOpsN (tcOpsBody γ boot)

/-- `tcSnapsInv` (§2.2): no snapshot is ever made. -/
def tcSnapsInv (γ : Cluster) : IProp GF := inv tcSnapsN (ownSnapsMade γ [])

instance tcOpsInv_persistent (γ : Cluster) (boot : List LogEntry) :
    Persistent (tcOpsInv (GF := GF) γ boot) := by unfold tcOpsInv; infer_instance
instance tcSnapsInv_persistent (γ : Cluster) : Persistent (tcSnapsInv (GF := GF) γ) := by
  unfold tcSnapsInv; infer_instance

/-! ## 1. Allocation (§2.2's first rows): `harness_alloc`, then the harness's invariants -/

theorem tcVoters_facts (n : Nat) (h1 : 1 ≤ n) (h5 : n ≤ tracecheck.maxNodes) :
    tcVoters n ≠ [] ∧ (tcVoters n).Nodup ∧ W64 0 ∉ tcVoters n ∧ ((tcVoters n).length : Int) < 2 ^ 62 ∧
      (tcVoters n).length < 2 ^ 40 := by
  have hl := tcVoters_length n
  unfold tracecheck.maxNodes at h5
  refine ⟨?_, ?_, ?_, by rw [hl]; omega, by rw [hl]; omega⟩
  · intro h; rw [h] at hl; simp at hl; omega
  · rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with rfl | rfl | rfl | rfl | rfl <;>
      decide
  · rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with rfl | rfl | rfl | rfl | rfl <;>
      decide

/-- **The harness's allocation, with its invariants** (§2.2): `harness_alloc` at the three voters,
then `tcOpsInv` from `ownCommittedOps γ boot`, `confPolicy` from `ownConfDecisions γ ∅`
(`confPolicy_alloc`), `tcSnapsInv` from `ownSnapsMade γ []`. Each comes out of `harness_alloc`'s post
as the design says. -/
theorem probeA_alloc (N : Namespace) (n : Nat) (h1 : 1 ≤ n) (h5 : n ≤ tracecheck.maxNodes)
    (boot : List LogEntry) (γt : GName) (E : CoPset)
    (hE : ↑N ⊆ E) (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (HB : BootLogFacts n boot) :
    ⊢ bootMarshal (GF := GF) (tcVoters n) (tcCtxs n) (LogEntry.toEntries boot 0) -∗ traceFrag γt [] ={E}=∗
      ∃ (γ : Cluster) (γd : GName) (tn : TraceNames),
        ⌜Cluster.trace γ = some γd ∧ tn.tr = γt ∧ tn.voters = tcVoters n ∧
          γ.snapLoc = (fun _ => none) ∧ γ.dup = false ∧ γ.bootLen = boot.length ∧
          γ.maxData = none⌝ ∗
        traceDir γd tn ∗ Cluster.traceSim γ (tcVoters n) tn ∗ isCluster γ N ∗
        tcOpsInv γ boot ∗ confPolicy γ tcConfN tcRule ∗ tcSnapsInv γ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet (tcVoters n))) ∗ isCommittedLogLb γ boot ∗
        [∗list] i ∈ tcVoters n, voterStart γ N (tcVoters n) (tcCtxs n) tn i := by
  obtain ⟨Hne, Hnd, Hnz, Hlen, -⟩ := tcVoters_facts n h1 h5
  iintro #Hm Hfr
  imod harness_alloc (GF := GF) N (tcVoters n) (tcCtxs n) boot γt E hE Hrb Hne Hnd Hnz Hlen HB $$ Hm Hfr
    with ⟨%γ, %γd, %tn, %Hγ, #Hd, #Hinv, Hops, -, #Hcl, Hdec, #Hca, Hsm, #Hlb, Hvs⟩
  obtain ⟨Htr, Htn, Hvs', Hdup, Hsl, Hbl, Hmd⟩ := Hγ
  imod inv_alloc tcOpsN E (tcOpsBody (GF := GF) γ boot) $$ [Hops] with #Hops
  · inext
    unfold tcOpsBody
    iexists boot
    iframe Hops
    ipureintro
    refine ⟨List.prefix_refl boot, fun op hop => ?_⟩
    simp at hop
  imod confPolicy_alloc (GF := GF) γ tcConfN tcRule E $$ Hdec with #Hpol
  imod inv_alloc tcSnapsN E (ownSnapsMade (GF := GF) γ []) $$ [Hsm] with #Hsn
  · inext; iexact Hsm
  imodintro
  iexists γ, γd, tn
  isplitr
  · ipureintro; exact ⟨Htr, Htn, Hvs', Hsl, Hdup, Hbl, Hmd⟩
  unfold tcOpsInv tcSnapsInv
  iframe Hd Hinv Hcl Hops Hpol Hsn Hca Hlb Hvs

/-- **A voter's `StartNode` precondition from its part** (`voterStart`, `startTraceC_intro`): the
`nodeBoot`, durable state and vacant slot `StartNode.tracedSpec` takes, and its `startTraceC γ vs cv`
for a configuration of the voter's id logging to the names' trace. -/
theorem probeA_startPre (n : Nat) (h5 : n ≤ tracecheck.maxNodes) (γ : Cluster) (N : Namespace) (γd : GName) (tn : TraceNames) (cv : Config)
    (Htr : Cluster.trace γ = some γd) (Hvs : tn.voters = tcVoters n) (Hpv : cv.PreVote' = false)
    (Hcq : cv.CheckQuorum' = false) (Hnil : cv.TraceLogger' ≠ interface.nil)
    (Hfit : receiptBound GF + max γ.bootLen 2 ≤ 2 ^ 61) :
    ⊢ voterStart (GF := GF) γ N (tcVoters n) (tcCtxs n) tn cv.ID' -∗ traceDir γd tn -∗
      Cluster.traceSim γ (tcVoters n) tn -∗ isTraceLogger tn.tr cv.TraceLogger' -∗
      nodeBoot γ N (tcVoters n) (tcCtxs n) cv.ID' ∗ nodeVacant γ cv.ID' ∗ raftState γ cv.ID' RaftState.init ∗
        startTraceC γ N (tcVoters n) cv := by
  iintro Hv #Hd #Hinv #Hlog
  unfold voterStart
  icases Hv with ⟨#Hb, ⟨Hrs, Hvac⟩, Hsh, Hbt⟩
  iframe Hb Hrs Hvac
  iapply startTraceC_intro γ γd tn (tcVoters n) cv Htr Hvs Hpv Hcq
    (by rw [tcVoters_length]; unfold tracecheck.maxNodes at h5; omega) Hnil N Hfit
    $$ Hd Hinv Hlog Hsh Hbt

/-- **The end of the run** (§2.2's last row): the `StartNode`s' `startDone`s, one voter's
`nodeBoot`, the directory and the simulation's invariant give `runOver c` (`runOver_intro`, at the
`n ≤ maxNodes` voters: fewer than `2^40` and than `numBound`). -/
theorem probeA_end (n : Nat) (h1 : 1 ≤ n) (h5 : n ≤ tracecheck.maxNodes) (c r : Loc) (γ : Cluster)
    (N : Namespace) (γd : GName) (tn : TraceNames) (id : w64)
    (htr : Cluster.trace γ = some γd) :
    ⊢ c.[G.Cluster, go!"rec"] ↦□ r -∗ isSyncRecorder (GF := GF) tn.tr r -∗
      nodeBoot γ N (tcVoters n) (tcCtxs n) id -∗ traceDir γd tn -∗ Cluster.traceSim γ (tcVoters n) tn -∗
      □ ([∗list] i ∈ tcVoters n, startDone γ i) -∗ runOver c := by
  obtain ⟨Hne, -, -, -, Hl40⟩ := tcVoters_facts n h1 h5
  have hl := tcVoters_length n
  unfold tracecheck.maxNodes at h5
  iintro #Hc #Hr #Hb #Hd #Hinv #Hs
  iapply runOver_intro c r γ N (tcVoters n) (tcCtxs n) id γd tn htr Hne Hl40
    (by rw [hl]; unfold Etcdraft.numBound; omega) $$ Hc Hr Hb Hd Hinv Hs

/-! ## 2. `handleReady`'s refutations and its `ConfChangeV2` arm (§2.3, A6) -/

/-- **No snapshot `Ready`** (§2.3, S12): a `Ready` with a snapshot loan holds its certificate
(`readySnap`, raft's exposed vocabulary: unfolded, as kv's and kvreconf's `run` do), which
`snapshotCert_made` turns into `snapMade`, against `tcSnapsInv`'s empty record (`snapMade_elem`). -/
theorem probeA_noSnap (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (l : SnapLoan) (E : CoPset) (hE : ↑tcSnapsN ⊆ E) :
    ⊢ isCluster (GF := GF) γ N -∗ tcSnapsInv γ -∗ readySnap γ N id rd st ce es (some l) ={E}=∗
      False := by
  iintro #Hc #Hinv Hs
  iunfold readySnap at Hs
  icases Hs with ⟨-, -, -, #Hcert, -⟩
  icases snapshotCert_made γ N _ $$ [Hc Hcert] with ⟨%l', %m, -, -, #Hmade, -⟩
  · iframe Hc Hcert
  unfold tcSnapsInv
  iinv Hinv with >Hown Hclose
  ihave %Hel := snapMade_elem γ [] _ $$ [Hown Hmade]
  · iframe Hown Hmade
  simp at Hel

/-- The pure core of the `ConfChangeV2` arm (§2.3, A6): a committed entry of type `2` is an empty
`ConfChangeV2`, from `tcOpsInv`'s clause and the committed operations' prefix (`ownCommittedOps_lb_prefix`):
not a filler (type `2`), not empty, it would be a requested entry, so in `boot` (whose entries are
`AddNode`s, type `1`: `BootLog`) or past it (the proposer's, type `0`). No position argument is needed. -/
theorem tc_emptyV2 (boot ops l : List LogEntry) (e : LogEntry) {n : Nat} (HB : BootLogFacts n boot)
    (hops : boot <+: ops ∧ ∀ op ∈ ops.drop boot.length, op.type = W32 0) (hpre : opsOf l <+: ops)
    (he : e ∈ l) (ht : e.type = W32 2) : e.isEmptyV2 := by
  by_cases hne : e.isEmptyV2
  · exact hne
  exfalso
  have hf : ¬ e.isFiller := fun h => by
    have := h.2; rw [ht] at this; exact w32_2_ne_0 this
  have hin : e ∈ opsOf l := by
    unfold opsOf; simp only [List.mem_filter]; exact ⟨he, by simp [hf, hne]⟩
  have hops' : e ∈ ops := hpre.subset hin
  obtain ⟨rest, hrest⟩ := hops.1
  have hdrop : ops.drop boot.length = rest := by subst hrest; simp
  rw [← hrest] at hops'
  rcases List.mem_append.1 hops' with hb | hr
  · obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem hb
    obtain ⟨_, _, _, _, _, ht1, _⟩ := HB.2.2 k e (by rw [List.getElem?_eq_some_iff]; exact ⟨hk, hkb⟩)
    rw [ht] at ht1; exact w32_2_ne_1 ht1
  · have := hops.2 e (by rw [hdrop]; exact hr)
    rw [ht] at this; exact w32_2_ne_0 this

/-- **The committed entries of type `2` are empty `ConfChangeV2`s** (the design's `tc_confShaped`,
in the form the arm uses): `tcOpsInv` opened, `ownCommittedOps_lb_prefix`, `tc_emptyV2`. -/
theorem tcOps_emptyV2 (γ : Cluster) (boot l : List LogEntry) (E : CoPset) {n : Nat} (HB : BootLogFacts n boot)
    (hE : ↑tcOpsN ⊆ E) :
    ⊢ tcOpsInv (GF := GF) γ boot -∗ isCommittedLogLb γ l ={E}=∗
      ⌜∀ e ∈ l, e.type = W32 2 → e.isEmptyV2⌝ := by
  iintro #Hops #Hl
  unfold tcOpsInv
  iinv Hops with >Hb Hclose
  unfold tcOpsBody
  icases Hb with ⟨%ops, Hown, %Hops⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γ ops l $$ [Hown Hl]
  · iframe Hown Hl
  imod Hclose $$ [Hown] with -
  · inext; iexists ops; iframe Hown; ipureintro; exact Hops
  imodintro
  ipureintro
  exact fun e he ht => tc_emptyV2 boot ops l e HB Hops Hpre he ht

/-- The bootstrap log's entries are requested entries (type `1`: no filler, no empty
`ConfChangeV2`). -/
theorem opsOf_boot_append (boot x : List LogEntry) {n : Nat} (HB : BootLogFacts n boot) :
    opsOf (boot ++ x) = boot ++ opsOf x := by
  unfold opsOf
  rw [List.filter_append]
  congr 1
  apply List.filter_eq_self.2
  intro e he
  obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem he
  obtain ⟨_, _, _, _, _, ht1, _⟩ := HB.2.2 k e (by rw [List.getElem?_eq_some_iff]; exact ⟨hk, hkb⟩)
  have h1 : ¬ e.isFiller := fun h => w32_1_ne_0 (ht1 ▸ h.2)
  have h2 : ¬ e.isEmptyV2 := fun h => w32_2_ne_1 (h.2 ▸ ht1)
  simp [h1, h2]

/-- **A committed `ConfChange` (type `1`) is at a bootstrap position** (A6's `ConfChange` arm: "past the
bootstrap log, impossible"): past `boot` the requested entries are the proposer's (type `0`), and a
type-`1` entry is a requested one. Positional, through the prefix `opsOf l <+: ops`. -/
theorem tc_v1_boot (boot ops l : List LogEntry) (k : Nat) (e : LogEntry) {n : Nat} (HB : BootLogFacts n boot)
    (hops : boot <+: ops ∧ ∀ op ∈ ops.drop boot.length, op.type = W32 0) (hpre : opsOf l <+: ops)
    (hbl : boot <+: l) (hk : l[k]? = some e) (ht : e.type = W32 1) : k < boot.length := by
  by_cases hlt : k < boot.length
  · exact hlt
  exfalso
  obtain ⟨x, rfl⟩ := hbl
  obtain ⟨rest, hrest⟩ := hops.1
  have hdrop : ops.drop boot.length = rest := by subst hrest; simp
  rw [opsOf_boot_append boot x HB, ← hrest] at hpre
  have hpx : opsOf x <+: rest := (List.prefix_append_right_inj boot).1 hpre
  have hkx : x[k - boot.length]? = some e := by
    rw [List.getElem?_append_right (by omega)] at hk; exact hk
  have hf : ¬ e.isFiller := fun h => w32_1_ne_0 (ht ▸ h.2)
  have h2 : ¬ e.isEmptyV2 := fun h => w32_2_ne_1 (h.2 ▸ ht)
  have hin : e ∈ opsOf x := by
    unfold opsOf; simp only [List.mem_filter]
    exact ⟨List.mem_of_getElem? hkx, by simp [hf, h2]⟩
  have := hops.2 e (by rw [hdrop]; exact hpx.subset hin)
  rw [ht] at this; exact w32_1_ne_0 this

/-- **The committed `ConfChange`s are the bootstrap log's** (the Iris form: `tcOpsInv` opened,
`ownCommittedOps_lb_prefix`, the committed log's agreement with `boot`). At such a position the entry is
the voter's `AddNode` (`BootLogFacts`), and `Membership.applyChange_addVoter` gives the step at the
simple membership of the voters: A6's `ConfChange` arm needs nothing else. -/
theorem tcOps_v1_boot (γ : Cluster) (boot l : List LogEntry) (E : CoPset) {n : Nat} (HB : BootLogFacts n boot)
    (hE : ↑tcOpsN ⊆ E) :
    ⊢ tcOpsInv (GF := GF) γ boot -∗ isCommittedLogLb γ boot -∗ isCommittedLogLb γ l ={E}=∗
      ⌜∀ (k : Nat) (e : LogEntry), l[k]? = some e → e.type = W32 1 → k < boot.length⌝ := by
  iintro #Hops #Hb #Hl
  icases isCommittedLogLb_agree γ boot l $$ [Hb Hl] with %Hag
  · iframe Hb Hl
  unfold tcOpsInv
  iinv Hops with >Hbd Hclose
  unfold tcOpsBody
  icases Hbd with ⟨%ops, Hown, %Hops⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γ ops l $$ [Hown Hl]
  · iframe Hown Hl
  imod Hclose $$ [Hown] with -
  · inext; iexists ops; iframe Hown; ipureintro; exact Hops
  imodintro
  ipureintro
  intro k e hk ht
  rcases Hag with hbl | hlb
  · exact tc_v1_boot boot ops l k e HB Hops Hpre hbl hk ht
  · have := (List.getElem?_eq_some_iff.1 hk).1
    have := hlb.length_le
    omega

/-- **The `ConfChangeV2` arm** (§2.3, A6): a committed entry `e` of type `2` at position `k`, where
the membership is `m`: it decodes to the empty change (`ccDecodeV2_nil`, so `proto.Unmarshal` returns no
error and the `panic` is not reached), the membership is joint (`committed_emptyV2_joint`), the change
applies (`Membership.applyChange_leaveJoint`, the probe's P1, at the membership's `Restorable`,
`confAt_restorable`), and `confPolicy_decide` records `.apply` of it: `node.ApplyConfChange.spec`'s
`confDecided` and its two `applyChange` premises (`o = o'`, at the view's membership `m`). -/
theorem probeA_confV2 (γ : Cluster) (N : Namespace) (boot l : List LogEntry)
    (k : Nat) (e : LogEntry) (m : Membership) (E : CoPset) {n : Nat} (HB : BootLogFacts n boot)
    (hk : l[k]? = some e) (ht : e.type = W32 2) (hE1 : ↑tcOpsN ⊆ E) (hE2 : ↑tcConfN ⊆ E) :
    ⊢ isCluster (GF := GF) γ N -∗ tcOpsInv γ boot -∗ confPolicy γ tcConfN tcRule -∗
      isCommittedLogLb γ l -∗ confAt γ k m ={E}=∗
      ∃ m', ⌜ccDecode e = some (.v2 ConfChangeV2M.empty) ∧
          Membership.applyChange (.v2 ConfChangeV2M.empty) m = some m'⌝ ∗
        confDecided γ k (.apply (.v2 ConfChangeV2M.empty)) := by
  iintro #Hc #Hops #Hpol #Hl #Ha
  -- the entry is an empty `ConfChangeV2`: `tcOpsInv`'s clause
  imod tcOps_emptyV2 γ boot l E HB hE1 $$ Hops Hl with %Hall
  have He2 : e.isEmptyV2 := Hall e (List.mem_of_getElem? hk) ht
  have Hdec : ccDecode e = some (.v2 ConfChangeV2M.empty) := by
    unfold ccDecode
    have h1 : e.type ≠ W32 1 := by rw [ht]; exact w32_2_ne_1
    rw [if_neg h1, if_pos ht, He2.1, ccDecodeV2_nil]; rfl
  ihave %Hv := confAt_valid γ k m $$ Ha
  ihave %Hr := confAt_restorable γ k m $$ Ha
  ihave %Hj := committed_emptyV2_joint γ N l k e m hk He2 $$ [Hc Hl Ha]
  · iframe Hc Hl Ha
  obtain ⟨m', hm'⟩ := Membership.applyChange_leaveJoint m Hv Hr Hj
  have hc : e.isConfChange := .inr ht
  have hs : (ConfDecision.ofRule (tcRule (l.take k) m e)).step m = some m' := by
    simp only [tcRule, Hdec, ConfDecision.ofRule, ConfDecision.step]; exact hm'
  imod confPolicy_decide γ N tcConfN E tcRule l k e m m' hk hc hE2 hs $$ [Hc Hpol Hl Ha] with #Hd
  · iframe Hc Hpol Hl Ha
  imodintro
  iexists m'
  isplitr
  · ipureintro; exact ⟨Hdec, hm'⟩
  simp only [tcRule, Hdec, ConfDecision.ofRule]
  iexact Hd

end ghost

/-! ## 3. `Ready`, `Advance` and the claim (§3.1, A5) -/

section claim
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A received `Ready`, taken apart** (the check "the claim's `ms` against `readyGot`'s `ms` and
`rd.Messages`"): the messages `rd.Messages'` points to, each owned with its credits, the claim on the
same list, *enter* (whose post gives their `sentMsg`s), the storage part, and the `Ready`'s loop state
handling the batch (what `node.Advance`'s premise `st.handling = some (es, L)` reads). -/
theorem probeA_readySplit (n : NodeH) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState)
    (rd : Ready) :
    readyGotT (GF := GF) n γ N id st rd ⊢
      ∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan)
        (ms : List QMsg) (ss : Option (w64 × StateType)),
        rd.Messages' ↦* ms.map QMsg.loc ∗
        ([∗list] q ∈ ms, msgOut γ q.loc (readyDq q.st) q.st ∗ msgCredits γ N q.st) ∗
        readySnap γ N id rd st ce es L ∗
        readyEnter n γ N id st (st.afterReady ce es h L ss) ms ∗ readyToksClaim n γ N ms ∗
        ⌜(st.afterReady ce es h L ss).handling = some (es, L)⌝ := by
  unfold readyGotT readyRest
  iintro ⟨%ce, %es, %h, %L, %ms, %ss, -, -, -, -, ⟨-, Hmsl, Hms, -, -, -, -, Hsnap, -⟩, -, Hent, -, -,
    Hcl⟩
  iexists ce, es, h, L, ms, ss
  iframe Hmsl Hms Hsnap Hent Hcl
  ipureintro; rfl

/-- **The messages' resources after `Advance`** (the check "`trTok` against `stepIn_intro`'s `st`"):
`readyRest`'s owned messages with credits, *enter*'s `readyMsgs` (`readyMsgs_sent`) and `Advance`'s
tokens give, for each message, what `send` takes: its `msgOwn` at `readyDq`, `sentMsg`, credits and
token, at one `q.st`. -/
theorem probeA_msgs (γ : Cluster) (N : Namespace) (src : w64) (ms : List QMsg) :
    ⊢ ([∗list] q ∈ ms, msgOut (GF := GF) γ q.loc (readyDq q.st) q.st ∗ msgCredits γ N q.st) -∗
      readyMsgs γ N src ms -∗ ([∗list] q ∈ ms, trTok γ q.st) -∗
      [∗list] q ∈ ms, (msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N src q.st ∗
        msgCredits γ N q.st) ∗ trTok γ q.st := by
  iintro Hm #Hs Ht
  ihave H := readyMsgs_sent γ N src ms $$ [Hm Hs]
  · iframe Hm Hs
  iapply (BigSepL.bigSepL_sep_eqv (Φ := fun (_ : Nat) (q : QMsg) => iprop(msgOwn (GF := GF) q.loc
      (readyDq q.st) q.st ∗ sentMsg γ N src q.st ∗ msgCredits γ N q.st))
    (Ψ := fun (_ : Nat) (q : QMsg) => trTok (GF := GF) γ q.st)).2
  iframe H Ht

end claim

/-! ## 4. `send`: the clone, the token, `Step` (§2.3, §2.4) -/

section send
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A clone's wire content and responses give the message `stepIn_intro` takes: `pbMessage`'s `eqv`
with the original's empty responses (`sentMsg_shape`). -/
theorem clone_st (st st' : MsgSt) (hr : st.resps = [])
    (heqv : wireOf st = wireOf st' ∧ (st.resps = [] → st'.resps = [])) :
    st' = ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ := by
  obtain ⟨hw, hr'⟩ := heqv
  have hr2 := hr' hr
  cases st'
  simp only [wireOf, MsgWire.mk.injEq] at hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  simp only at hr2
  subst h1 h2 h3 h4 hr2
  rfl

/-- **`proto.Clone` of a frozen raft message without responses**, in the shape the harness uses:
the clone owned, decoded (`msgPtsC … true`), at the original's wire content with empty responses.
From `ClonePb`'s per-type spec at the registered `pbMessageC` (`pbMessageC_reg`), the frozen message
at its wire content by `msgOwn_msgRoC`; the original marshals (no responses), so the clone is at the
same content, whose snapshot conf states have no unknown fields (`decOk`). -/
theorem wp_Clone_msg (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG))
    (l : Loc) (st : MsgSt) (hr : st.resps = []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
        msgOwn l DFrac.discard st }}
      (App (Val (@! google_golang_org.protobuf.proto.Clone))
        (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l)))
    {{ (l' : Loc), RET #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l');
        ∃ st' : MsgSt, msgPtsC l' (DFrac.own 1) (DFrac.own 1) true st' ∗
          ⌜wireOf st = wireOf st' ∧ (st.resps = [] → st'.resps = [])⌝ }} := by
  iintro %Φ ⟨#Hpi, #Hro⟩ HΦ
  ihave ⟨%c, #Hc, %Hcm⟩ := msgOwn_msgRoC l st hr $$ Hro
  have Hcl := wp_Clone pbMessageC pbMessageC_reg l c
  simp only [pbMessageC_ty, pbMessageC_roC, pbMessageC_decC, pbMessageC_eqv, pbMessageC_modelOf,
    pbMessageC_C, pbMessageC_marshals, pbMessageC_ufValid] at Hcl
  iapply Hcl $$ [] [HΦ]
  · iframe Hpi Hc
  inext
  iintro %l' ⟨%c', Hdec, %Hp⟩
  have hm : MsgMarshals c.model := by simp only [MsgMarshals, Hcm.1, hr]
  have hc' : c' = c := Hp.2.2 hm
  subst hc'
  iapply HΦ
  iexists c'.model
  isplitl [Hdec]
  · iapply msgPtsCC_msgPtsC _ _ _ _ _ Hcm.2 $$ Hdec
  · ipureintro; rw [Hcm.1]; exact ⟨rfl, fun h => h⟩

/-- **`proto.Clone(m)` then `node.Step(ctx, clone)`** (§2.3's last row, §2.4; S1's correction, the
uncertain glue of design-r3's A6): `ClonePb`'s `T.ro` from the `Ready`'s `msgOwn … (readyDq q.st)`
(`msgOwn_persist`), its `T.dec`/`eqv` into `msgPtsC … ⟨…, []⟩` (`clone_st`, the original's responses
empty by `sentMsg_shape`), `stepIn_intro` with the token at the same `q.st`, the snapshot local by the
harness's `snapLoc` (`snapLocalMsg_noDir`), then `node.Step.spec`. -/
theorem probeA_cloneStep
    (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG))
    (wp_Step : node.Step.spec (GF := GF) (hG := hG))
    (n : NodeH) (γ : Cluster) (N : Namespace) (id src : w64) (q : QMsg) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (hto : q.st.msg.To' = id) (hsl : γ.snapLoc id = none)
    (hmd : γ.maxData = none) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗ isNode n γ N id -∗ nodeCtx ctx cd -∗
      msgOwn q.loc (readyDq q.st) q.st -∗ sentMsg γ N src q.st -∗ msgCredits γ N q.st -∗
      trTok γ q.st -∗
      WP (App (Val (@! google_golang_org.protobuf.proto.Clone))
          (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #q.loc)))
        {{ v, ∃ l' : Loc, ⌜v = #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l')⌝ ∗
            WP (App (App (Val (n.loc @!! go.GoType.PointerType node.ty @!! go!"Step"))
                (Val #(interface.ok ctx))) (Val #l'))
              {{ e, ∃ err : GoInterface, ⌜e = #err⌝ ∗ nodeErrS n γ N cd err }} }} := by
  iintro #Hpi #Hri #Hn #Hctx Hmo #Hs Hcr Htok
  ihave %Hsh := sentMsg_shape γ N src q.st $$ Hs
  have hr : q.st.resps = [] := by have := Hsh.1; unfold SentMsgShape at this; exact this.2.2.2.2.2.2.2
  imod msgOwn_persist q.loc (readyDq q.st) q.st $$ Hmo with #Hro
  have Hcl := wp_Clone_msg wp_Clone q.loc q.st hr
  iapply Hcl $$ [] [Hcr Htok]
  · iframe Hpi Hro
  inext
  iintro %l' ⟨%st', Hdec, %Heqv⟩
  iexists l'
  isplitr
  · ipureintro; rfl
  have Hst := clone_st q.st st' hr Heqv
  ihave #Hloc := snapLocalMsg_noDir (GF := GF) γ id hsl q.st
  -- (raft-entsize §2) the clone's content form; no bound on proposed data (`hmd`)
  icases msgPtsC_msgPtsCC _ _ _ _ _ $$ Hdec with ⟨%cm, Hdec, %Hcm⟩
  imod stepIn_intro γ N id l' src q.st cm hto (Hcm.1.trans Hst) Hcm.2
    (fun b h => by simp [hmd] at h) $$ [Hdec Hcr Htok] with Hstep
  · iframe Hs Hdec Hcr Hloc Htok
  iapply (wp_Step n γ N id l' ctx cd) $$ [Hstep] []
  · iframe Hri Hn Hctx Hstep
  inext
  iintro %err Herr
  iexists err
  iframe Herr
  ipureintro; rfl

/-- **The `MsgSnap` branches are dead** (§2.4): at a traced cluster the token says the message is no
`MsgSnap` (`trTok_type`), read before `Step` consumes it; the clone's type is the original's (its wire
content, `pbMessage`'s `eqv`), which is what `send`'s `typ := m.GetType()` reads. -/
theorem probeA_noSnapReport (γ : Cluster) (γd : GName)
    (htr : Cluster.trace γ = some γd) (st st' : MsgSt) (hw : wireOf st = wireOf st') :
    trTok (GF := GF) γ st ⊢ trTok γ st ∗ ⌜st'.msg.Type' ≠ MsgSnap⌝ := by
  iintro Ht
  icases trTok_type γ st $$ Ht with ⟨Ht, %Hty⟩
  iframe Ht
  ipureintro
  have : st.msg = st'.msg := by simp only [wireOf, MsgWire.mk.injEq] at hw; exact hw.1
  rw [← this]; exact Hty (by rw [htr]; simp)

end send

/-! ## 5. The thread tokens (§2.2's `app` fork, §2.4, §6 B5) -/

section toks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `netJoin.wp_Add` (§6, Q34), over the design's sealed `njAdder`/`njDone` and the call's expression
`eAdd` (`c.net.Add(1)`). -/
abbrev NetJoinAdd (njAdder : Qp → IProp GF) (njDone : IProp GF) (eAdd : Expr) : Prop :=
  ∀ q : Qp, {{ njAdder q ∗ threadTok }} eAdd {{ RET #(); njAdder q ∗ njDone }}

/-- `netJoin.wp_Done` (§6): the slot's token back. -/
abbrev NetJoinDone (njDone : IProp GF) (eDone : Expr) : Prop :=
  {{ njDone }} eDone {{ RET #(); threadTok }}

/-- **`app`'s token through a `send`** (§2.4, B5; the check "`app`'s token through each round"): the
token `app` holds goes into the network's invariant at `Add`; the goroutine is forked by
`wp_fork_tok_self`, the fresh token staying with `app`, so `app` ends the call as it began
(`njAdder q ∗ threadTok`); the goroutine must end with a token (`hG`), which its deferred `Done` gives
(`probeA_goroutineEnd`). -/
theorem probeA_appToken (njAdder : Qp → IProp GF) (njDone : IProp GF) (eAdd eG : Expr)
    (hAdd : NetJoinAdd njAdder njDone eAdd) (q : Qp) (R : IProp GF)
    (hG : R ∗ njDone ⊢ WP eG {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) :
    ⊢ njAdder q ∗ threadTok ∗ R -∗
      WP eAdd {{ _v, WP (Expr.Fork eG) {{ _w, njAdder q ∗ threadTok }} }} := by
  iintro ⟨Ha, Ht, HR⟩
  iapply (hAdd q) $$ [Ha Ht] [HR]
  · iframe Ha Ht
  inext
  iintro ⟨Ha, Hd⟩
  iapply wp_fork_tok_self $$ [HR Hd] [Ha]
  · inext; iapply hG; iframe HR Hd
  · inext; iintro Ht; iframe Ha Ht

/-- **The goroutine's end** (§2.4's `defer c.net.Done()`): `Done` hands back the token
`wp_fork_tok_self` requires of the forked thread. -/
theorem probeA_goroutineEnd (njDone : IProp GF) (eDone : Expr) (hDone : NetJoinDone njDone eDone) :
    ⊢ njDone -∗ WP eDone {{ v, ⌜v = #()⌝ ∗ threadTok }} := by
  iintro Hd
  iapply hDone $$ [Hd] []
  · iexact Hd
  inext
  iintro Ht
  iframe Ht
  ipureintro; rfl

/-- **The fork of `app`** (§2.2, B5): `wp_fork_tok_body` hands `app` the fresh token its precondition
names; `app` must return one (its `c.stop` arm). -/
theorem probeA_forkApp (eApp : Expr) (P : IProp GF)
    (happ : P ∗ threadTok ⊢ WP eApp {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) :
    ⊢ P -∗ WP (Expr.Fork eApp) {{ v, ⌜v = #()⌝ }} := by
  iintro HP
  iapply wp_fork_tok_body $$ [HP] []
  · inext; iintro Ht; iapply happ; iframe HP Ht
  · inext; ipureintro; rfl

end toks

end ProbeA
end TraceCheck
end EtcdGrove
end Perennial
