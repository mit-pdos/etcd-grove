/-
Lean-first (no Rocq counterpart). Trace-check's **Probe A** (`notes/trace-check-design.md` §8, revision 3;
`notes/spec-first-plan.md`, "Probe"; `notes/decisions.md`, "Probe A (harness glue)"): the harness-level
composition along the concrete path (`StartNode`, `Ready`, `handleReady`, `Advance`, then `send` →
`Step`), over the client statements, each post checked to supply the next pre.

A probe, not a result: nothing links it (no `Link`/`Results` imports it) and nothing here is used by a
proof. The statements the design specifies that do not exist in Lean yet are **hypotheses** here, each a
`Prop` (or a parameter standing for a sealed predicate the design adds to raft, with the laws the
client sees as hypotheses), never an axiom or a `sorry`:

- `readyToksClaim` (design §3.1): a parameter `claim` of the probe, its law `readyToksClaim_nil` the
  hypothesis `ClaimNil claim` (a client sees the sealed claim only through its laws);
- `isReadyChan_recvAu.tracedSpec` (revised: `readyGotT` with the claim): `RecvTracedSpec claim`, over
  `readyGotC claim`;
- `node.Advance.tracedSpec` (A5): `AdvanceTracedSpec claim`; its instance `node.Advance.spec_of_traced`
  is **proved** here (`advance_spec_of_traced`), from `ClaimNil` alone;
- `stepIn_intro` with `trTok` (F2): `StepInIntroTr`; the law `trTok_type`: `TrTokType`;
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

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.HarnessAlloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.HarnessEnd
public import Proof.go_etcd_io.raft.v3.ConfPolicy
public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PbMessage
public import Spec.google_golang_org.protobuf.proto.ClonePb
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2Empty
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__Step

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

/-- The three voters (`concurrent.go`: `Peer{ID: i}` for `i = 1, 2, 3`). -/
abbrev tcVoters : List w64 := [W64 1, W64 2, W64 3]
/-- Their bootstrap contexts (nil). -/
abbrev tcCtxs : List (List w8) := [[], [], []]

/-- `tracecheck.BootLogFacts` (§1.1). -/
abbrev BootLogFacts (boot : List LogEntry) : Prop := BootLog tcVoters tcCtxs boot

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

theorem tcVoters_facts :
    tcVoters ≠ [] ∧ tcVoters.Nodup ∧ W64 0 ∉ tcVoters ∧ (tcVoters.length : Int) < 2 ^ 62 ∧
      tcVoters.length < 2 ^ 40 := by
  refine ⟨by simp, ?_, ?_, by simp, by simp⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]
    refine ⟨?_, ?_, ?_, trivial⟩ <;> (try simp only [or_false]) <;> (intro h; rcases h with h | h <;> revert h <;> decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h) <;> revert h <;> decide

/-- **The harness's allocation, with its invariants** (§2.2): `harness_alloc` at the three voters,
then `tcOpsInv` from `ownCommittedOps γ boot`, `confPolicy` from `ownConfDecisions γ ∅`
(`confPolicy_alloc`), `tcSnapsInv` from `ownSnapsMade γ []`. Each comes out of `harness_alloc`'s post
as the design says. -/
theorem probeA_alloc (N : Namespace) (boot : List LogEntry) (γt : GName) (E : CoPset)
    (hE : ↑N ⊆ E) (Hrb : receiptBound GF ≤ 2 ^ 64 - 2) (HB : BootLogFacts boot) :
    ⊢ bootMarshal (GF := GF) tcVoters tcCtxs (LogEntry.toEntries boot 0) -∗ traceFrag γt [] ={E}=∗
      ∃ (γ : Cluster) (γd : GName) (tn : TraceNames),
        ⌜Cluster.trace γ = some γd ∧ tn.tr = γt ∧ tn.voters = tcVoters ∧
          γ.snapLoc = (fun _ => none) ∧ γ.dup = false ∧ γ.bootLen = boot.length⌝ ∗
        traceDir γd tn ∗ Cluster.traceSim γ tcVoters tn ∗ isCluster γ N ∗
        tcOpsInv γ boot ∗ confPolicy γ tcConfN tcRule ∗ tcSnapsInv γ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet tcVoters)) ∗ isCommittedLogLb γ boot ∗
        [∗list] i ∈ tcVoters, voterStart γ N tcVoters tcCtxs tn i := by
  obtain ⟨Hne, Hnd, Hnz, Hlen, -⟩ := tcVoters_facts
  iintro #Hm Hfr
  imod harness_alloc (GF := GF) N tcVoters tcCtxs boot γt E hE Hrb Hne Hnd Hnz Hlen HB $$ Hm Hfr
    with ⟨%γ, %γd, %tn, %Hγ, #Hd, #Hinv, Hops, -, #Hcl, Hdec, #Hca, Hsm, #Hlb, Hvs⟩
  obtain ⟨Htr, Htn, Hvs', Hdup, Hsl, Hbl⟩ := Hγ
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
  · ipureintro; exact ⟨Htr, Htn, Hvs', Hsl, Hdup, Hbl⟩
  unfold tcOpsInv tcSnapsInv
  iframe Hd Hinv Hcl Hops Hpol Hsn Hca Hlb Hvs

/-- **A voter's `StartNode` precondition from its part** (`voterStart`, `startTraceC_intro`): the
`nodeBoot`, durable state and vacant slot `StartNode.tracedSpec` takes, and its `startTraceC γ vs cv`
for a configuration of the voter's id logging to the names' trace. -/
theorem probeA_startPre (γ : Cluster) (N : Namespace) (γd : GName) (tn : TraceNames) (cv : Config)
    (Htr : Cluster.trace γ = some γd) (Hvs : tn.voters = tcVoters) (Hpv : cv.PreVote' = false)
    (Hcq : cv.CheckQuorum' = false) (Hnil : cv.TraceLogger' ≠ interface.nil) :
    ⊢ voterStart (GF := GF) γ N tcVoters tcCtxs tn cv.ID' -∗ traceDir γd tn -∗
      Cluster.traceSim γ tcVoters tn -∗ isTraceLogger tn.tr cv.TraceLogger' -∗
      nodeBoot γ N tcVoters tcCtxs cv.ID' ∗ nodeVacant γ cv.ID' ∗ raftState γ cv.ID' RaftState.init ∗
        startTraceC γ tcVoters cv := by
  iintro Hv #Hd #Hinv #Hlog
  unfold voterStart
  icases Hv with ⟨#Hb, ⟨Hrs, Hvac⟩, Hsh, Hbt⟩
  iframe Hb Hrs Hvac
  iapply startTraceC_intro γ γd tn tcVoters cv Htr Hvs Hpv Hcq (by simp) Hnil
    $$ Hd Hinv Hlog Hsh Hbt

/-- **The end of the run** (§2.2's last row): the three `StartNode`s' `startDone`s, one voter's
`nodeBoot`, the directory and the simulation's invariant give `runOver c` (`runOver_intro`, at the
three voters: fewer than `2^40` and than `numBound`). -/
theorem probeA_end (c r : Loc) (γ : Cluster) (N : Namespace) (γd : GName) (tn : TraceNames)
    (htr : Cluster.trace γ = some γd) :
    ⊢ c.[G.Cluster, go!"rec"] ↦□ r -∗ isSyncRecorder (GF := GF) tn.tr r -∗
      nodeBoot γ N tcVoters tcCtxs (W64 1) -∗ traceDir γd tn -∗ Cluster.traceSim γ tcVoters tn -∗
      startDone γ (W64 1) -∗ startDone γ (W64 2) -∗ startDone γ (W64 3) -∗ runOver c := by
  iintro #Hc #Hr #Hb #Hd #Hinv #H1 #H2 #H3
  iapply runOver_intro c r γ N tcVoters tcCtxs (W64 1) γd tn htr (by simp) (by simp)
    (by simp [Etcdraft.numBound]) $$ Hc Hr Hb Hd Hinv
  imodintro
  iapply (BigSepL.bigSepL_cons (Φ := fun _ i => startDone (GF := GF) γ i)).2
  isplitr
  · iexact H1
  iapply (BigSepL.bigSepL_cons (Φ := fun _ i => startDone (GF := GF) γ i)).2
  isplitr
  · iexact H2
  iapply (BigSepL.bigSepL_cons (Φ := fun _ i => startDone (GF := GF) γ i)).2
  isplitr
  · iexact H3
  iapply (BigSepL.bigSepL_nil (Φ := fun _ i => startDone (GF := GF) γ i)).2
  iempintro

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
theorem tc_emptyV2 (boot ops l : List LogEntry) (e : LogEntry) (HB : BootLogFacts boot)
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
theorem tcOps_emptyV2 (γ : Cluster) (boot l : List LogEntry) (E : CoPset) (HB : BootLogFacts boot)
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
theorem opsOf_boot_append (boot x : List LogEntry) (HB : BootLogFacts boot) :
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
theorem tc_v1_boot (boot ops l : List LogEntry) (k : Nat) (e : LogEntry) (HB : BootLogFacts boot)
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
theorem tcOps_v1_boot (γ : Cluster) (boot l : List LogEntry) (E : CoPset) (HB : BootLogFacts boot)
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

/-- **Probe finding (P1): the empty `ConfChangeV2` applies at a valid joint membership.** What the
`ConfChangeV2` arm needs and raft does not export: `Membership.applyChange` is sealed and its laws
(`InvNode.lean`, `applyChange_nodeZero`/`_addVoter`/`_removeVoter`/`_removeAbsent`) are of simple
memberships only ("nothing is said of joint configurations"); `committed_emptyV2_joint` gives
`m.isJoint`, not the step. The fix: this law in raft's API (proved from `ccApplyM_leaveJoint`,
`ConfchangeApiImpl.lean:109`, and `leaveJointM`'s definedness at a valid joint state). -/
abbrev LeaveJoint : Prop :=
  ∀ m : Membership, m.Valid → m.isJoint →
    ∃ m', Membership.applyChange (.v2 ConfChangeV2M.empty) m = some m'

/-- **The `ConfChangeV2` arm** (§2.3, A6): a committed entry `e` of type `2` at position `k`, where
the membership is `m`: it decodes to the empty change (`ccDecodeV2_nil`, so `proto.Unmarshal` returns no
error and the `panic` is not reached), the membership is joint (`committed_emptyV2_joint`), the change
applies (`LeaveJoint`), and `confPolicy_decide` records `.apply` of it: `node.ApplyConfChange.spec`'s
`confDecided` and its two `applyChange` premises (`o = o'`, at the view's membership `m`). -/
theorem probeA_confV2 (hleave : LeaveJoint) (γ : Cluster) (N : Namespace) (boot l : List LogEntry)
    (k : Nat) (e : LogEntry) (m : Membership) (E : CoPset) (HB : BootLogFacts boot)
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
  ihave %Hj := committed_emptyV2_joint γ N l k e m hk He2 $$ [Hc Hl Ha]
  · iframe Hc Hl Ha
  obtain ⟨m', hm'⟩ := hleave m Hv Hj
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

/-- `readyToksClaim_nil` (§3.1, A5), of the probe's `claim` (the design's sealed `readyToksClaim`). -/
abbrev ClaimNil (claim : Loc → Cluster → Namespace → List QMsg → IProp GF) : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace), ⊢ claim n γ N []

/-- **The revised `readyGotT`** (§3.1): `readyGot` with the claim on its messages. **Probe finding
(P2):** the design writes `readyGotT = readyGot ∗ readyToksClaim n γ N ms`, where `ms` is unbound
(`readyGot` binds it inside its existentials); the claim must be inside them, at `readyRest`'s `ms`
(the messages `rd.Messages'` points to), as today's `readyGotT` places its tokens. -/
def readyGotC (claim : Loc → Cluster → Namespace → List QMsg → IProp GF) (n : Loc) (γ : Cluster)
    (N : Namespace) (id : w64) (st : NodeDriverState) (rd : Ready) : IProp GF :=
  iprop(∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan)
      (ms : List QMsg) (ss : Option (w64 × StateType)),
    committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
    isCommittedLogLb γ (st.delivered ++ ce) ∗
    (∃ rs, readStatesPts rd.ReadStates' rs ∗
      [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
    readyRest γ N id rd st ce es h L ms ss ∗
    readyLeaderMsgs γ N id st ms ss ∗
    readyEnter n γ N id st (st.afterReady ce es h L ss) ms ∗
    deliveredLogLb n γ N (st.afterReady ce es h L ss).delivered ∗
    (⌜phsNext st.hardState h = hsZero⌝ ∨
      committedAtTerm γ N (phsNext st.hardState h).Term' (phsNext st.hardState h).Commit' ∗
      ⌜((st.afterReady ce es h L ss).delivered.length : Int) ≤
        uint.Z (phsNext st.hardState h).Commit'⌝) ∗
    claim n γ N ms)

/-- **`isReadyChan_recvAu.tracedSpec`, revised** (§3.1): `readyGotC` for `readyGot`. -/
abbrev RecvTracedSpec (claim : Loc → Cluster → Namespace → List QMsg → IProp GF) : Prop :=
  ∀ (n ch : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState)
    (Φ : Ready → Bool → IProp GF),
  st.handling = none →
  ⊢ isReadyChan (GF := GF) n γ N ch -∗ isNode n γ N id -∗ nodeDriver n γ N st -∗
    ∃ γc : ChanNames, isChan ch γc Ready ∗
      (£ 1 ∗ £ 1 -∗
        ▷ (∀ rd : Ready, readyGotC claim n γ N id st rd -∗ Φ rd true) -∗
        recvAu γc Ready Φ)

/-- **`node.Advance.tracedSpec`** (§3.1, A5), as the design writes it. -/
abbrev AdvanceTracedSpec (claim : Loc → Cluster → Namespace → List QMsg → IProp GF) : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState) (es : List EntryM)
    (L : Option SnapLoan) (v : ConfigView) (ms : List QMsg),
  st.handling = some (es, L) →
  (∀ l, L = some l → l.dlv.length = uint.nat l.snap.Metadata'.Index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isCluster γ N ∗ isNode n γ N id ∗
      nodeDriver n γ N st ∗ advReceipt st.storage st.delivered.length es L ∗ nodeConfig n γ N v ∗
      (match L with
       | none => skippedIn γ st.delivered v.applied st.delivered.length
       | some l => snapshotCert γ N (snapTrip l.snap l.snap.Metadata'.ConfState'.lists)) ∗
      claim n γ N ms }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); (nodeDriver n γ N { st with handling := none } ∗
      nodeAppliedLb γ st.key st.delivered.length ∗
      (match L with
      | none => nodeConfig n γ N v
      | some l => ∃ m : Membership,
          nodeConfig n γ N ⟨uint.nat l.snap.Metadata'.Index', m⟩ ∗
          confAt γ (uint.nat l.snap.Metadata'.Index') m ∗
          ⌜confStateIs l.snap.Metadata'.ConfState' m⌝) ∗
      [∗list] q ∈ ms, trTok γ q.st) ∨
    (nodeStopped n γ N ∗ nodeDriver n γ N { st with handling := none }) }}

/-- **`node.Advance.spec_of_traced`** (A5), proved: `node.Advance.spec` (today's text, every `γ`) is
the traced spec's instance at `ms = []`, the claim from `ClaimNil`, the empty list of tokens dropped. -/
theorem advance_spec_of_traced (claim : Loc → Cluster → Namespace → List QMsg → IProp GF)
    (hnil : ClaimNil claim) (h : AdvanceTracedSpec claim) : node.Advance.spec (GF := GF) := by
  intro n γ N id st es L v Hh HL
  iintro %Φ Hpre HΦ
  iapply (h n γ N id st es L v [] Hh HL) $$ [Hpre] [HΦ]
  · icases Hpre with ⟨Hi, Hc, Hn, Hd, Hr, Hv, Hm⟩
    ihave Hcl := hnil n γ N
    iframe Hi Hc Hn Hd Hr Hv Hm Hcl
  · inext
    iintro Hpost
    iapply HΦ
    icases Hpost with (⟨Hd, Ha, Hm, -⟩ | Hs)
    · ileft; iframe Hd Ha Hm
    · iright; iexact Hs

/-- **A received `Ready`, taken apart** (the check "the claim's `ms` against `readyGot`'s `ms` and
`rd.Messages`"): the messages `rd.Messages'` points to, each owned with its credits, the claim on the
same list, *enter* (whose post gives their `sentMsg`s), the storage part, and the `Ready`'s loop state
handling the batch (what `node.Advance`'s premise `st.handling = some (es, L)` reads). -/
theorem probeA_readySplit (claim : Loc → Cluster → Namespace → List QMsg → IProp GF) (n : Loc)
    (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState) (rd : Ready) :
    readyGotC claim n γ N id st rd ⊢
      ∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan)
        (ms : List QMsg) (ss : Option (w64 × StateType)),
        rd.Messages' ↦* ms.map QMsg.loc ∗
        ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ msgCredits γ N q.st) ∗
        readySnap γ N id rd st ce es L ∗
        readyEnter n γ N id st (st.afterReady ce es h L ss) ms ∗ claim n γ N ms ∗
        ⌜(st.afterReady ce es h L ss).handling = some (es, L)⌝ := by
  unfold readyGotC readyRest
  iintro ⟨%ce, %es, %h, %L, %ms, %ss, -, -, -, ⟨-, Hmsl, Hms, -, -, -, Hsnap, -⟩, -, Hent, -, -,
    Hcl⟩
  iexists ce, es, h, L, ms, ss
  iframe Hmsl Hms Hsnap Hent Hcl
  ipureintro; rfl

/-- **The messages' resources after `Advance`** (the check "`trTok` against `stepIn_intro`'s `st`"):
`readyRest`'s owned messages with credits, *enter*'s `readyMsgs` (`readyMsgs_sent`) and `Advance`'s
tokens give, for each message, what `send` takes: its `msgOwn` at `readyDq`, `sentMsg`, credits and
token, at one `q.st`. -/
theorem probeA_msgs (γ : Cluster) (N : Namespace) (src : w64) (ms : List QMsg) :
    ⊢ ([∗list] q ∈ ms, msgOwn (GF := GF) q.loc (readyDq q.st) q.st ∗ msgCredits γ N q.st) -∗
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

/-- **One round of `app`, from the `Ready` to `Advance`'s return** (§2.3): the received `Ready`
(`readyGotC`), *enter* run with the driver's durable state and its share of `nodeRunning`, the snapshot
loan refuted (`probeA_noSnap`), `handleReady`'s storage and apply work (abstracted: `Hwork`, from the
`Ready`'s storage part, the batch's receipt and the view with the skipped conf entries: not on the
probe's list), then `node.Advance.tracedSpec` with the claim. Its post: for each message, what `send`
takes (`probeA_msgs`), or the node stopped. -/
theorem probeA_round (claim : Loc → Cluster → Namespace → List QMsg → IProp GF)
    (hadv : AdvanceTracedSpec claim) (n : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (st : NodeDriverState) (rd : Ready) (qr : Qp) (hN : ↑N ⊆ (⊤ : CoPset)) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗ isCluster γ N -∗ isNode n γ N id -∗
      tcSnapsInv γ -∗ readyGotC claim n γ N id st rd -∗
      raftState γ id st.durable -∗ nodeRunning n γ N qr -∗
      (∀ (ce : List LogEntry) (es : List EntryM), readySnap γ N id rd st ce es none -∗
        advReceipt st.storage (st.delivered ++ ce).length es none ∗
        ∃ v : ConfigView, nodeConfig n γ N v ∗
          skippedIn γ (st.delivered ++ ce) v.applied (st.delivered ++ ce).length) -∗
      |={⊤}=> ∃ (ms : List QMsg) (S : RaftState), rd.Messages' ↦* ms.map QMsg.loc ∗ raftState γ id S ∗
        nodeRunning n γ N qr ∗
        WP (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
          {{ v, ⌜v = #()⌝ ∗ ((∃ st', nodeDriver n γ N st' ∗
              [∗list] q ∈ ms, (msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N id q.st ∗
                msgCredits γ N q.st) ∗ trTok γ q.st) ∨
            (∃ st', nodeStopped n γ N ∗ nodeDriver n γ N st')) }} := by
  iintro #Hi #Hc #Hn #Hsn Hrg Hrs Hrun Hwork
  ihave Hsp := probeA_readySplit claim n γ N id st rd $$ Hrg
  icases Hsp with ⟨%ce, %es, %h, %L, %ms, %ss, Hmsl, Hms, Hsnap, Hent, Hcl, %Hh⟩
  cases L with
  | some l =>
    imod probeA_noSnap γ N id rd st ce es l ⊤ (fun _ _ => CoPset.mem_full) $$ Hc Hsn Hsnap
      with %Hf
    exact Hf.elim
  | none =>
  iunfold readyEnter at Hent
  imod Hent $$ %⊤ %qr %hN [Hrs Hrun] with ⟨Hrs, Hrun, Hdrv, #Hsent⟩
  · iframe Hrs Hrun
  ihave ⟨Hrec, %v, Hv, #Hsk⟩ := Hwork $$ %ce %es Hsnap
  imodintro
  iexists ms, _
  iframe Hmsl Hrs Hrun
  iapply (hadv n γ N id (st.afterReady ce es h none ss) es none v ms Hh
    (fun _ h => by cases h)) $$ [Hdrv Hrec Hv Hcl] [Hms]
  · iframe Hi Hc Hn Hdrv Hv Hcl
    simp only [NodeDriverState.afterReady]
    iframe Hrec Hsk
  · inext
    iintro Hpost
    isplitr
    · ipureintro; rfl
    icases Hpost with (⟨Hd, -, -, Ht⟩ | ⟨Hs, Hd⟩)
    · ileft
      iexists _
      iframe Hd
      iapply probeA_msgs γ N id ms $$ Hms Hsent Ht
    · iright
      iexists _
      iframe Hs Hd

end claim

/-! ## 4. `send`: the clone, the token, `Step` (§2.3, §2.4) -/

section send
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`stepIn_intro` with the token** (§3.1, F2), as the design writes it. -/
abbrev StepInIntroTr : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (src : w64) (st : MsgSt),
    st.msg.To' = id →
    sentMsg (GF := GF) γ N src st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ∗ snapLocalMsg γ id st ∗ trTok γ st ⊢
    |==> stepIn γ N id ml

/-- **The law `trTok_type`** (§2.4), as the design writes it. -/
abbrev TrTokType : Prop :=
  ∀ (γ : Cluster) (st : MsgSt),
    trTok (GF := GF) γ st ⊢ trTok γ st ∗ ⌜Cluster.trace γ ≠ none → st.msg.Type' ≠ MsgSnap⌝

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

/-- **`proto.Clone(m)` then `node.Step(ctx, clone)`** (§2.3's last row, §2.4; S1's correction, the
uncertain glue of design-r3's A6): `ClonePb`'s `T.ro` from the `Ready`'s `msgOwn … (readyDq q.st)`
(`msgOwn_persist`), its `T.dec`/`eqv` into `msgPtsC … ⟨…, []⟩` (`clone_st`, the original's responses
empty by `sentMsg_shape`), `stepIn_intro` with the token at the same `q.st`, the snapshot local by the
harness's `snapLoc` (`snapLocalMsg_noDir`), then `node.Step.spec`. -/
theorem probeA_cloneStep (hSI : StepInIntroTr (GF := GF))
    (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG))
    (wp_Step : node.Step.spec (GF := GF) (hG := hG))
    (n : Loc) (γ : Cluster) (N : Namespace) (id src : w64) (q : QMsg) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (hto : q.st.msg.To' = id) (hsl : γ.snapLoc id = none) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗ isNode n γ N id -∗ nodeCtx ctx cd -∗
      msgOwn q.loc (readyDq q.st) q.st -∗ sentMsg γ N src q.st -∗ msgCredits γ N q.st -∗
      trTok γ q.st -∗
      WP (App (Val (@! google_golang_org.protobuf.proto.Clone))
          (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #q.loc)))
        {{ v, ∃ l' : Loc, ⌜v = #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l')⌝ ∗
            WP (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Step"))
                (Val #(interface.ok ctx))) (Val #l'))
              {{ e, ∃ err : GoInterface, ⌜e = #err⌝ ∗ nodeErrS n γ N cd err }} }} := by
  iintro #Hpi #Hri #Hn #Hctx Hmo #Hs Hcr Htok
  ihave %Hsh := sentMsg_shape γ N src q.st $$ Hs
  have hr : q.st.resps = [] := by have := Hsh.1; unfold SentMsgShape at this; exact this.2.2.2.2.2.2.2
  imod msgOwn_persist q.loc (readyDq q.st) q.st $$ Hmo with #Hro
  have Hcl := wp_Clone (pbMessage (GF := GF)) q.loc q.st
  simp only [pbMessage_ty, pbMessage_ro] at Hcl
  iapply Hcl $$ [] [Hcr Htok]
  · iframe Hpi Hro
  inext
  iintro %l' ⟨%st', Hdec, %Heqv⟩
  iexists l'
  isplitr
  · ipureintro; rfl
  have Hst := clone_st q.st st' hr Heqv
  ihave #Hloc := snapLocalMsg_noDir (GF := GF) γ id hsl q.st
  imod hSI γ N id l' src q.st hto $$ [Hdec Hcr Htok] with Hstep
  · iframe Hs Hcr Hloc Htok
    rw [← Hst]
    iExactEq Hdec
    rfl
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
theorem probeA_noSnapReport (htt : TrTokType (GF := GF)) (γ : Cluster) (γd : GName)
    (htr : Cluster.trace γ = some γd) (st st' : MsgSt) (hw : wireOf st = wireOf st') :
    trTok (GF := GF) γ st ⊢ trTok γ st ∗ ⌜st'.msg.Type' ≠ MsgSnap⌝ := by
  iintro Ht
  icases htt γ st $$ Ht with ⟨Ht, %Hty⟩
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
