# Raft's node API, unified: candidate 12 (2026-10-28), one text — frozen for implementation

Changes from candidate 11 (review 11): K1 a hold mark (`storHoldMark`) so `storHoldsLb` stays persistent
and kvreconf keeps its mid-`Ready` snapshots; K2 `snapshotCert_make`'s `i < 2^61`; K3 `applyChange_valid`
deleted; K4 `CreateSnapshot` over today's resources and mask; K5/K9 every stopped answer with
`nodeStopped`, the server's `nodeLive` hand-back (U10); K10 kvreconf's size check keeps the `Changer`'s
`prs`; K11 `Membership.empty`. Reviews 1..11 (`notes/spec-first-study/raft-node-unified-review-*.md`).
Remaining (Tier 2-3, implementation): K6 the plan's U7-U11 wording, K7 the assembly law as a record
update, K8 nits.

Changes from candidate 10 (review 10): J1 `ConfRule.Ok`/`clamp` over `Valid` results, `WellFormed` = empty or
`Valid`, a size law and `validConf`'s size check in Go; J2 `CreateSnapshot`'s two continuations per branch over
`memSnapTokG`; J3 `nodeLive` (fractional; `Stop` takes it whole, a holder rules out stopped answers); J4
`storHoldsLb` a `StorageModel` field, from `appendReceipt`, its persistence an U8 invariant; J5
`SetHardState` importable; J6 a cluster without a bootstrap log bounds a `MsgSnap`'s index by the
certificate's `SnapListsOk`; J7 `storHoldsLb` through the clients' hand-offs (U10); J8 `ownTrackerM_assemble`
as a record update; J9 nits. Reviews 1..10.

Changes from candidate 9 (review 9): H1 `CreateSnapshot` over a persistent `storHoldsLb` (from the append and
from `Advance`), its triple written out, the term fixed in the post; H2 `applyChange` is Go's, `WellFormed`
for the empty membership, `ownCfgPairM` and the assembly law; H3 the server's re-certification an
obligation in the plan (U10); H4 the `MsgSnap` index bound in `SentMsgShape`; H5 the plan's text; H6 nits:
reviews 1..9, `nodeStorage` gone (not needed); H7 filed (`issues/raft-committedentries-stable-storage-doc.md`).

Changes from candidate 8 (review 8): G1/G2/G5 today's storage specs kept, `CreateSnapshot` bounded by the
node's delivered log instead of the floor (`storWriter`/`storCommittedAt` withdrawn); G3 the length law
`l.length < 2^61`; G6 `readyFits` only with a bootstrap log (kv's adequacy bound unchanged); G4 importable
`confchange`/`tracker` specs over `ownTrackerM` (§4b); G7 `NoDupLists` premise dropped; G9 the newcomer
restriction in §6; G10 the fold's step laws written out, `nodeConfig_reject` without an update; G12 the
axiom's reach in §6.

Scratch file, never committed. Supersedes candidates 1-7. One mode: snapshots and reconfiguration
together. Reviews: `notes/spec-first-study/raft-node-unified-review-{1..7}.md`.

Changes from candidate 7 (review 7): F1 `receiptBound GF ≤ 2^61` for every cluster, `readyFits` always
given, `isCommittedLogLb_length` over `readyFits`; F2 `clamp_eq` pointwise; F3 `storAppended` replaced by
the writer's exclusive `storWriter` and the persistent `storCommittedAt`; F4 the Go change to `applyEntry`
dropped (the axiom is needed by the rule and by U5 anyway); F5 newcomers at `c0` a recorded scope
restriction; F7 `stepIn_intro`'s shape premise dropped; F8 `sentMsg_noTransfer` excludes
`MsgTransferLeader` too; F9 `bootedCluster`, `nodeBoot_booted` removed; F10 `fold_total`'s premise
explained; F11 the stopped `Step`'s answer; F12 U6m: one mechanism (no undecided conf entry), no separate
reject step; F13 the stopped case a case split in each method's one triple (no second spec file); F14
`SnapListsOk` reduced to what is not derivable.

Changes from candidate 6 (review 6): E1 the certificate at the committed term only (candidate 5's form),
`CreateSnapshot` fixing the storage's term at `i`; E2 `readyFits` only with a bootstrap log; E3 the model
stage U6m with a reject step and `applyConf` after a rejection; E4 the pre-vote premise dropped (U4
re-proves pre-votes at term 0); E5 `SentMsgShape` without `From ≠ To` for `MsgTransferLeader`; E6 the
decode of empty data a trust-base fact, kept out of kvreconf (its Go does not unmarshal empty data); E7 no
credits in any client-facing spec; E8 `storAppended` defined; E9-E15 the body written out, `clamp_eq`,
the leave's invariant listed, one `msgCredits` law, `al` bound, the stopped specs as one triple each.

## 0. Prerequisites (proof stages of `notes/raft-unified-plan.md`) and one trust-base question

- U0 (in progress): the configuration switches at `appliedSnap`; the model's `applyConf` with a snapshot
  pending; `snapRestore` leaves `cfg`/`cidx`.
- U6m: the protocol's decoder a decision (`CCDecision := apply op | reject`; `entStep` of `reject` keeps the
  state, joint configurations included); one mechanism for passing a rejected entry: `applyConf` and
  `advance` require "no undecided conf entry between" (a rejected one counts as decided), with no
  separate reject step.
- U4: a joiner (empty log, configuration `c0`) in the protocol invariant beside the founders; pre-votes
  granted by a node at term 0 (an empty log) with no `bootedCluster` premise. Scope restriction (F5):
  a newcomer starts at `c0`, not on an empty `ConfState` as etcd's joining member does (`notes/decisions.md`:
  the protocol's invariant forbids a node at a configuration that is not a fold of its log; etcd's server
  proof has no joiners, `notes/membership-plan.md`).
- U5: raft's automatic leave (`appliedTo`'s proposal, its recursion into `Step`); the invariant that a
  committed type-2 entry with empty data is a leave where the configuration is joint (`RaftLeave`, for
  `opsOf`).
- U7: `SentMsgShape` in every cluster; a re-forwarded `MsgTransferLeader` never reaches `send`'s `Panicf`;
  each method takes the receipts it needs from its own steps.
- **Trust base (the user's approval):** raft's leader decodes its own automatic leave (`raft.go:1320`,
  `proto.Unmarshal` of empty bytes into a `ConfChangeV2`); `ccDecodeV2` is opaque and nothing says what it
  gives for `[]`. Proposed: one axiom beside `proto.UnmarshalConfChangeV2.spec`,
  `ccDecodeV2_nil : ccDecodeV2 [] = some ConfChangeV2M.empty` (protobuf's wire format: the empty encoding
  decodes to the message with every field unset; `proto/decode.go`). Without it U5 cannot be proved, and
  automatic leaves stay excluded.

## 1. Pure vocabulary (`NodeApiVocab`, exposed)

```lean
structure LogEntry where term : w64; type : raftpb.EntryType; data : List w8
def LogEntry.isFiller (e) : Prop := e.data = [] ∧ e.type = W32 0
def LogEntry.isConfChange (e) : Prop := e.type = W32 1 ∨ e.type = W32 2

structure Membership where
  voters votersOutgoing learners learnersNext : GSet w64; autoLeave : Bool
def Membership.ids (m) : GSet w64 := m.voters ∪ m.votersOutgoing ∪ m.learners ∪ m.learnersNext
def Membership.isJoint (m) : Prop := m.votersOutgoing ≠ ∅
def Membership.simple (vs) : Membership := ⟨vs, ∅, ∅, ∅, false⟩
/-- well formed: `confchange`'s invariants, a voter, ids nonzero, `ids.size < 2^62`. -/
def (sealed) Membership.Valid (m) : Prop
def (sealed) Membership.applyChange (o : ConfChangeIM) (m) : Option Membership

/-- The decoded change of a conf entry (`EntryConfChange`: a `ConfChange`; `EntryConfChangeV2`: a
`ConfChangeV2`), as `proto.Unmarshal` gives it (`ccDecodeV1`/`ccDecodeV2`). -/
def ccDecode (e : LogEntry) : Option ConfChangeIM
def ConfEntryDecodes (e) : Prop := ∃ o, ccDecode e = some o

/-- The application's decision on a committed conf entry `e` after `pre`, at membership `m`: apply `o`
(`some o`; etcd's rejection is a change with `NodeID` 0, which `confchange` skips) or reject it without
calling `ApplyConfChange` (`none`). A client's explicit `ConfChangeV2{}` and raft's automatic leave have
the same (empty) bytes; the rule decides both. -/
def ConfRule := List LogEntry → Membership → LogEntry → Option ConfChangeIM
/-- (Candidate 11, J1.) The rule only applies changes whose result is `Valid` (`confchange` accepts it and
it stays under `2^62` ids, the protocol's bound: `ccStepB`). -/
def ConfRule.Ok (r) : Prop := ∀ pre m e o, m.Valid → r pre m e = some o → ∃ m', Membership.applyChange o m = some m' ∧ m'.Valid
def ConfRule.clamp (r) : ConfRule := fun pre m e =>
  (r pre m e).filter fun o => ∃ m', Membership.applyChange o m = some m' ∧ m'.Valid   -- (decidable)
/-- `confchange`'s invariants, or the empty membership (a fresh tracker's, a stopped node's `nil`
`ConfState`): what `Restore` accepts. -/
def Membership.WellFormed (m) : Prop := m = Membership.empty ∨ m.Valid
theorem ConfRule.clamp_ok : (ConfRule.clamp r).Ok
theorem ConfRule.clamp_eq : r.Ok → m.Valid → ConfRule.clamp r pre m e = r pre m e
/-- raft's validation as the rule (kvreconf's `validConf`). -/
def ConfRule.validated : ConfRule := ConfRule.clamp fun _ _ e => ccDecode e
theorem ConfRule.validated_ok : ConfRule.validated.Ok

def Membership.fold (r : ConfRule) (c0 : Membership) (l : List LogEntry) : Option Membership
/-- Total for an `Ok` rule from a valid `c0`: the rule's `none` is a rejection, which keeps the
membership, and its `some o` an accepted change (`Ok`). (Decoding is the rule's business:
`ConfRule.validated` rejects an entry that does not decode; every committed conf entry decodes anyway,
`committed_confDecodes`, which the clients' own decoding needs.) -/
theorem fold_total : r.Ok → c0.Valid → ∃ m, Membership.fold r c0 l = some m ∧ m.Valid
theorem fold_nil : Membership.fold r c0 [] = some c0
theorem fold_snoc_normal : ¬ e.isConfChange → Membership.fold r c0 (l ++ [e]) = Membership.fold r c0 l
theorem fold_snoc_conf : e.isConfChange → Membership.fold r c0 l = some m →
    Membership.fold r c0 (l ++ [e]) = match r l m e with
      | none => some m
      | some o => Membership.applyChange o m

def RaftLeave (r c0) (pre) (e) : Prop :=
  e.type = W32 2 ∧ e.data = [] ∧ ∃ m, Membership.fold r c0 pre = some m ∧ m.isJoint ∧ m.autoLeave
def opsOf (r c0) (l : List LogEntry) : List LogEntry          -- drops fillers and raft's leaves
theorem opsOf_noType2 : (∀ e ∈ l, e.type ≠ W32 2) → opsOf r c0 l = l.filter (¬ ·.isFiller)

structure SnapRec where index : Nat; conf : Membership; data : List w8
structure ConfigView where applied : Nat; membership : Membership
```

`Membership.empty : Membership := ⟨∅, ∅, ∅, ∅, false⟩` (K11). Laws of `Membership`: per `confchange`
operation, over the `confchange` specs' models (`applyChange_valid` deleted, K3: false of Go's
`applyChange` at the size bound, and unused): `Restore` of any `cs` with `confStateIs cs m` and
`m.WellFormed` gives `m`; `Simple`/`EnterJoint`/
`LeaveJoint` succeed exactly when `applyChange` of the matching `ConfChangeIM` is `some`, with its result.

## 2. The cluster (`InvNode`, sealed, with laws)

```lean
def (sealed) Cluster : Type 1
def (sealed) Cluster.c0 (γ) : Membership
def (sealed) Cluster.rule (γ) : ConfRule
def (sealed) isCluster (γ) (N) : IProp GF                     -- persistent

theorem cluster_alloc (N c0 rule ps ctxs boot E) :
    c0.Valid → rule.Ok →
    receiptBound GF ≤ 2 ^ 64 - 2 →
    (boot ≠ [] → BootLog ps ctxs boot ∧ c0 = Membership.simple (listToSet ps) ∧ ps.Nodup ∧ W64 0 ∉ ps ∧
                 receiptBound GF + boot.length ≤ 2 ^ 61) →
    (boot = [] → ps = elements c0.ids) →
    ⊢ (if boot = [] then emp else bootMarshal ps ctxs (LogEntry.toEntries boot 0)) ={E}=∗ ∃ γ,
        ⌜γ.c0 = c0 ∧ γ.rule = rule⌝ ∗ isCluster γ N ∗
        ownCommittedOps γ (opsOf rule c0 boot) ∗ ownReadCtxs γ ∅ ∗ ownSnapsMade γ [] ∗ ownProposals γ ∅ ∗
        transferChoice γ ∗ joinAuth γ (listToSet ps) ∗
        (if boot = [] then [∗list] id ∈ ps, nodeRestartBoot γ N id
         else readyFits γ N ∗ [∗list] id ∈ ps, nodeBoot γ N ps ctxs id)
-- (candidate 9, G6: `readyFits` only with a bootstrap log, as today, so kv's adequacy keeps its
-- `n < 2^63` steps; a cluster without one takes its index bound from its storage, as kv does today)

theorem committed_fold : isCluster γ N ∗ isCommittedLogLb γ l ⊢ ⌜∃ m, Membership.fold γ.rule γ.c0 l = some m ∧ m.Valid⌝
theorem committed_confDecodes : isCluster γ N ∗ isCommittedLogLb γ l ⊢ ⌜∀ e ∈ l, e.isConfChange → ConfEntryDecodes e⌝
theorem isCommittedLogLb_length : readyFits γ N ∗ isCommittedLogLb γ l ⊢ ⌜↑l.length < 2 ^ 61⌝
```

`ownCommittedOps γ ops` means `ops = opsOf γ.rule γ.c0` of the committed log (`ownCommittedOps_get_lb :
ownCommittedOps γ ops ⊢ ownCommittedOps γ ops ∗ ∃ l, isCommittedLogLb γ l ∗ ⌜opsOf γ.rule γ.c0 l = ops⌝`,
`ownCommittedOps_lb_prefix` likewise). Kept with their laws: `isCommittedLogLb`, `ownReadCtxs`,
`isReadCtx`, `readCtxAfter`, `readStateOk`, `readCtx_commit(_after)`, `readStateOk_ctx`, `committedAtTerm`,
`deliveredLogLb`, `readyFits` (`readyRest_fits`). Removed: `bootedCluster`, `nodeBoot_booted`,
`nodeDynamicBoot_booted` (their only use was the pre-vote premise, gone).

```lean
-- joining
def (sealed) joinAuth (γ) (U : GSet w64) : IProp GF
def (sealed) nodeJoin (γ) (N) (id : w64) : IProp GF
theorem joinAuth_join : id ∉ U → id ≠ W64 0 → joinAuth γ U ==∗ joinAuth γ ({[id]} ∪ U) ∗ nodeJoin γ N id

-- proposals (normal entries)
def (sealed) ownProposals (γ) (P : GSet (List w8)) : IProp GF
def (sealed) proposalReg (γ) (d : List w8) : IProp GF        -- persistent
theorem proposals_register : ownProposals γ P ==∗ ownProposals γ ({[d]} ∪ P) ∗ proposalReg γ d
theorem proposalReg_elem : ownProposals γ P ∗ proposalReg γ d ⊢ ⌜d ∈ P⌝
theorem proposals_all : ownProposals γ ∅ ==∗ □ ∀ d, proposalReg γ d

-- snapshots
def (sealed) ownSnapsMade (γ) (S : List SnapRec) : IProp GF
def (sealed) snapMade (γ) (s : SnapRec) : IProp GF            -- persistent
def (sealed) noSnapsEver (γ) : IProp GF                        -- persistent
theorem snapMade_elem : ownSnapsMade γ S ∗ snapMade γ s ⊢ ⌜s ∈ S⌝
theorem snapsNone_freeze : ownSnapsMade γ [] ==∗ noSnapsEver γ
theorem noSnapsEver_cert : noSnapsEver γ ∗ snapshotCert γ N k ⊢ False
theorem snapshotCert_make (l : List LogEntry) (i : w64) (t : w64) (d : List w8) (m : Membership) (cs : ConfStateM) :
    l.length = uint.nat i → Option.map LogEntry.term l.getLast? = some t →
    uint.Z i < 2 ^ 61 →                  -- (K2: the certificate carries the `MsgSnap` bound; a cluster with a
                                         -- bootstrap log has it from `readyFits`, kv from its storage)
    Membership.fold γ.rule γ.c0 l = some m → confStateIs cs m →     -- (G7: no-repeat lists follow)

    isCluster γ N ∗ isCommittedLogLb γ l ∗ ownSnapsMade γ S ==∗
      ownSnapsMade γ (S ++ [⟨l.length, m, d⟩]) ∗
      snapshotCert γ N { sid := ⟨t, i⟩, cl := cs.lists, al := m.autoLeave, dat := d }
theorem snapshotCert_made : isCluster γ N ∗ snapshotCert γ N k ⊢
    ∃ l m, isCommittedLogLb γ l ∗ snapMade γ ⟨l.length, m, k.dat⟩ ∗
      ⌜l.length = uint.nat k.sid.index' ∧ Option.map LogEntry.term l.getLast? = some k.sid.term' ∧
        Membership.fold γ.rule γ.c0 l = some m ∧ confStateIs' k.cl m ∧ k.al = m.autoLeave⌝
-- storageCertInv, storageCertLink, storageCert_register, storageCert_read kept

-- a node's applied configuration
def (sealed) nodeConfig (n) (γ) (N) (v : ConfigView) : IProp GF
theorem nodeConfig_fold : isCluster γ N ∗ nodeConfig n γ N v ∗ deliveredLogLb n γ N l ⊢
    ⌜v.applied ≤ l.length → Membership.fold γ.rule γ.c0 (l.take v.applied) = some v.membership⌝
theorem nodeConfig_skip : v.applied ≤ k → k ≤ l.length → NoConfChangeIn l v.applied k →
    nodeConfig n γ N v ∗ deliveredLogLb n γ N l ⊢ nodeConfig n γ N { v with applied := k }
theorem nodeConfig_reject : l[v.applied]? = some e → e.isConfChange →
    γ.rule (l.take v.applied) v.membership e = none →
    nodeConfig n γ N v ∗ deliveredLogLb n γ N l ⊢ nodeConfig n γ N { v with applied := v.applied + 1 }

-- messages
/-- the shapes raft sends (today's `SentMsgOk`, with `MsgTimeoutNow`: a term, no entries, no context;
`MsgTransferLeader`: no term or the sender's, `From` the transferee, possibly equal to `To`; a `MsgSnap`'s
snapshot index below `2^61`, so `stepIn_intro` needs no premise for it: candidate 10, H4). -/
def SentMsgShape (st : MsgSt) : Prop
theorem sentMsg_shape : sentMsg γ N src st ⊢ ⌜SentMsgShape st⌝
theorem sentMsg_prop : st.msg.Type' = MsgProp → sentMsg γ N src st ⊢
    [∗list] e ∈ st.ents, (⌜e.Type' = W32 0⌝ ∗ proposalReg γ e.Data') ∨ ⌜e.Type' ≠ W32 0 ∧ ConfEntryDecodes (LogEntry.ofEntryM e)⌝
/-- what a delivered copy of a message needs: for a `MsgProp`, an update per entry; nothing else. -/
theorem msgCredits_intro : (st.msg.Type' = MsgProp → [∗list] e ∈ st.ents, AU <{ ∃∃ ops, ownCommittedOps γ ops }>
    @ ⊤ \ ↑N, ∅ <{ ∀∀ t, ownCommittedOps γ (ops ++ [⟨t, e.Type', e.Data'⟩]), COMM True }>) ⊢ |==> msgCredits γ N st
def (sealed) transferChoice (γ) : IProp GF
def (sealed) transferAllowed (γ) : IProp GF                   -- persistent
def (sealed) noTransfer (γ) : IProp GF                        -- persistent
theorem transfer_allow : transferChoice γ ==∗ transferAllowed γ
theorem transfer_forgo : transferChoice γ ==∗ noTransfer γ
theorem sentMsg_noTransfer : noTransfer γ ∗ sentMsg γ N src st ⊢ ⌜st.msg.Type' ≠ MsgTimeoutNow ∧ st.msg.Type' ≠ MsgTransferLeader⌝
theorem stepIn_intro : st.msg.To' = id →
    sentMsg γ N src st ∗ msgPtsC ml (DFrac.own 1) (DFrac.own 1) true st ∗ msgCredits γ N st ⊢ |==> stepIn γ N id ml
```

Removed: `isStaticCluster`, `isDynamicCluster`, `snapOk`, `snapshotCert_static`, `snapshotCert_data`,
`cluster_alloc_static`, `dynamicCluster_alloc`, `readySnap_dynamic`, `sentMsg_dynamic_notSnapshot`,
`nodeDynamicBoot`, `CCShrink`, `ccShrink_addVoter`, `ConfChangeDecoder`, `leaderTransferOn/Off`,
`sentMsg_transferOff`, `readCredit(s)`, `readCredits_split`, `readCredit_eq`, `tickCredit`,
`tickCredit_intro/_zero`, `msgCredits_none`/`_snapshot` (into `msgCredits_intro`).

## 3. The specs (one triple per spec file)

Common premises as today, each citing its reason in the file's docstring: `ConfigValid cv`;
`AsyncStorageWrites = false` (asynchronous writes unverified: `issues/raft-async-snapshot-during-apply-divergence.md`);
`ReadOnlyOption = 0` (lease reads assume bounded clock drift); `DisableConfChangeValidation = false`;
`DisableProposalForwarding = false`; `MaxCommittedSizePerReady ≠ 0 ∨ MaxSizePerMsg ≠ 0`
(`issues/nonissues/raft-zero-max-size-per-msg.md`); `Applied = 0` (no restart: durability out of scope);
`MaxInflightMsgs < 2^62`. `PreVote`, `CheckQuorum`, `StepDownOnRemoval` free. No credits.

- `StartNode.spec`: storage empty with an empty initial `ConfState`; `nodeBoot γ N ps ctxs cv.ID'`;
  `storageCertLink γ N si`; post `isNode n γ N id ∗ nodeDriver n γ N (init) ∗ nodeConfig n γ N ⟨0, γ.c0⟩`.
- `RestartNode.spec`: empty log and hard state; initial `ConfState` `cs`, `confStateIs cs γ.c0`;
  `nodeRestartBoot γ N cv.ID' ∨ nodeJoin γ N cv.ID'`; `storageCertLink γ N si`; post as `StartNode`'s.
- `node.wp_readyRecv` (a law): as today, `readySnap`'s snapshot case in every cluster (its `snapshotCert`
  gives `snapshotCert_made`). `readyRest`/`readySnap` sealed, with laws for what clients read of them
  (the unfold list of kv's and the server's proofs, emptied before freezing).
- `node.Advance.spec`: `nodeDriver st`, `st.handling = some (es, L)`, `advReceipt st.storage es L`,
  `nodeConfig n γ N v`, and `L = none → NoConfChangeIn st.delivered v.applied st.delivered.length`; post
  `nodeDriver {handling := none}` ∗ (match `L`: `none` → `nodeConfig v` ∗ the storage floor as today;
  `some l` → `∃ m, nodeConfig ⟨uint.nat l.snap index, m⟩ ∗ ⌜Membership.fold γ.rule γ.c0 (strip l.dlv) =
  some m ∧ confStateIs (l.snap's ConfState) m⌝`).
- `node.ApplyConfChange.spec`: `ownConfChangeI c dq (some o)`, `nodeConfig v`, `deliveredLogLb l`,
  `l[v.applied]? = some e`, `e.isConfChange`, `γ.rule (l.take v.applied) v.membership e = some o'`,
  `applyChange o v.membership = some m'`, `applyChange o' v.membership = some m'`; post
  `ownConfChangeI c dq (some o) ∗ ((∃ cs, csPts csp (DFrac.own 1) cs true ∗ ⌜confStateIs cs m'⌝ ∗
  nodeConfig ⟨v.applied + 1, m'⟩) ∨ (⌜csp = null⌝ ∗ nodeStopped n γ N ∗ nodeConfig v))`.
- `node.Propose.spec`: `isNode`, `nodeCtx ctx cd`, `ownSlice data_sl data DFrac.discard`,
  `proposalReg γ data`, `AU <{ ∃∃ ops, ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅ <{ ∀∀ t, ownCommittedOps γ
  (ops ++ [⟨t, 0, data⟩]), COMM True }>`; post today's errors.
- `node.ProposeConfChange.spec`: today's (no registration).
- `node.Step.spec`: today's (`stepIn γ N id ml`); `node.ReadIndex.spec`: today's without `readCredit`;
  `node.Tick.spec`: `isNode` → unit (no `tickCredit`); `node.TransferLeadership.spec`: `isNode`,
  `transferAllowed γ` → unit; `node.ReportSnapshot`, `node.ReportUnreachable`: today's.
- `node.Campaign.spec`: `isNode`, `nodeCtx` → `nil`, `ErrStopped` or `ctx.Err()`.
- `node.ForgetLeader.spec`: `isNode`, `nodeCtx` → `nil`, `ErrStopped` or `ctx.Err()`.
- `node.Status.spec`: `isNode` → an owned `Status` value.
- `node.Stop.spec`: `isNode`, `nodeLive n γ N 1` → `nodeStopped n γ N` (persistent).
- (Candidate 11, J3.) `nodeLive n γ N q` (fractional), given whole by `StartNode`/`RestartNode`'s post;
  `nodeLive_stopped : nodeLive n γ N q ∗ nodeStopped n γ N ⊢ False`: a client holding a fraction rules out
  every stopped answer (etcd's server: its apply path holds one until its scheduler has stopped, before it
  stops raft, `server.go:823-830`, so its `ApplyConfChange` never answers `nil`); one that stops the node
  concurrently with its other calls (kvreconf) keeps the whole token for `Stop` and handles the answers.
  (K5) Every stopped answer, of every method, comes with `nodeStopped n γ N` in its post (`Propose`'s
  `ErrStopped` included), so a holder of a fraction rules them all out. In etcd it is the raft goroutine
  that calls `Stop` (`onStop`): the apply jobs' fraction comes back through `Scheduler.Stop` and travels
  with the `r.stopped` send (U10). (K9) A stopped node given the running precondition owes only the
  stopped answer: each post is the running post ∨ (the stopped answer ∗ `nodeStopped`), the second
  disjunct refuted by `nodeLive`.
- A stopped node, in each method's one triple (a case split on the input, not a second spec): the
  precondition is `isNode ∗ (the arguments' ownership) ∗ (P ∨ nodeStopped n γ N)`, `P` the running
  precondition above, and the post is the running post when `P` was given, the stopped answer when
  `nodeStopped` was: `Advance`, `Tick`, `ReportSnapshot`, `ReportUnreachable`, `TransferLeadership` → unit;
  `ApplyConfChange` → `null` (the change given back, the view untouched); `Propose`, `ProposeConfChange`,
  `ReadIndex`, `Campaign`, `ForgetLeader` → `ErrStopped` or `ctx.Err()`; `Step` → `nil` for a local message
  type from a non-local sender (`node.go:480-483`), else `ErrStopped` or `ctx.Err()`; `Status` → an owned
  value; a receive from `Ready()` never returns. One spec file, one triple, per function.

## 4. Storage

(Candidate 9, review 8's G1/G2/G5: `storWriter`/`storCommittedAt` withdrawn.) Today's storage specs stay
(the atomic specs over the shared snapshot token, both outcomes, so etcd's server with its two writer
goroutines keeps its proof; a client that is the storage's sole writer keeps the token and so knows the
snapshot index, which rules the error out), with one change to `CreateSnapshot`'s bound:

- (Candidate 10, review 9's H1: a delivered entry is not necessarily appended: in the synchronous mode a
  `Ready` hands out committed entries of its own `Entries`, `issues/raft-committedentries-stable-storage-doc.md`.)
  A persistent storage-level witness:
  ```lean
  /-- (A new field of `class StorageModel`, which every storage instance proves; candidate 11, J4.) The
  storage's entries at or above its first index agree with the committed log `l` (index and term) up to
  `l`'s end: persistent, since a committed prefix never changes and the writer's calls only drop entries
  below a point (`Compact`) or replace the log by a certified snapshot's, which agrees with it (an
  invariant of U8). -/
  def (sealed) storHoldsLb (st : Storage) (l : List LogEntry) : IProp GF          -- persistent
  theorem storHoldsLb_mono : l1 <+: l2 → storHoldsLb st l2 ⊢ storHoldsLb st l1
  /-- After appending a `Ready`'s entries (its `appendReceipt`): the node's delivered log after that
  `Ready` (`nodeDriver`'s `delivered`, which already includes the `Ready`'s committed entries). -/
  theorem appendReceipt_holds : nodeDriver n γ N st' ∗ appendReceipt st'.storage es ⊢
      nodeDriver n γ N st' ∗ appendReceipt st'.storage es ∗ storHoldsLb st'.storage st'.delivered
  ```
  and `Advance`'s post gives `storHoldsLb st.storage st.delivered`. etcd's server and kv pass it through
  their hand-off (`raftAdvancedC`) in place of today's floor token (U10).
- (Candidate 12, K1, option (a): mid-`Ready` snapshots kept.) A hold mark: `storHoldMark st l` (exclusive
  fragment, the storage's record of the longest prefix it has promised to keep), minted with
  `storHoldsLb` by `appendReceipt_holds`; `MemoryStorage.ApplySnapshot.spec` takes, beside today's
  premises, a snapshot index at or above every promised prefix's length, which the snapshot loan supplies
  (a `Ready`'s snapshot is past everything the node delivered before it). So `storHoldsLb` stays
  persistent: no writer call drops a promised entry but `Compact`, which only drops below the snapshot.
- (K4) The `CreateSnapshot` triple above uses today's resources: the token `memSnapTokG γs σt`, the creation
  record `memStorCreated`, the mask `⊤ ∖ ↑memSnapN` (the server's `srvStorTokN` invariant), `memKey`/
  `memSnapRO`; its `al` is the certificate's (`m.autoLeave`).
- `MemoryStorage.CreateSnapshot.spec` (written out; atomic over the snapshot token as today):
  ```lean
  -- (candidate 11, J2: today's two continuations, one per branch, over today's token `memSnapTokG`)
  ∀ st i l (cs : ConfStateM) d,
    uint.nat i = l.length → 0 < l.length →
    {{ isMemStorage st ∗ storHoldsLb st l ∗ csOpt oc (some cs) ∗ ownSlice d data ∗
       snapshotCert γ N { sid := ⟨(l.getLast).term, i⟩, cl := cs.lists, al := cs.AutoLeave', dat := data } ∗
       storageCertLink γ N st ∗
       AU <{ ∃∃ si, memSnapTokG st si }> @ ⊤ ∖ ↑N, ∅
          <{ memSnapTokG st (if uint.Z si < uint.Z i then i else si),
             COMM (⌜uint.Z si < uint.Z i⌝ -∗ Qok) ∧ (⌜uint.Z i ≤ uint.Z si⌝ -∗ Qold) }> }}
      ms.CreateSnapshot(i, cs, d)
    {{ snap err, RET; (⌜err = nil⌝ ∗ Qok ∗ ownSnapS snap _ ⟨⟨(l.getLast).term, i⟩, cs, data⟩)
                     ∨ (⌜err = ErrSnapOutOfDate⌝ ∗ Qold) }}
  ```
  (A sole writer that keeps the token in its own invariant picks `Qold := False` when it knows `si < i`.)
- `MemoryStorage.SetHardState.spec`: today's, made importable (`etc/api/raft.txt`; kvreconf calls it, J5).
- `MemoryStorage.Compact.spec`: today's (the floor token `memFloorTok` bounds the compact index by the
  applied index raft knows; `ErrCompacted` at or below the storage's offset; kvreconf's `Compact(first +
  k)` with `first = offset + 1` is above it).
- A storage wrapper law: a struct embedding a `MemoryStorage` whose `InitialState` answers a fixed `ConfState`
  and whose `Snapshot` answers the embedded one's or `ErrSnapshotTemporarilyUnavailable` is a `Storage`.

## 4b. `confchange` and `tracker` for clients (G4)

An application that validates a change the way raft does (kvreconf's `validConf`) calls
`tracker.MakeProgressTracker`, `confchange.Restore` and `Changer.{Simple,EnterJoint,LeaveJoint}`. Their
specs today are internal (stated over the tracker's fields). New importable specs, over a sealed
`ownTrackerM (trk : ProgressTracker) (m : Option Membership)` (a tracker holding the configuration `m`;
`none` for a fresh one):

- (Candidate 10, H2; 11, J1.) `Membership.applyChange` is Go's `confchange` (no `2^62` cut; the cut is
  in `Valid`, and a rule keeps results `Valid`: `ConfRule.Ok`); `Membership.WellFormed` (§1). A size law:
  `ownCfgPairM cfg prs m ⊢ ⌜(prs's size) = m.ids.size⌝`, so `validConf` checks `len(prs) < 2^62` in Go (§5)
  and its answer is `ConfRule.validated`'s.
- `ownCfgPairM (cfg : tracker.Config) (prs : tracker.ProgressMap) (m)`: a `(Config, ProgressMap)` pair at `m`;
  `ownTrackerM_assemble : ownTrackerM trk _ ∗ ownCfgPairM cfg prs m ⊢ (after `trk.Config = cfg; trk.Progress =
  prs`, the field writes' specs) ownTrackerM trk (some m)` (as kvreconf's `validConf` assembles it).
- `tracker.MakeProgressTracker.apiSpec`: → `ownTrackerM trk none`.
- `confchange.Restore.apiSpec`: `ownTrackerM trk none`, a `ConfState` `cs` with `confStateIs cs m`,
  `m.WellFormed` (a `nil` `ConfState` is the empty membership) → `err = nil ∗ ownCfgPairM cfg prs m`.
- `Changer.Simple/EnterJoint/LeaveJoint.apiSpec`: `ownTrackerM trk (some m)`, `m.WellFormed`, the changes
  as raft's `AsV2` makes them of `o` → `(err = nil ∧ Membership.applyChange o m = some m') ∗ ownCfgPairM cfg
  prs m'` or `err ≠ nil ∧ Membership.applyChange o m = none`.

Their proofs are over today's internal specs (`InvConfchange`, `InvTracker`), stage U11.

## 5. kvreconf's Go changes

- `Storage` with a newcomer flag: `InitialState` gives a newcomer the bootstrap voters, a founder an empty
  `ConfState`; `Replica.cs` starts at the bootstrap voters' `ConfState`.
- (dropped, F4: `applyEntry` keeps unmarshaling every conf entry; the empty-data axiom is needed anyway)
- `validConf` also rejects when the restored-and-changed progress map has `2^62` ids or more (J1: the
  protocol's bound; never reached by kvreconf's at most 9 replicas, but checked so the answer is the rule's).
- `maybeSnapshot`: only past the storage's snapshot index (it is: `index > snapIndex`), so `CreateSnapshot`
  never answers `ErrSnapOutOfDate`; the panic stays, unreachable.
- Done: messages read before they are stepped (`15851e8158`).

## 6. Decisions recorded (to `notes/decisions.md`)

- `γ.rule` a pure function fixed at allocation, a deliberate departure from "TaDa, not HoCAP": the protocol
  fixes the configuration function in its ghost names (`RaftNames.reDyn`), and every node must apply the same
  decision to the same committed entry. etcd's server skips `ApplyConfChange` when `shouldApplyV3` is false (a
  local condition): sound only without restarts, a scope restriction cited in the server's spec.
- Two start-token kinds, one per cluster.
- Scope restriction: a newcomer starts at `c0` (not on an empty `ConfState`, as etcd's joining member):
  the protocol's invariant forbids a node at a configuration that is not a fold of its log, and etcd's
  server proof has no joiners.
- The axiom `ccDecodeV2_nil` (if approved) is used by raft's own proof (U5: its leader decodes its
  automatic leave), so every result over raft rests on it, kv's and the server's included.
- Credits gone from the API: raft's proofs take the receipts they need.
