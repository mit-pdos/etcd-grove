# Review of the unified node-API candidate 9, round 9

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-7.md`, titled "candidate 9", one
  text. It is a design and nothing of it is implemented, so no finding can be stale against `HEAD` (`231b666893`).
- **Compared with**: today's API at `eb59bb8d1b`:
  - `interface/Proof/go_etcd_io/raft/v3/{InvNode,ApiVocab,NodeApiVocab,InvMemstorage,MemstorageAU}.txt`;
  - `interface/Spec/go_etcd_io/raft/v3/{MemoryStorage__*,node__Advance,node__ProposeConfChange,NewMemoryStorage}.txt`;
  - `etc/api/raft.txt`;
  - `Proof/go_etcd_io/raft/v3/{InvApi,InvApiDyn,InvMemstorage,Protocol/CfgOverlap}.lean`.
  - Also `notes/raft-unified-plan.md` and `notes/decisions.md` in the worktree, with the other agent's
    uncommitted edits.
- **Go**:
  - raft a2 (`.lake/raft-fork`, `565c2bd`): `storage.go`, `log.go`, `rawnode.go`, `raft.go`, `node.go`,
    `raftpb/confchange.go`, `confchange/{confchange,restore}.go`, `tracker/tracker.go`;
  - kvreconf (`examples/kvreconf/{kv,cluster,reconf}.go`);
  - etcd's server (`~/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261027220749-a20f6760ff43/etcdserver/{raft,server}.go`).
- **Clients' proofs**: kv (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/{KV__run,Defs,KVStorageInstance,Cluster,deliverable}.lean`)
  and the server (`etcdserver/{SnapTake,InvRaftNode}.lean`), at `eb59bb8d1b`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md` (the worktree has no `spec/` skill).
- **Not run**: lake build, lean-check, Go tests.

Each finding is marked **[spec]** (a defect of the specification) or **[obligation]** (a proof obligation),
and says whether §0 or `notes/raft-unified-plan.md` carries it.

## Summary

Candidate 9 fixes review 8's G2, G3, G5, G6, G7, G10 and G12, and the plan fixes G11. G4 and G9 are partly
fixed. G8 and G13 are not addressed.

**G1's replacement is unsound.** `CreateSnapshot` is now bounded by the node's delivered log, justified by "a
delivered entry is committed and was appended before it was handed out". That justification is false here.
With `AsyncStorageWrites = false`, raft hands out committed entries from the unstable log, in the same `Ready`
as their `Entries`, before the client has appended them. A client holding `deliveredLogLb` of that `Ready` can
call `CreateSnapshot` past the storage's last index, and `storage.go:250-252` panics. The term link the bound
is meant to carry also has no source on the storage's side, and the triple is still not written out.

The new §4b `confchange`/`tracker` specs are needed, but they have three gaps:
- they claim an iff that the model's `2^62` bound breaks;
- they cover only `Valid` memberships, which shuts out kvreconf's `validConf(nil, …)` after a stopped
  `ApplyConfChange`;
- they give no vocabulary for the tracker that `validConf` builds by field assignment.

**Tier 1 (1)**: H1. **Tier 2 (2)**: H2, H3. **Tier 3 (4)**: H4-H7.
**Go defects**: no bug. One possible documentation issue, H7 (`node.go:89-91`). It is not filed (read-only
review), and no existing `issues/` entry covers it.

---

## Review 8's findings: fixed?

| review 8 | candidate 9 | status |
|---|---|---|
| G1 `storCommittedAt_of` false/unusable | withdrawn; `CreateSnapshot` bounded by `deliveredLogLb` | **Not fixed**: the replacement is unsound (H1) |
| G2 server's two writers | today's atomic specs kept, both outcomes; the sole writer uses the token (`MemstorageAU.spec_tok_of`, importable, `etc/api/raft.txt:64`) | **Fixed** for the storage half. The server's certificate path is a new obligation (H3) |
| G3 off by one | `isCommittedLogLb_length … < 2^61` | **Fixed**: `isCommittedLogLb` gives `l.length < receiptBound + bootLen` (`InvApi.lean:134-136`), and `cluster_alloc` gives `receiptBound + boot.length ≤ 2^61` |
| G4 `validConf`'s callees | §4b `ownTrackerM` specs, plan U11 | **Partly**: H2 |
| G5 `Compact` | today's `Compact.spec` (`memFloorTok`) kept | **Fixed** (kvreconf's `Compact(first + k)`: see the table below) |
| G6 kv's adequacy | `readyFits` and the `2^61` bound only with a bootstrap log; `≤ 2^64-2` otherwise | **Fixed**: kv (`boot = []`, Go-checked bounds, `KV__run.lean:210,414`, `deliverable.lean:120`) keeps `n < 2^63` |
| G7 `NoDupLists` | dropped | **Fixed** |
| G8 `stepIn_intro`'s `MsgSnap` premise derivable | unchanged | **Not addressed** (H4) |
| G9 newcomer restriction | in §6 | **Partly**: §0 still cites a `notes/decisions.md` entry that does not exist yet (grep finds none in the worktree's file, uncommitted edits included) (H6) |
| G10 `fold_snoc_conf`, `nodeConfig_reject` | both written; `nodeConfig_reject` is `⊢` | **Fixed**: `fold_total` follows from `fold_snoc_conf`, `Ok` and `applyChange_valid` |
| G11 plan U11 term budget | plan U11: "no bound on ticks or campaigns: raft takes its own time receipts" | **Fixed** (plan) |
| G12 the axiom's reach | §6 says every result over raft rests on it | **Fixed**. The need is confirmed: `appliedTo` proposes `confChangeToMsg(nil)` (`raft.go:742-748`), `MarshalConfChange(nil)` gives `nil` data without calling `proto.Marshal` (`raftpb/confchange.go:40-45`), and `stepLeader` unmarshals it (`raft.go:1327-1337`). So `MarshalConfChangeV2.spec` cannot replace the axiom |
| G13 nits | none applied | **Not addressed** (H6) |

---

## Findings, ranked

### Tier 1

#### H1. [spec] `CreateSnapshot` bounded by the delivered log is unsound, and its term link has no source

**Principles**: *Sound* (no panic under the precondition); *every premise has a source*; *Local*.

**Evidence: unsound.** §4 replaces `i ≤ x` (the floor `memFloorTok`) by `deliveredLogLb n γ N l` with
`uint.nat i = l.length`, and justifies it with "a delivered entry is committed and was appended before it was
handed out". In this configuration that is false:
- The premise `AsyncStorageWrites = false` makes `applyUnstableEntries()` true (`rawnode.go:443-444`).
- `Ready.CommittedEntries` is then `nextCommittedEnts(true)` (`rawnode.go:144`), bounded by `committed` and
  not by the stable index (`log.go:267-272`; `log.go:216-219`: "Entries can be committed even when the local
  raft instance has not durably appended them"). A follower that receives a `MsgApp` whose commit index covers
  the new entries gets them in `Entries` and in `CommittedEntries` of the same `Ready`.
- At the receive, the driver's `delivered` is already `st.delivered ++ ce` (`node.wp_readyRecv`, `InvNode.txt`).
  `nodeDriver_deliveredLogLb` then gives `deliveredLogLb` of it, before the client has called `Append`.
- With no snapshot yet (`ss.index = 0 < i`), `CreateSnapshot(i, …)` reaches `i > ms.lastIndex()` and
  `Panicf` (`storage.go:250-252`).
- etcd's server documents exactly this hazard and waits for it: "applied index might be greater than the last
  index in raft storage, since the raft routine might be slower" (`server.go:991-995`, `<-apply.notifyc`).

**Evidence: the term has no source.**
- Today's triple asks for `□ ∀ t, memStorCert γs (snapTrip (memSnapCreated σt i t oc bs) …)`, a certificate
  at every term (`MemoryStorage__CreateSnapshot.txt`). The reason is that the atomic state `memSnapTokG γs σt`
  holds only `snapPart σ` and `prev`, never the entries (`InvMemstorage.lean:538-540`, `938-939`). The client
  cannot know which term the storage has at `i`.
- `snapshotCert_make` gives the certificate at one term `t`, the last of `l`. So the triple must change, so
  that the created snapshot's term is `t`. The proof then needs a fact tying the storage's entries to the node's
  log, which today's storage vocabulary does not state.
- §4 says "raft's storage invariant gives" it, without naming the predicate; that is uncertain, not checked.
  The triple is still not written out, as review 8 asked.

**Evidence: other gaps in the same section.**
- `nodeStorage n st` is said to come "from `StartNode`/`RestartNode`'s post", but §3's posts do not list it, and
  §2 does not declare it.
- The triple is over `ms γs`, while `nodeStorage`/`deliveredLogLb` are over `st : Storage` and the node. Nothing
  says how they meet (as kv's `kvStorRec`/`kvStorIface` do, `Defs.lean:160-171`).
- Today's AU asks for the certificate in both outcomes, at the conf state `memSnapCreated` uses: with `cs = nil`
  that is the storage's previous one. The client can certify only `cs.lists` with `confStateIs cs m`. So the
  triple must take `oc = some cs`, or ask for the certificate only in the success branch.
- Locality: a `MemoryStorage` method's spec would take the node's predicates, not the storage's footprint.

**Callers**:
- kvreconf: its in-loop `maybeSnapshot` comes after `Append` (`kv.go:343`, `347-350`), so it is sound under the
  fix below; under the candidate as stated it is "covered" only by an unsound spec;
- kv (`KV__run.lean:612`);
- the server (`SnapTake.lean:137`).

**Restatement**: keep the bound in the storage's vocabulary and give it two sources:
- A persistent `memStorHolds ms γs l`: the storage's entries at indices above its snapshot index and up to
  `|l|` are `l`'s, with their terms. It can be built like `memFloorTok`, from a lower bound of `γs.hist`.
- Its sources:
  - `Advance`'s post, where today's floor is (`storFloor … ∗ ⌜|delivered| ≤ x⌝`), extended with the
    entries;
  - a law over the append receipt: `appendReceipt st es ∗ nodeDriver n γ N st` (`st.handling = some (es,
    none)`) `⊢ … ∗ memStorHolds … st.delivered`. After `Append(rd.Entries)` the `Ready`'s committed entries are
    in the storage.
- `CreateSnapshot.spec`, written out, then takes:
  - `memStorHolds ms γs l` with `uint.nat i ≤ l.length`;
  - `oc = some cs`;
  - inside the AU, `⌜σt.ss.index < i → σt.prev.index ≤ i⌝` (today's) and
    `memStorCert γs (snapTrip ⟨t, i⟩ cs.lists …)` with `t` the term of `l` at `i`.
- Its post fixes the created snapshot's term to `t`. `spec_tok_of` follows.
- The node/storage link (that raft's committed entries in the storage are the delivered ones) is then an
  obligation of the law's proof, U8. It is not a premise of a storage spec.

### Tier 2

#### H2. [spec] §4b's `confchange`/`tracker` specs: false at the size bound, `Valid`-only, and no shape for what `validConf` builds

**Principles**: *Sound*; *Complete* (every caller, every path); *the vocabulary is part of the spec*.

**Evidence: (a) the iff is false at the boundary.**
- `Membership.applyChange` is `memApply` (`InvApiDyn.lean:73-74`), which is `ccStepB` (`Protocol/CfgOverlap.lean:224-225`).
  `ccStepB` returns `none` when the result has `≥ 2^62` ids.
- `Changer.{Simple,EnterJoint,LeaveJoint}` have no such check (`confchange/confchange.go:51-150`).
- So "`err = nil ∧ applyChange o m = some m'`, or `err ≠ nil ∧ applyChange o m = none`" is false for a change that
  grows the ids past `2^62` (a long `Changes` slice). The `ownSlice` length is only `< 2^63`, so the bound is not
  derivable.
- The same gap makes `ConfRule.validated` reject an entry that Go's `validConf` accepts. kvreconf would then
  call `ApplyConfChange` on an entry whose rule value is `none`, and the spec's premise `γ.rule … = some o'` fails.

**Evidence: (b) `Valid`-only excludes a reachable path.**
- After a stopped `ApplyConfChange` returns `nil`, kvreconf sets `r.cs = nil` (`kv.go:470-472`). The same
  `Ready`'s later conf entries reach `validConf(nil, …)`, which restores `&pb.ConfState{}` (`kv.go:220-222`), the
  empty membership.
- The empty membership is not `Valid` ("a voter"). §4b's `Restore` and `Changer` specs require `m.Valid`. So the
  stopped path is outside them, although review 8 listed it as not excluded.
- Only safety is needed there (no panic, owned results): whatever `validConf` answers, `ApplyConfChange` takes
  the `nodeStopped` case.

**Evidence: (c) the shape.**
- `validConf` builds a `Changer{Tracker: MakeProgressTracker(1,0), LastIndex: 1}` value and passes it to
  `Restore` (`restore.go`: `Restore(chg Changer, cs)`).
- It then assigns `trk.Config = cfg; trk.Progress = prs` into a second fresh tracker (`kv.go:223-229`) and
  calls methods on a `Changer` value.
- §4b states `Restore` over "`ownTrackerM trk none`", with a post "`ownTrackerM` of the returned config and
  progress map". `ownTrackerM` takes a tracker, not a `(Config, ProgressMap)` pair. No predicate is given for
  the pair, and no law assembles a tracker from a fresh one and a pair.
- `ownTrackerM` is sealed, so the client cannot do the field writes itself.

**Caller**: kvreconf's `validConf` (`kv.go:219-240`). Plan U11 carries the proof, not the spec shape.

**Restatement**:
- An `ownConfigM cfg prs m` for `Restore`'s and the `Changer`s' results.
- The law `ownTrackerM trk none ∗ ownConfigM cfg prs m ⊢ ownTrackerM {trk with Config := cfg, Progress := prs} m`.
- The specs over `Changer` values (`ownTrackerM c.Tracker m`).
- Total specs at any `m` reached from a `ConfState` with no duplicate lists, the empty one included, with the
  post:
  - `err = nil → applyChange o m = some m' ∨ (ids of m and o).size ≥ 2^62`;
  - `err ≠ nil → applyChange o m = none`.
- kvreconf refutes the size disjunct from its own invariant on the proposals it makes (`reconf.go`: at most
  `maxReplicas` ids).

#### H3. [obligation; neither §0 nor the plan carries it] etcd's server must re-certify its snapshots

**Principles**: *Complete* (all callers); *One general spec*.

**Evidence**:
- §4 says today's storage specs are kept "so etcd's server … keeps its proof". That holds only for the storage
  half.
- The server's `CreateSnapshot.wp_reg` certifies each created snapshot at every term through a free registry
  (`memCertReg`). Its file header says this is "free in raft's no-snapshot mode … L3 replaces it by raft's
  `memCertInv`" (`SnapTake.lean:4-10`, `55-56`, `127-131`).
- In one mode with snapshots, raft reads the storage's certificates (`storageCertLink`). So the server must
  make each certificate with `snapshotCert_make`. That needs:
  - `ownSnapsMade γ S` in an invariant of the server;
  - `isCommittedLogLb` of length `appliedi`;
  - the fold;
  - `confStateIs ep.confState m`.
- `ep.confState` is set by `ApplyConfChange` only when `shouldApplyV3` (`server.go:2051-2053`), and may be
  `nil` after a stopped `ApplyConfChange`. `CreateSnapshot(ep.appliedi, ep.confState, nil)` (`server.go:2131`)
  with `nil` needs H1's `oc = some` or a success-only certificate.
- Plan U10 says only "etcd's server … over the unified API".

**Restatement**: add to U10, and to §0, the server's snapshot certification over `snapshotCert_make`, with the
`ep.confState`/`shouldApplyV3` scope restriction §6 already records. Whether a stopped server can reach
`snapshot` with `ep.confState = nil` is uncertain; I did not trace it.

### Tier 3

- **H4. [spec] `stepIn_intro`'s `MsgSnap` index premise (G8, not addressed).**
  - With a bootstrap log it is derivable: `sentMsg_snapshot`, then `snapshotCert_made`, then
    `isCommittedLogLb_length`. kvreconf would pay that glue.
  - Without one, nothing in the API gives it. kv checks it in Go (`deliverable.lean:110-121`), and a client
    with no such check cannot.
  - Raft sends a snapshot only from its storage (`< 2^61` by `memstorageInv`'s `Hpb`, `InvMemstorage.txt:147-151`)
    or one it received under the same premise. So `SentMsgShape` could carry `MsgSnap → Index < 2^61`, and the
    premise would go. Uncertain for a general `Storage`.
- **H5. [obligation, plan] The plan still describes candidate 8's storage.** "The spec" says
  "`CreateSnapshot` … before `Advance` (`storWriter`)", and U8 says "The writer's view `storWriter` and
  `storCommittedAt`". Both are withdrawn. U8 should become H1's witness and laws, and U11 should name §4b's
  `ownConfigM`/assembly law (H2).
- **H6. [spec, nits]**
  - G13's three nits remain: §1's "(F9)" label; the stopped `Step` should say that a `nil` message is
    excluded by the argument's ownership; `Propose` with `data = []` is a filler whose update never fires.
  - §0 cites a `notes/decisions.md` entry that does not exist yet (G9 residual; §6 lists it "to
    `notes/decisions.md`").
  - The header's "Reviews: …-{1..7}" should include 8.
  - `nodeStorage` is missing from §3's posts (H1).
- **H7. [Go documentation, possible issue; not filed]**
  - `Ready.CommittedEntries`' doc says "These have previously been appended to stable storage"
    (`node.go:89-91`). With `AsyncStorageWrites = false`, raft returns committed entries that are in the
    same `Ready`'s `Entries`, not yet appended (H1's evidence).
  - The candidate's §4 justification repeats the doc's claim.
  - It is benign for an application that appends before it applies, as raft's README asks, but it is a
    precondition of `CreateSnapshot` that the API does not state.
  - Worth an `issues/` entry (`upstream: unchecked`). Nothing in `issues/` covers it. I did not file it
    (read-only).

## What is good

- **The storage section went back to the specs that work.**
  - The atomic `CreateSnapshot`/`Compact` with both outcomes keep the server's two-writer proof
    (`MemstorageAU.wp_shared`).
  - A sole writer takes `spec_tok_of`, so kvreconf's use is an instance of the general spec, not a second
    one (G2).
  - `Compact` keeps `memFloorTok`, which names the applied bound (G5).
- **Bounds**:
  - `isCommittedLogLb_length < 2^61` is true (G3).
  - `readyFits` is tied to the bootstrap log, so kv's adequacy keeps `n < 2^63` (G6).
- **The fold is fully stated** (G10):
  - `fold_nil`/`fold_snoc_normal`/`fold_snoc_conf` determine `fold`, and `fold_total` follows;
  - `nodeConfig_reject` is a plain entailment, consistent with U6m's "a rejected entry is decided";
  - `ApplyConfChange`'s premise `γ.rule (l.take v.applied) v.membership e = some o'` matches
    `fold_snoc_conf`'s pre/membership.
- **§4b exists.** `validConf` (`kv.go:219-240`) now has callee specs in the API to aim at (G4), and
  `ConfChangeV2.{LeaveJoint,EnterJoint,GetChanges}` already have raftpb specs
  (`interface/Spec/go_etcd_io/raft/v3/raftpb/`).
- **The trust base is honest**: §6 says the axiom reaches every result over raft (G12). The axiom is sound
  against protobuf's wire format (the empty encoding is the default message), and it is needed (table above).
- **The rest is as review 8 found it**: the start kinds and joiners (StartNode for founders with peers,
  RestartNode for newcomers: `cluster.go:125-136`, `163-176`); `RaftLeave`/`opsOf`; no credits; one stopped
  triple per function; `ownSnapsMade` TaDa style.

## kvreconf's Go still excluded

| behaviour | where | excluded by | kind |
|---|---|---|---|
| `CreateSnapshot` in the apply loop and after `Advance` | `kv.go:349`, `355`, `366-379` | H1: the candidate's spec is unsound. Under H1's restatement the in-loop call is covered by the append receipt (it follows `Append`, `kv.go:343`), and the post-`Advance` call by `Advance`'s witness | spec |
| `validConf(nil, …)` after a stopped `ApplyConfChange` | `kv.go:220-222`, `470-472` | H2(b) | spec |
| `validConf`'s tracker assembly; the `2^62` boundary | `kv.go:223-229`; `confchange.go` | H2(a)(c) | spec (+ plan U11) |
| a newcomer on an empty `ConfState` (today's `Storage` has no `InitialState`) | `kv.go:244-246`, `cluster.go:174-175` | §5's Go change; scope restriction in §6 | Go change |
| unmarshalling raft's automatic leave | `kv.go:443-447` | the axiom's approval | trust base |
| a joiner at `c0`; pre-votes at term 0 | `cluster.go:163-176` | U4 (§0, plan) | obligation |
| `ApplyConfChange` after a rejected entry; conf changes applied while a snapshot is pending | `kv.go:461-472` | U6m, U0/U3 (§0, plan; `notes/decisions.md` "Stage U0", "Not done") | obligation |
| raft's automatic leave | `raft.go:742-760` | U5 (§0, plan) | obligation |
| a forwarded `MsgTransferLeader`; `MsgTimeoutNow` | `reconf.go:104-106` | U7 (§0, plan) | obligation |

**Not excluded** (checked):
- `maybeCompact`:
  - after an `Advance` without a snapshot, `r.index ≤` the floor;
  - after a snapshot `Advance`, `hi = snapIndex < first` returns before `Compact` (`kv.go:390-400`);
  - `ci ≤ ss.index` from the sole writer's token.
- `ApplySnapshot`'s ignored error (`kv.go:336`): the client's own invariant refutes it (its snapshots are at or
  below the delivered log, and `readySnap` puts the incoming one past it).
- The `Snapshot` wrapper's `ErrSnapshotTemporarilyUnavailable`; `ReadIndex`, `Campaign`, `ForgetLeader`,
  `Status().Lead`, `TransferLeadership`; retried and duplicated `MsgProp` (`proposalReg`, `msgCredits_intro`).
- The options: `RandomOptions` keeps `MaxCommittedSizePerReady ≠ 0 ∨ MaxSizePerMsg ≠ 0`
  (`cluster.go:90-104`), and the rest are free or defaults.

## Ranking (most in need of revision first)

1. **`CreateSnapshot`** (H1): unsound as stated. Use a storage-side witness from the append receipt and
   `Advance`, and write the triple out.
2. **§4b** (H2): total specs, a vocabulary for the `(Config, ProgressMap)` pair, and the size bound stated.
3. **The server's certificates** (H3): an obligation to put in §0 and U10.
4. **Derivable or unsourced `MsgSnap` bound** (H4).
5. **Records** (H5, H6), and the doc issue to file (H7).

## Uncertain

1. H1's restatement: that raft's internal invariant can prove "after `Append(rd.Entries)` the `Ready`'s
   committed entries are in the storage with their terms" (not checked in `InvStorage`/`InvRawnode`).
2. H3: whether a stopped server reaches `snapshot` with `ep.confState = nil`.
3. H4: whether every `Storage` raft is given bounds its snapshot index below `2^61` (true of `MemoryStorage`).
4. H2(a): whether the user wants the `2^62` slack in `ConfRule.validated` itself (clamp at Go's behavior)
   rather than in a disjunct of the `Changer` specs.
