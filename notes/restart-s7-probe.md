# Restart S7.1: probe report (CP-b, 2026-11-14, for etcd-grove-81)

The probes P1-P4 of `notes/restart-s7-scope.md` §6 (S7.1), run at branch `restart-s7` after S7.0
(`examples/etcd/restart1`, its counting test, its translation). **No statement changed.** The Lean
probes are in `Scratch/S7Probe.lean` (untracked, as `Scratch/S56Probe.lean`), checked with
`etc/lean-check.py`: `probe_P1_split`, `probe_P2_static`, `probe_P3_start`, `probe_P4_mint`,
`probe_P4_rdctx`. Abbreviations as in the Scope (`E/`, `SE/`, `X/`, `SX/`).

**Summary.**

| Probe | Question | Answer | Consequence |
|---|---|---|---|
| P1 | in-process `Put`/`Range`, readers back before `HardStop` | **yes**: no `Serve` split, no `GracefulStop` | three local lemmas (§P1); the Scope's P1 risk does not happen |
| P2 | single voter: no message sent, from raft's API | **no**: the server's cluster is in raft's dynamic mode, where a `MsgSnap`'s protocol clause says only `dst ≠ src` | a proved raft law is needed (proposal P2-a): a raft interface diff, a hard stop |
| P3 | `Start.spec` at a restart | **already applies**: `specR` builds at `ai₀ = W64 0` | G1 is not a spec change; S7.2 is an etcdstart proof (2-3 d, no Freeze) |
| P4 | `BuildServer.specRestart`'s premises from `HardStop`'s image; threads | the image and the fresh names are there; **the cluster's persistent facts are not** in its precondition | add them (form; proposal P4-a); threads: no change |

No new world assumption and no new trusted text was found. P2's proposal adds a proved raft law, not
an axiom, but it changes raft's exported vocabulary.

## P1. In-process `Put`/`Range`, and the stop's readers

**What `Put.spec` takes** (`SE/EtcdServer__Put.lean`), and where `restart1` gets it:
- `isServerReqM false s E ρ` = `isServerReq`: `memberUp`'s.
- `srvLeadTimeReader s ∗ E.RD`: borrowed from the revocation's inner pool, which is in
  `srvServeStock`'s persistent `srvRevokeBuilt` (`srvRevokeBuilt_innerBorrow`, with `£ 1` and
  level 2 of the main thread's token, `threadTokFrom_succ`), and given back after the call
  (`srvRevokeInnerLoan_giveBack`). This is how a gRPC run gets them.
- `idCred ρ.ids 1`: pure (`receiptBound GF ≤ 2^48`).
- `putPermitM false … op Q` (`kvOpAu1`, the update fired at most once) and `srvApi.kvLogLb`: from
  the example's KV invariant, as `restart3`'s `put` gets them through the client (`putGetInv_st`).
- `context.isContext`, `context.libCtxOk`, `trace.spanCtxOk` of `context.WithTimeout(Background(), …)`:
  `context.WithTimeoutBackground.spec` gives `isContext` and `ctxValueFrom background ctx'`, from which
  `context.libCtxOk_bgFrom` and the chain laws (`trace.spanCtxOkC_from`, `trace.spanCtxOk_of_spanCtxOkC`)
  give the other two.
- `txn.putRequestIs r op`: **no law builds it** from an allocated `&etcdserverpb.PutRequest{…}` (the
  server's requests arrive decoded by gRPC's trusted model). A local lemma: the fields made
  read-only and the size cache's invariant allocated (est. 0.5 d). The same for
  `txn.rangeRequestIs`.

**The stop.** The borrow takes nothing from `srvServeStock`'s raw stock (`srvRevokePoolN` store
tokens with `bemu` slots), so `srvStopReaders_intro` still collects every token after the `Put`s.
`probe_P1_split` (checked) gives, from `memberUp`, at **one** environment `E`: the request and read
views, `srvRevokeBuilt`, `srvGoRes`, `srvStopRight` and `srvStopReaders`. `memberUp_stop` gives the
request view and the stop right at two separate existential environments and drops
`srvRevokeBuilt`, so `restart1` needs this joint form: a new etcdstart law (a form change, beside
`memberUp_stop`). `HardStop`'s other premises: `srvBootApplied` from the `AppliedIndex()` wait (as
`restart3`'s `stop`), `srvStop.scope` (auth off, `AutoCompactionRetention = 0`, so no compaction
mode), `srvDataDir` from `BuildServer`'s post.

**`Range` after the restart** (`SE/EtcdServer__Range.lean`), at the restarted member, which is never
stopped: `srvRdCall` = one store token (split off the second incarnation's raw stock), a `lgMu` slot
(`memberUp`'s), `committedAtLeast γr 0`, a read-loop slot (`memberReadN ≥ 1`), `E.RD` (borrowed from
the inner pool, never given back); `srvAuthLb` and `authPubLbM .off` are trivial at auth off;
`kvDep` at the restarted names reads the same KV invariant (`kvInv_restartNames`).
**One gap: `traceutil.ctxTraceIs ctx none`** for the context `WithTimeout(Background(), …)` returns.
Only a `*cancelCtx` law exists (`traceutil.ctxTraceIs_cancelCtx_background`, which unfolds Perennial's
context code). A law from `ctxValueFrom background ctx'` (what `WithTimeoutBackground.spec` gives,
the form `libCtxOk_bgFrom` uses) is a local lemma (`traceutil.ctxTraceIs_bgFrom`, est. 0.5 d; no
trusted text). The driver's
`for s.Leader() == 0` wait (added in S7.0, below) uses `EtcdServer.Leader`, proved and linked.

**Proposal P1.** Accept the in-process route as planned. Three local lemmas in S7.5: the joint split
(`probe_P1_split`, made an etcdstart law), `putRequestIs`/`rangeRequestIs` from an allocated request,
the trace law from `ctxValueFrom`. Est. +1-1.5 d over the Scope's G5.

## P2. The single-voter "no `MsgSnap`" fact (G2)

`srvRestartRows γ id A σ` asks a ghost update to `rnSnapTermAbove γn ∗ srvWinPend s γr γn`. For one
member both would follow from "this cluster never sends a `MsgSnap`".

**What raft's API gives.** A `Ready`'s message carries `isRaftMsg`, whose protocol abstraction of a
`MsgSnap` is `isMessage γ (absSnap …)`. Its `.snap` clause (`Proof/go_etcd_io/raft/v3/Protocol/
GhostState.lean:225-239`) ends in `⌜m.dst ≠ m.src ∧ ∀ T, γ.reTracked = some T → m.src ∈ T ∧ m.dst ∈ T⌝`.
In a cluster with a tracked bound of one member, that excludes every `MsgSnap`: `probe_P2_static`
(checked). **But the server's cluster is in raft's dynamic mode** (`cluster_alloc` in
`E/NewServerAlloc.lean:231`, `RNMode.dyn`), where `reTracked = none` (`RaftNames.reTracked_of_dyn`):
the clause says only `dst ≠ src`, and nothing says the destination is a member. The leader
certificate in the clause does not help either: the stopped incarnation, the only member, was leader
at the restored term `t0`, so a `MsgSnap` at `t0` is not excluded by it. So neither row follows from
the API for one member. (`srv_confAt_eq_simple` does give a static configuration for every committed
log: the gap is only the message's destination.)

**Proposals** (a hard stop: each changes raft's API or proves a new raft law):
- **P2-a (recommended):** a proved raft law in dynamic mode: the `.snap` clause also says that `src`
  and `dst` are voters or learners of the configuration of the sender's log (`maybeSendSnapshot`
  sends only to a peer of the progress tracker, whose ids are the configuration's). On the server
  side, `srvRestartRows_single`: with every configuration the boot one (`srv_confAt_eq_simple`, to be
  checked for the leader's uncommitted suffix: `srvRule` on proposed conf entries) and the boot
  configuration `{id}`, `src = dst = id` contradicts `dst ≠ src`, so both rows hold vacuously. Raft-side:
  the protocol clause, `maybeSendSnapshot`'s step lemma, the receivers that destructure the clause; an
  `interface/` diff of raft's API. Est. 1.5-2.5 wk (the Scope's G2 said 1-2 wk "plus maybe a raft API
  law"; it is needed).
- P2-b: prove `rnSnapTermAbove` in general (R2d'b's target, a raft-struct invariant and a `StartNode`
  post change, 5-8 d est.). It does not give `srvWinPend` (its `sentMsg` is keyed by member id across
  incarnations), so it does not close G2 alone; it is R2s-A's work, not S7's.
- Not acceptable: carrying `srvRestartRows` into `etcd_restart1_safe` (the strong-theorems goal; the
  Scope's §1 says it must not appear).

## P3. `Start.spec` at a restart (G1)

`NewServer.specR`'s post builds the restart at `ai₀ = c₀ = W64 0` with the apply state
`restartKV ρ.rd.kv A`: the restart point is the backend log `γn.a0` and the ghost index
`ai₀ + |γn.a0|` (`srvBuiltRestartR`, restart S4/S6). So `Start.spec`'s `ai₀ = W64 0` holds, and its
construction premise `isServerBuiltC .off` is `srvBuiltR_C` of the post's `srvBuiltR` and the slot
from the post's `srvStop.keep` (`srvStop.slot_intro`, `Er.ST = srvTrStopK γk` by `rfl`); `acLessor .off`
is `True`. `probe_P3_start` (checked). The Scope's G1 premise ("`Start.spec` takes `ai₀ = W64 0`; a
restarted member's apply thread starts at `i`") predates S6's choice of the restart point.

**What remains is on the etcdstart side.** `memberBuiltR` (DRAFT) is `∃ ai₀ at₀ c₀ x₀, memberBuilt …`,
and `memberBuilt` holds the first start's `isServerBuilt` (with `γn.a0 = []`), so no restart can give
it. **Proposal P3:** `memberBuiltR`'s body becomes `specR`'s post shape (`srvBuiltR` at `W64 0` and
`restartKV`, `srvStop.keep`, the serving stocks, the lessor's part), a form fix of a DRAFT definition;
`wp_Start_builtR` is proved from `Start.spec` as `wp_Start_built` is, and `Start_builtR_spec` is
deleted. No linked spec changes, so no Freeze. Est. 2-3 d (the Scope's S7.2 said 1-1.5 wk with a
Freeze). One check to make in it: the restarted lessor's part (`lease.srvInvAt false srv E m (recMap
…)`, from the image's lease bucket) against `memberUp`'s `srvLeaseRd s E .none`; `restart1` grants
no lease.

## P4. `BuildServer.specRestart`'s premises (G3), the thread budget (G7)

**From `HardStop`'s image.** `memberRestartRes name {} γn γ ρo id` is `srvDiskImage` alone (no peer
or client address: `restart1` serves neither), built from `HardStop`'s post with no extra resource.
`specR` wants the image at explicit witnesses (`srvDiskImageAt`): the proof destructures the
existential. The image already holds `nodeVacant` and `raftState`.

**The fresh per-incarnation names** `specR` takes are allocatable inside `BuildServer`'s proof:
`idShare`, `idWaitTok`, `idKeyFactAt` from `idIncarnation_alloc` (on the cluster's `idClusterInv`,
a key above every key: R2c's design for restarts), the slot and pending maps, `newServerStoreFreshA`,
`cok`, `γrev`, `srvReadNamesFreshNK` (ghost allocations, as `memberBoot`'s at a first start).

**The cluster's persistent facts are missing from the precondition.** `specR` takes, at the restarted
names `ρ`: `srvRaftLogInv`, `idClusterInv`, `idNoZero`, `srvPropMint`, `srvRdCtxInv`, `kvInvM false`.
They carry over from the stopped incarnation's names: raft's names are equal (`restartNames`),
`kvInv_restartNames`, and `probe_P4_mint`/`probe_P4_rdctx` (checked: both read only raft's names and
the issued map). `srvPropMint` holds an exclusive authority, so it must be the stopped incarnation's,
not a new one. But `BuildServer.specRestart`'s precondition (`memberRestartRes`, `bootPremiseR`,
`commonPremises`, `netHttpOk`) holds none of them, so as stated it is not provable. **Proposal P4-a:**
add to its precondition the persistent part of `memberBoot` at `ρo` (the facts above and the stand-in
conditions), as one persistent bundle the driver keeps from the cluster's allocation. A statement-only
DRAFT spec, not linked: a form change of the obvious kind, but it changes a spec's precondition, so it
is listed here for 81. Also, `srvRestartRows` reaches `BuildServer` only through P2.

**Threads (G7).** The adequacy's thread bound counts forks as steps (`Hn : n + 2 ≤ 2 ^ 28`, as in
`etcd_putget_safe`), so the first incarnation's leaked goroutines are already inside it. The write
budget is per backend (`N + 7 + bootWB ≤ backend.wbInit`, one open each) and `receiptBound GF ≤ N + 1`
is global. No change.

## S7.0 note: the driver waits for a leader before the `Range`

The first test run failed without a check: the restarted member's linearizable `Range`, begun before
the member had elected itself, returned `etcdserver: leader changed` (`linearizableReadNotify`'s
leader-change notifier fired by the election). `check` now waits for `s.Leader() != 0` first (a
liveness wait, like `stop`'s `AppliedIndex()` wait). With it, 20/20 runs pass.

## Revised estimates

| Stage | Scope | Now |
|---|---|---|
| S7.2 (G1) | 1-1.5 wk, Freeze | 2-3 d, internal (P3) |
| S7.3 (G2) | 1-2 wk | 1.5-2.5 wk, raft interface diff (P2-a) |
| S7.4 (G3) | 1-1.5 wk | 1-1.5 wk, with P4-a |
| S7.5 (G5) | 2-2.5 wk | 2.5-3 wk (P1's lemmas) |

Total about 6-8.5 weeks of work (Scope: 7-10).

## Decisions requested

1. **P2-a** (a proved raft law: a `MsgSnap`'s ends are members of the sender's configuration, in
   dynamic mode; raft interface diff). *Recommended.*
2. **P3**: G1 dropped as a spec change; `memberBuiltR`'s DRAFT body fixed and `wp_Start_builtR` proved
   (no Freeze). *Recommended.*
3. **P4-a**: `BuildServer.specRestart`'s precondition gains the persistent part of `memberBoot` at the
   stopped names. *Recommended.*
4. **P1**: the three local lemmas, and the S7.0 driver's leader wait. *Recommended.*
