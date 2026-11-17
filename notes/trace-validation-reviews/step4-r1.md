# Trace-check step 4 (the three statements), review round 1

Reviewed: `trace-check` at `e05ff2026d` (the merge of `trace-check-s4`), file
`Proof/go_etcd_io/raft/v3/TracedRunSpecs.lean`: `RunTracedOk`, `node.run.gatedSpec`,
`node.run.spec_of_gatedSpec`, `RawNode.Advance.tracedSpec`, `RawNode.Advance.spec_of_tracedSpec`,
`raft.applyConfChange.tracedSpec`, plus the "Step 4" section of `notes/trace-check-design.md`
(lines 36-161). I did not modify the repository; this report is the only file written.

Elaboration: `lake env lean Proof/go_etcd_io/raft/v3/TracedRunSpecs.lean` reports no errors. Its one
warning is `package_sem` unused in `RawNode.Advance.spec_of_tracedSpec`. Both instance theorems are
proved, with no `sorry`. (`etc/lean-check.py` failed in this sandbox, which does not support Unix
sockets: `OSError: [Errno 95]`.)

Go sources: `.lake/raft-trace` (`e8f9566`, the trace hooks under the goose tag). Its `run`, `Advance`,
`applyConfChange` and `switchToConfig` match the Goose output `Code/go_etcd_io/raft/v3.lean`
(`raft.switchToConfig.impl` at :8389 calls `traceConfChangeEvent` at :8513). I did not diff it against
the pin `565c2bd`.

## Verdict

All three statements are **true of the Go code** as far as I could check, and their gated premises
hold vacuously in the untraced case. The two instances that were written are honest:
`node.run.spec_of_gatedSpec` discharges `RunTracedOk` by `absurd` and the escrow half by `gateTr_none`;
`RawNode.Advance.spec_of_tracedSpec` likewise. The pre and post of `RawNode.Advance.tracedSpec` are
word for word those of `RawNode.Advance.spec` (`Spec/go_etcd_io/raft/v3/RawNode__Advance.lean:100-141`).
`raft.applyConfChange.tracedSpec` is `raft.applyConfChange.spec`
(`Spec/go_etcd_io/raft/v3/raft__applyConfChange.lean:188-221`) plus the capability and the new binder `γ`.

First tier (fix before proving `node.run.gated_of`):

- **F1**: the source of `c'.cfg = c` (known open point 1). I agree with the proposal and say below why
  it cannot be derived. It must actually be made (a `Spec/` change and a `confcP` clause), and §3.1's
  table updated.
- **F2**: `raft.applyConfChange` would get two proofs. There is no `spec_of_tracedSpec`, and the docstring
  plans to keep today's proof as well.
- **F3**: the intended theorem's tick hypothesis is untraced-only. `RawNode.Tick.spec` takes
  `γ.reTrace = none`, and the traced tick is a separate statement fixed to the traced case (a twin).

Second tier: S1-S7 below. That list includes known open point 2, the fit from `StartNode`'s caller: it
blocks step 5, not `gated_of`.

## What is good

- **One statement for both modes.** Each target is today's spec with its untraced premise replaced by a
  premise gated on the trace mode (as `RawNode.acceptReady.spec` has been since slice 28n). The traced
  content stays inside the predicates both modes share (`ownRawNode`'s `rnTrace`, `isNodeChan`'s
  escrow). This is the form "One spec per function; special cases are instances" and
  `examples/restore-modes.md` ask for.
- **The gated premises of `RawNode.Advance.tracedSpec` are exactly the bounds of
  `RawNode.acceptReady.spec`** (`Spec/go_etcd_io/raft/v3/RawNode__acceptReady.lean:61`). Its one
  addition is `rs.slent = none`, so `run` discharges both bounds from one source.
- **The traced premises of `raft.applyConfChange.tracedSpec` are exactly `trCapB_hookGate_applyCC`'s**
  (`TracedApplyCC.lean:165-173`): `hboot`, `hcl`, `hbnd`. Its `hcn` follows from `c'.cfg = c`. The
  capability's form, `trCapB s.gh.tr γ r id c true (fun C => SimIdle C s)` with the default `Λ`, is
  `rnTrace`'s (`InvRawnode.lean:2695-2701`). So the proof can reseal `rnTrace` at the end state.
- **The traced restriction to a follower is true of the Go code at the `confc` arm.** `raft.hup`
  refuses to campaign while conf entries are unapplied, and `Bootstrap` leaves `applied = 0` with
  `committed = |boot|`. A node is therefore a follower until its first `Advance` after the bootstrap
  entries, and the application calls `ApplyConfChange` on each entry before that `Advance`. The
  proof's route is right: `RnTrBoot`'s second conjunct (`InvRawnode.lean:2631`),
  `ownStepGhost_applied_capplied` (`InvRawnode.lean:2920`), `DynCCPreOp`'s `capplied ≤ k`, and G3 (a)
  for `k < |boot|`.
- **`c'.cfg = c` is the right premise for `hCC`.** `bootstrap.go` already applies every bootstrap
  `AddNode` through `rn.raft.applyConfChange` inside `StartNode`, so at the `confc` arm raft's
  configuration is already the voters' (the capability requires `c.incoming ~ C`, `c.outgoing = ∅`). The
  application's re-application of an `AddNode` of an existing voter is a no-op in `confchange`.
  `traceConfChangeEvent` (`state_trace.go:272-285`) logs `cfg.Voters[0]` before `r.trk.Config = cfg`
  (`raft.go:1981-1983`), so with `c'.cfg = c` the logged configuration is both the old one and the new.
- **Every number in `RunTracedOk` has a reason, and the docstring gives it.** The third conjunct
  (`receiptBound GF + 2 ≤ traceNumBound`) comes from `budgetInv`'s `M ≤ k + 1`
  (`InvNodeChan.lean:194-196`) and `preceipt_lt` (`k < receiptBound`), which give
  `rs.tc ≤ receiptBound GF`.
- **The `gateTr (rtkRun γ.esc none)` conjunct is needed.** `run` lends it at `advancec` and needs it at
  `readyc`. Neither `runPre` nor `isNodeChan` has it, and today's proof makes it with `gateTr_none`
  (`node__run.lean:1067`, `:1147`). `StartNode`'s proof is where it can be allocated (`rtk_alloc`).

## Findings

### F1 (first tier): `hCC`'s `c'.cfg = c` has no source. The proposed client premise is right, but it is not yet made

**Principles:** Complete (sufficient for every caller); Every premise has a source the client sees.

**Evidence.** `run`'s `confc` arm reaches `hCC` through `wp_applyConf_dyn`
(`InvNodeRun.lean:1347-1445`). There the change satisfies only `DynCCPreOp (effDec dec ds) D …`, which
says that the change's effect is the recorded decision's. `node.ApplyConfChange.spec`
(`Spec/go_etcd_io/raft/v3/node__ApplyConfChange.lean:38-46`) relates the change `o` to the entry `e`
only through the decision `o'` and the shared result `m'`, and `confDecide` records any decision. So a
client may decide and apply a `RemoveNode` at a bootstrap position. `hCC`'s premise is then false, and
the trace genuinely fails validation (the specification's `ApplySimpleConfChange` reapplies the log's
configuration). The premise is therefore a real client obligation, not an artefact of the proof.

**Can it be derived instead?** Not from what raft knows:
- deriving it from the entry's content needs a premise tying `o` to `e`'s bytes. The node API takes
  `o` and `e` independently.
- it also needs raft to know that the bootstrap entries decode to `AddNode`s of the voters. Raft knows
  only `IsConfEnt` of them (`RnTrBoot`'s first conjunct). The decoding facts (`BootLogFacts`,
  `MarshalsConfChange`) are on the client's side, and G3's design dropped (a2) to avoid exactly this
  decoder dependence.
- a gate on `confDecide` would need an invariant relating every decision to the configuration at its
  position, as the design says.

The one-call premise is local and weaker for clients.

**Form.** `Cluster.trace γ ≠ none → m' = v.membership` on `node.ApplyConfChange.spec` is dischargeable
at once by its one traced caller. The harness's `app` calls `wp_ACC … v' tcMem Hva Hpos (.inl Ht1)
(by rw [Hvm]; exact Hap) …` (`Cluster__handleReady.lean:379-380`), with `Hvm : v'.membership = tcMem`
and `m' = tcMem`. Its `ConfChangeV2` arm is already refuted (`:153-157`, `committed_emptyV2_joint`
against the simple `tcMem`). Untraced callers (the etcd server, kvreconf) are untouched by the gate.

Two refinements:
- **Wording.** Write the premise as the step's fact the client already states:
  `Cluster.trace γ ≠ none → Membership.applyChange o v.membership = some v.membership` ("at a traced
  cluster the change applied keeps the view's membership"). This reads as the TLA+ requirement. It is
  equivalent to `m' = v.membership` under the existing premise `applyChange o v.membership = some m'`.
- **The `confcP` side** (`InvNodeChan.lean:1184-1193`). The gated clause
  `γ.raft.reTrace ≠ none → cs'.cfg = cfg.cfg` belongs in the dynamic disjunct beside `DynCCPreOp`.
  That is where `run` reads it into `hCC`'s `c'.cfg = c` (with `cfgStateC cf = rs.cfg`).
  `node.ApplyConfChange`'s proof derives it by injectivity of the membership-to-configuration map at
  the view. I did not check that this injectivity lemma exists (uncertain).

**What else must change.** §3.1's table still lists `node.ApplyConfChange` as "unchanged"
(`notes/trace-check-design.md:1019`, also `:1924`). This premise changes a `Spec/` statement on
`etc/api/raft.txt`, so it produces an `interface/` diff. Update the table and route the change as a
client-visible change.

**Callers affected:** the harness's `app`, `node.ApplyConfChange`'s proof, and `run`'s `confc` arm.

### F2 (first tier): no untraced instance for `raft.applyConfChange.tracedSpec`, and the plan keeps today's proof too

**Principle:** One spec per function; special cases are instances (hard rule). `restore-modes.md`:
"the callers that stay off get the old text by a lemma, not a second spec".

**Evidence.** The design note says there is no `spec_of_tracedSpec` because "it would need some
`RaftNames` value; none is needed: the untraced spec stays proved"
(`notes/trace-check-design.md:83-84`). But `gated_of` takes `hCC`, so the tracedSpec must be proved.
`raft.applyConfChange.spec` also keeps other users: `wp_applyConf_static` via `spec_simple`
(`InvNodeRun.lean:1654-1684`), `RawNode.ApplyConfChange`, and today's `node.run.wp_proof`. Keeping
both would mean two proofs of one function.

A value of `RaftNames` is trivial to build: every field is a `GSet`, `GMap`, `GName`, `List`, `Option`
or predicate (`Protocol/Ghost.lean:230-340`). Untraced, `trCapB none … = emp` (`trCapB_none`,
`TracedCap.lean:1404`), so `γ` does not matter.

**Restatement.** Add
`raft.applyConfChange.spec_of_tracedSpec (h : raft.applyConfChange.tracedSpec) :
raft.applyConfChange.spec`. It instantiates `γ` with any `RaftNames` value (a `default`, or a local
`Inhabited RaftNames` instance), discharges the gated premise by `absurd`, and frames `emp` with
`trCapB_none_intro`. Retire today's `raft.applyConfChange.wp_proof` in favour of
`tracedSpec`'s proof plus the instance. Change the docstring's "No instance theorem" accordingly.

### F3 (first tier): the tick arm has no statement covering both modes. `RawNode.Tick` is a spec plus a twin for the traced case

**Principles:** One spec per function (hard rule); Complete.

**Evidence.**
- The intended theorem lists `wp_RawNode_Tick : RawNode.Tick.spec` (`TracedRunSpecs.lean:30`), but
  `RawNode.Tick.spec` takes `γ.reTrace = none` (`Spec/go_etcd_io/raft/v3/RawNode__Tick.lean:47`).
- The traced tick is `RawNode.Tick.tracedTriple` (`TracedRawNode.lean:563-575`). It is stated at
  `γ.reTrace = some γd` and proved by its own proof `RawNode.Tick.traced` from
  `raft.tickElection.spec`/`raft.tickHeartbeat.spec` (`:581`).
- So the gated `run`'s `tickc` arm (`node.go:433-434`) would split on the mode and use two statements.
  `gated_of`'s hypotheses must then include the tick callees' specs, not (only) `RawNode.Tick.spec`.
- `RawNode.Advance` gets a statement covering both modes in this step, while `Tick`, the arm next to it,
  stays a twin.

**Restatement.** State `RawNode.Tick.tracedSpec`, which is `RawNode.Tick.spec` with `γ.reTrace = none`
replaced by `γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ`. Also state
`RawNode.Tick.spec_of_tracedSpec`, and use the new spec in `gated_of`'s hypothesis list in place of
`RawNode.Tick.spec`. Its proof joins the two existing proofs, and the untraced `RawNode.Tick.wp_proof`
then retires to the instance. At minimum, correct the header's hypothesis list so that it names what
the traced arm actually needs.

**Callers affected:** the `gated_of` prover and `Link.lean`.

### S1 (second tier): `RunTracedOk`'s fit should be supplied in the node API's vocabulary, inside `startTrace` (known open point 2)

**Principles:** Every premise has a source the client sees; Name the abstraction a definition exposes.

**Evidence.**
- `StartNode.gatedSpec` (`TracedApiDraft.lean:97-126`) and `StartNode.tracedSpec`
  (`TracedNodeApi.lean:97`) have no fit. The design proposes a new pure gated premise
  `receiptBound GF + vs.length ≤ traceNumBound ∧ 2 ≤ vs.length`.
- The node API already has `readyFits γ N` (persistent and sealed, `InvNode.lean:221`:
  `receiptBound GF + γ.bootLen ≤ 2^61`, with `readyFits_intro`).
- `traceReadyFits GF γ.raft` is the same fact at `RaftNames` (`TraceFits.lean:30-33`, `2^61 =
  traceNumBound`, `Model.lean:227`).
- The harness holds the bound in `tcWorld`
  (`HarnessDefs.lean:141`: `receiptBound GF + W.cl.bootLen ≤ 2 ^ 61`, with `W.rs.length = 3`).

**Restatement.**
- Put `readyFits γ N` into the traced branch of `startTrace` (`TracedApiDraft.lean:78-82`; its pure
  conjunct already carries `vs.length < 2^40`). Put the last conjunct there as
  `2 ≤ vs.length ∨ receiptBound GF + 2 ≤ traceNumBound`, or drop it per S2.
- `StartNode`'s traced proof then turns `readyFits` into `traceReadyFits GF γ.raft` (`bootLen =
  |reBoot|`).
- This stays in the gated bundle of resources the client already supplies and adds no new gated
  premise.

`RunTracedOk`'s first conjunct comes from `HdynOk` (`StartNode.lean:319`), as claimed.

### S2 (second tier, uncertain): `RunTracedOk`'s third conjunct may be slack

**Principle:** No constant or conjunct whose reason you do not know.

**Evidence.**
- The conjunct exists only because the traced triples take `uint.Z rs.tc + 1 < traceNumBound`
  (`acceptReady.spec:61`, `Tick.tracedTriple`, and this `hAdv`).
- In `RawNode.Tick.traced` the bound is used only to get `s.term + 1 < traceNumBound` from
  `term + 1 ≤ tc` (`TracedRawNode.lean:594-595`), and `tc < traceNumBound` gives that too.
- If no traced triple needs `tc + 1` itself, then the triples could take `tc < traceNumBound`, and the
  fit alone would give it. A single voter is fine: `StartNode` with no peers fails in `Bootstrap`
  (`bootstrap.go:33-34`), so `|boot| ≥ 1` and `receiptBound GF + 1 ≤ traceNumBound`.
- `RunTracedOk` would then be `γ.mode.isDyn = true ∧ traceReadyFits GF γ.raft`, and S1 would need no
  `2 ≤ vs.length`.

I checked `Tick` only, not `acceptReady`'s or the step bundle's uses.

### S3 (second tier): `trCapB_hookGate_applyCC` takes `hboot`/`hcl` unconditionally, while `hCC` supplies them only in the traced case

**Evidence.** `TracedApplyCC.lean:168-169` against `TracedRunSpecs.lean:182-187`. The untraced branch of
the lemma (`:176-188`) does not use them. A proof of `hCC` that calls the lemma once for both modes
cannot. Relax the two hypotheses to `tr.isSome → …`, as `hbnd` already is. This is a proof-plumbing
note for the `hCC` prover, not a defect of the statement.

### S4 (second tier): `hAdv`'s traced `rs.slent = none` follows from the precondition

**Principle:** No unneeded premise.

**Evidence.** The planned `ownRawNode_trNoLoan` derives it from `ownRawNode` (`TrNoSnap` and `LoanOk`).
`ownRawNode` is already in `hAdv`'s precondition, so the premise moves one lemma call from the callee
to its one caller. `run` needs the same lemma at `confc` anyway, so the cost is small, and taking it
keeps the snapshot arm out of `hAdv`'s proof. It is acceptable if the docstring says the premise is
derivable (it nearly does: "`run` reads it off `TrNoSnap` and `LoanOk`"). If `ownRawNode_trNoLoan`
turns out to need a mask or a later step, keep the premise.

### S5 (second tier): pure premises as Lean implications

**Principle:** Pure premises go in the precondition ("convert one when you change it").

All three are new statements, yet they put their pure premises before the triple as Lean implications.
Moving them into the precondition costs only an `ipure` in the two instances. I lean toward waiting:
`acceptReady.spec`, whose shape these copy, would have to move with them. Do it when the specs land in
`Spec/` (S7).

### S6 (second tier): `hAdv`'s premises are sufficient as far as I could follow, but unchecked in parts

**Uncertain.** I checked the following against the Go code (`rawnode.go:477-489` steps the queue
through `raft.Step`):
- **Bounds.** The per-step bounds come from `rs.tc` and the fit.
- **Leaving the joint configuration.** `c.autoLeave = false` comes from `rnTrace`, and it discharges
  `raft.Step.spec`'s `MsgStorageApplyResp` premise.
- **Snapshots.** At `slent = none` there is no `appendAck (some _)`, which discharges `raft.Step`'s
  premise `MsgStorageAppendResp → sn ≠ none → s.gh.tr = none` (`raft__Step.lean:674`).
- **Election.** A candidate winning by its own vote (`becomeLeader`'s empty entry, then `bcastAppend`)
  produces traced lines whose last index must be within the fit.

I did not check that `ownStepGhost_traceBound` covers the entry `becomeLeader` appends inside `Advance`
(in the receipt fit's terms, `lastRec_receipt`). The prover should confirm it, or `hAdv` lacks a premise.

### S7 (second tier): where the statements end up

`node.run.gatedSpec` is strictly stronger than `node.run.spec`, which is its instance. The same holds
for `hAdv` against `RawNode.Advance.spec`. Once `gated_of` is proved, the layout ("`Spec/<pkg>/<fn>.lean`:
the one Hoare triple") wants the gated statements to become `node.run.spec`/`RawNode.Advance.spec` in
`Spec/`, redefined in place, with the old texts kept only as corollaries for callers that stay
untraced. That would also put `rtkRun`'s gated half inside `runPre`, as "A new mode redefines the
shared predicates in place" asks. They should not live on as a second, raft-internal statement next to
the old one. Record this in the plan's §9 order of work.

## Bugs in the Go code

None found. Applying a change other than the entry's (a `RemoveNode` at a bootstrap position) is what
raft documents: it applies what it is handed. F1 is a missing premise of the traced node API, not a
raft bug. Nothing for `issues/` or `nonissues/`.

## Targets ranked by need of revision

1. **`raft.applyConfChange.tracedSpec`**: F1 (its traced premise has no source yet; the fix is
   client-visible), F2 (the missing instance and the two-proofs plan), S3.
2. **`node.run.gatedSpec` / `RunTracedOk`**: F3 (the intended theorem's tick hypothesis), S1, S2 (the fit's
   home and its third conjunct), S7.
3. **`RawNode.Advance.tracedSpec`**: S4, S6 (minor or uncertain). The statement itself is ready to
   prove.
