# The server's auth component: a sealed slot in place of mode twins (2026-11-04)

**Kind:** a package-internal API: a slot, with predicates and laws, that replaces a mode index
threaded through about 175 definitions and 14 twin theorems. Frozen by the user, candidate 3, after
two spec-reviewer rounds. Code: `Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthComp.lean`.
Decision: `notes/decisions.md`, "The auth component".

## First version (candidate 1)

`AuthC := off | on γa`, sealed predicates `acRes` (the row's auth part), `acInv`, `acTok`, `acPub`,
`acBkts`, `acImg`, `acOpenQ`, `acModesOk`, `acRead`, `acSnapOk`, and laws for each divergence point
of the twins. The claim was that only `applyEntryNormal`'s data branch diverges in the KV model and
the applier contract, so that branch alone would keep two cases. The admin, Authenticate and boot
laws were shapes ("the existential is fixed by elaboration").

## Critiques (two spec-reviewer rounds) and what they changed

1. **A law false in its trivial instance**: `acSnapOk_intro`'s off case took its fact from the kit,
   but the off kit is `True`; off's fact sits in a separate conjunct. → The off value of a slot
   predicate is defined from where the off proof really gets its fact (`acSnapKit .off :=
   authRecoverOk`), with a bridge law from today's conjuncts.
2. **A law with no client, and false besides** (`acRes_recovered`). → Deferred to the stage whose
   client needs it.
3. **The divergence map was drawn too narrowly**: the model step at the top, and the replayed
   branch with its admin case below `c₀`, also diverge. → The two-case law covers the whole entry.
4. **Divergence points the slot missed** (the lessor premise, the receipt and its bound, the
   compactor's restriction, the window's side condition) and **containers not inventoried**. →
   Added as slot predicates, or listed for stage 2.
5. **Shapes cannot be frozen, and an elimination law that exposed the slot's interior** (the
   history `hs`). → Replaced by opening laws (`acRes_on`, `⊣⊢` today's definition), confined to
   the one two-case law, and marked as a departure until the single model.
6. **Pure pieces sealed although clients outside read them** (`acBkts`, `acOpenQ`). → Made public.
7. (Round 2) **A gate the plan itself could not pass**: containers that differ in the model cannot
   be rewritten through a resource slot. → The allow file names them until stage 3.

## The approved spec

Candidate 3 is what `AuthComp.lean` states: its header and docstrings, and the laws in the order
of the twins' divergence points.

Principles exercised: PRINCIPLES' slot convention (a hub names a subsystem through sealed slots and
laws); a law's trivial instance must be checked as carefully as the real one; a spec in shapes is
not a candidate; map the clients' divergence points before stating the laws.

# Stage 2: the rows over the slot and the merged linked specs (2026-11-04)

**Kind:** five linked Hoare triples (`run`, `start`, `Start`, `applyAll`'s batch, `AppliedIndex`)
merged from off/on twins into one statement over the slot `C`, with new `…C` rows
(`AuthCompRows.lean`). Frozen by the user, candidate 6 ("freeze it, go ahead with stage 2"), after
spec-reviewer rounds 1 to 5.

## First version (candidate 1)

Every mode-indexed row re-indexed by `C` (72 `on : Bool` definitions and the `AuthMode` ones),
every spec over `E.authOn` restated over `C`, and literal `true` arguments replaced by `C.isOn`.

## Critiques and what they changed

1. (Round 1) **Most rows are model rows, not resource rows.** A classification of all 72 bodies
   showed the KV model, not the auth resource, is what most rows read. → Only resource rows and
   their containers move to `C`; model and flag rows keep `Bool`, used at `C.isOn`.
2. (Round 2) **Renaming in place changes exported texts.** Re-indexing `isServerReqM` changed
   `Put.specOn`, v3rpc's results and the admin `specOn`s. → New names for the `C` rows (`…C`),
   with bridges `XM C.isOn ⊣⊢ XC C` under `hC`; the old rows stay.
3. (Round 3) **The narrowing reached axioms.** Restating every spec over `C` changed four
   trust-boundary axioms (`waitAppliedIndex`, `waitLeader`, `ensureLeadership`,
   `leaseTimeToLive`) and v3rpc's exported results. → Scope cut to the five linked twins; every
   other spec and every axiom keeps its text. A spec moves to the `C` rows when its proof does.
4. (Round 3) **A gate that counts vocabulary, not divergence.** → The ratchet counts matches on a
   mode outside the slot, twin declarations and literal mode arguments, not `C` binders.
5. (Round 4) **A commit that cannot build.** One-way bridges could not carry the merged spec's
   pre back to the twin proofs. → Bridges stated `⊣⊢`; the merged proofs case on `C` and call
   the renamed twins (`X.wp_proofOff`, `X.wp_proofOn`) through them, until 2c gives one proof.
6. (Round 4) **Exported results whose meaning changes must be listed** (`applyAll_model`,
   `server_run`, `server_start`, `server_Start`: same text, stronger).
7. (Round 4) **Callers incomplete, and `=term` link entries the script splits on spaces.** →
   Every caller listed; off-only callers link a named corollary (`EtcdServer.wp_Start_off`,
   `LinkedOff.lean`).
8. (Round 4) **A bound count that grows**: `Start`'s reader stocks would appear three times. → One
   row, `srvStartReaders`, folded in the merged post and its corollaries.
9. (Round 4) **Pure premises belong in the precondition** of a changed spec (PRINCIPLES). → The
   five merged specs carry `⌜E.authMode = C.mode ∧ acReceiptOk C ∧ …⌝` in the pre.
10. (Round 5) **An import cycle and the twin proofs' names.** `AuthComp` imported the module the
    merged `applyAll` spec needed below it. → `snapAuthResM_on` moved beside `snapAuthResM`; the
    off twins renamed `wp_proofOff` so the merged proof takes the linked name.

## The approved spec

Candidate 6: the merged statements in `Spec/go_etcd_io/etcd/server/v3/etcdserver/
EtcdServer__{run,start,Start,applyAll,AppliedIndex}.lean`, the rows in `AuthCompRows.lean`, the
old texts as corollaries in `ModeSpecs.lean` (`X.spec_off`, `X.spec_on`).

Principles exercised: classify before re-indexing (a row's index is what its body reads); a
restatement's blast radius includes axioms and exported texts, so scope it to what the proof
change needs; a merged statement must carry both twins (equivalent under the mode premise, the
corollaries proved); keep a changed spec's pure premises in its precondition.

# Stage 3: the remaining linked twins folded, the corollaries gone (2026-11-04)

**Kind:** a plan of restatements, not one triple: the server's request-path `specM` family
(`parseProposeCtxErr`, `raftRequest`, `doSerialize`, `processInternalRaftRequestOnce`) folded into
one `spec` each, `ModeSpecs.lean`'s off/on corollaries of the stage-2 merged specs deleted with
their `_on` results, `Start`'s off clients moved to the merged spec. Frozen by the user, candidate 5
("freeze it, go ahead with stage 3"), after spec-reviewer rounds 1 to 4.

## First version (candidate 1)

Delete `ModeSpecs.lean` first; fold `applyEntryNormal`/`apply`/`applyEntries` (3b) and the server's
`specM`s (3a) after; a merged exported result "covers" every deleted `_on` result; `NewServer` kept
as an off-only `spec` plus an on-only `specG true false`; the mode gate lowered by a new class
`instance` and by renaming client `specM`s.

## Critiques and what they changed

1. (Round 1) **A commit order that cannot build.** The twin proofs and five off examples state
   ModeSpecs' definitions, so deleting it first breaks them. → Every ModeSpecs consumer listed with
   where it goes; deletion after its consumers move.
2. (Round 1) **"Covered by a merged result" checked, and false** for `Range`, `raftRequest`,
   `applyAll`; `server_Start_on` and the request-side `specOn`s have consumers (the auth example,
   v3rpc). → §4 lists each exported result: deleted, replaced (with the new statement), same text
   with a new proof, or unchanged.
3. (Rounds 1, 3) **A gate change dressed as a classification.** An allow line only classifies;
   the gate counts every finding, so a new class or a rename lowers nothing (or only dodges the
   pattern). → No renames to dodge the gate; changing what it counts is its own decision (D8, not
   taken); the estimate recomputed from the gate's own findings.
4. (Round 2) **A merged spec that cannot be linked.** One `NewServer.spec ∀ on cmp` needs, at
   `on = true`, premises only `server_new_auth_on` supplies (D22's trusted schema): every off client
   would inherit them. → `NewServer` out of scope (D6).
5. (Round 2) **A hidden binder.** Inlining `AppliedIndex`'s `∀ on` would hide it from the gate.
   → No inlining; `AppliedIndex` keeps its text (D7 (b), after round 3 found the restart example's
   exported triple would change under (a)).
6. (Round 2) **Unpriced options.** D2 (i), deleting `LinkedOff`, priced in files (`gen-link.py`,
   two link lists, two regenerated Links); the 3b pilot given a numeric bound (the twins' 1,133
   lines) with a stop rule.
7. (Round 3) **A "nothing uses it" set that was wrong.** Six of 3-0's declarations were used inside
   ModeSpecs by kept ones. → A full table of the file's 68 declarations with their consumers.
8. (Round 4) **Counts and instructions exact**: the allow-line instruction (c4's range would fail
   `--check`), 3-0's count (16), the estimate's two totals agreeing, §4 listing the results whose
   premises get weaker (`authkv_startServer` loses `[ErrorStringLeaf]`).

## The approved spec

Candidate 5, D1–D8: layer A deferred; `Start`'s clients instantiate the merged `Start.spec`
(`isServerBuilt_offC` at `.off`), `LinkedOff` deleted; the receipt `if` kept; the request side,
`NewServer` and `AppliedIndex` unchanged; 3-0, then the pilot, then 3a. The pilot failed its bound
(projected ~1,200 lines), so `applyEntryNormal`'s twins stay, as D5 said.

Principles exercised: a deletion plan lists every consumer of what it deletes, checked by a table,
not by "nothing uses it"; a claim that a result is "covered" is checked per result, with its
replacement statement; a gate is changed only by a decision about what it counts, never by
classifying or renaming; an option is priced in files before it is chosen; a pilot gets a numeric
bound and a stop rule fixed before it starts.

# Stage 4: the request side's server and v3rpc layers (2026-11-04)

**Kind:** a plan of restatements over two layers: the server's `Txn` (one spec in place of `spec`,
`specOn`, `specOnR`, one proof), the `Put`/`DeleteRange`/`Range` corollaries deleted, and v3rpc's
answer contract to the gRPC handlers merged (`srvKVAnsM on`, one proof per operation), the exported
off and on results kept in text as instances. Frozen by the user, candidate 4 ("freeze it, go ahead
with 4-1"), after spec-reviewer rounds 1 to 4; the user chose (a) for round 1's B4.

## First version (candidate 1)

Stage 4 is L1 (server) and L2 (v3rpc) of four layers; L3 (the client's registrations) and L4
(`Serve`) later. One `Txn.spec` over `E.authOn`, with the premise `E.authMode ≠ .any` for both
cases; the corollaries deleted together with the request path's three `spec_off`s; `srvKVAnsM` and
its rows sketched, not written; the on-only facts as flag rows at a mode.

## Critiques and what they changed

1. (Round 1) **Consumers not listed**: `Txn.spec`'s exported callers (`txn_readonly`,
   `txn_applied`), and the request path's `spec_off`s, which `Compact` and the off tails still use.
   → A consumer table per changed or deleted declaration, with the commit that moves each; the
   three `spec_off`s kept.
2. (Round 1) **A gate the plan did not price.** New rows with `match on` are match-mode findings.
   → Every row written without a match: a mode-dependent part gated (`⌜on = true⌝ → …`) or read at
   the mode (`kvModelM on`); each commit passes `mode-check.py --check`, counted per commit.
3. (Round 1) **A hypothesis choice** (B4): the merged proof's on read needs `CheckTxnAuth.specLb`,
   which the link does not pass. The user chose (a): both specs as hypotheses, `.specLb` linked by a
   named closed term, the trust-base checks at each commit.
4. (Round 1) **Rows and laws sketched, not stated** (`srvKVAnsM`, its rows). → Written out, with
   their laws.
5. (Round 2) **Counts estimated, not recounted.** → The gate's findings recounted per file and line;
   one definition per row (the off and on names abbreviations of the `M` row), no per-row bridges,
   generic permit helpers (`Gb` with its premise, not `hdrBoundM true`).
6. (Round 2) **A fallback that contradicted the commit order** (the case proofs' names and the
   twin count). → The fallback stated with its own gate numbers and its own commit grouping.
7. (Round 3) **Laws false at one mode, from the atomic update's variance.** The grant `G` of
   `kvAu1G γk f G Q` is the committer's to supply, so weakening the update strengthens `G`: a gated
   grant `⌜on = true⌝ → X` can be added at any mode, removed only at `false`, identified with `X`
   only at `true`. Three "any `on`" laws were false at one mode. → Each stated at the literal mode
   where it holds (`kvDepOwnM_true` as `⊣⊢`, `kvDepOwnM_false`, `txnPermit_of_false`), counted by
   the gate as bridges, never with an `(h : on = b)` premise.
8. (Round 3) **A binding premise in the wrong direction**: the permit helpers' `Gb` premise flipped
   and gated (`on = true → ∀ hm, Gb hm ⊢ hdrBoundT …`).
9. (Round 3) **A scope restriction wider than today's**: `≠ .any` (and the read's lower bounds)
   only in the read-only branch; the writing case's footprint today's.
10. (Round 4, non-blocking) The proof lines the abbreviations touch listed; dead helpers' list
    corrected; `#print axioms` lines for the new results.

## The approved spec

Candidate 4, D1–D8, as built (4-1 to 4-4): `Txn` merged (1,369 lines against the bound 1,460);
v3rpc's proofs one per operation (613 lines against 966); the corollaries gone; the mode gate 327 →
300. Two departures, recorded in `notes/decisions.md`, "The auth component, stage 4": the off and on
`*_end_to_end` results stay derived through `raftKV_server(On)` (now instances of the merged
`raftKV_serverM`) instead of from the merged `*_end_to_endM`; and the put and delete proofs take
`Put.spec`'s gate `hdrBoundM true` by unification rather than writing the literal.

Principles exercised: before stating a law over a free mode, check it at both literals against the
variance of every resource it mentions (an atomic update's grant is contravariant); state a law that
holds at one mode only at that mode, where the gate sees it; write a merged row without a match on
the mode (gate the mode's part); recount a gate from its findings, not by estimate.

# Stage 5: the served KV side and `Serve` (2026-11-05)

**Kind:** a plan of restatements over the last two layers of the request side: the client's KV
registrations (one `GrpcSpecMd` per KV method over the mode, the handlers and the served result
merged at `E.authOn`) and `etcdstart.Serve` (one spec, the caller's ghost step from `grpcUpM
E.authOn`), the exported off and on texts kept as views. Frozen by the user, candidate 6 ("yes,
freeze c6"), after spec-reviewer rounds 1 to 5.

## First version (candidate 1)

The merged gRPC specs `etcdXSpecM on` with the on facts at the mode; the merged handlers and served
result with `hρ : ρ.rd = γr`; `grpcUp`/`grpcUpOn` made abbreviations of a `grpcUpM`; the off and on
registrations as views of the merged one "as `raftKV_server(On)` do"; `LinkOn.lean` and the on
handlers deleted; a gate estimate.

## Critiques and what they changed

1. (Round 1) **An off-only fact ungated.** The off handlers' revision bound `kvRevLb` is a fact about
   the off model, produced only from the off invariants; the merged handler cannot supply it at `on`.
   → Gated, `(⌜on = false⌝ → kvRevLb …) -∗`, and read off the read view at off only.
2. (Round 1) **The on view is not today's on text**: at `true` the merged spec has
   `⌜true = true⌝ → …` where the on spec has the fact. → A named view per row and mode, checked
   against each on client's statement; the on clients' texts kept.
3. (Round 1) **Consumers missed** (the deleted handlers', methods' and lists' users; `Serve.spec`'s 12
   clients; `grpcCfgOk_of_started`'s watch consumer; the files the link generator reads). → A
   consumer table by grep, per declaration.
4. (Round 1) **Nothing excludes `.any`**, which the merged proofs need. → `⌜E.authMode ≠ .any⌝` in
   the handlers', the served result's and `Serve.spec`'s preconditions.
5. (Round 1) **Abbreviations break positional unfolds** (`grpcUp := grpcUpM false` changes every
   `iunfold … icases ⟨…⟩` of it). → `grpcUpM` its own definition, `grpcUp`/`grpcUpOn` kept, related
   by named laws.
6. (Round 2) **An ungated premise contradicted a kept text**: `hρ : ρ.rd = γr` cannot be passed by
   `etcd_kv_auth_served_on`, which takes them independently. → Gated, `hρ : E.authOn = false →
   ρ.rd = γr`.
7. (Round 2) **A commit that could not pass the gate** and **a module that made an import cycle**.
   → The gate counted per commit; the merged proofs placed after their imports.
8. (Round 3) **A placement not checked against what the moved code uses**: a new module below
   `Results.lean` could not see the declarations its proofs call. → The merged proofs stay in
   `Results.lean`, in place of the off ones; checked by listing the identifiers each moved block uses.
9. (Round 4) **Bridges stated in the direction the author assumed, not the consumer's**:
   `raftKV_srvKVAnsM_false` went from the old answers to the merged ones, where `raftKV_mono`'s
   contravariance and the consumer (`raftKV_server`) need the converse. → Restated from the consumer's
   goal, `raftKV s (srvKVAnsM false …) ⊢ raftKV s (srvKVAns …)`.
10. (Round 5, non-blocking) `rw` after `cases hon : E.authOn` fails (use the case's literal); bridge
    proofs as terms, not `iapply`; 5-3's size recounted.

## The approved spec

Candidate 6, D1–D7, as built (5-1 to 5-4): one registration per KV method and mode-free laws
`isGrpcRpcMd_mono(_upd)`; one handler per method and one served proof at `E.authOn`; one
`Serve.spec`; the on handlers, `ServedOn.lean`, `Serve.specOn`, `LinkOn` and their dead helpers gone;
the mode gate 300 → 277, then 288 once the bridges were restated at their literal (lean's 300 → 288). Departures in `notes/decisions.md`, "The auth component, stage 5":
`grpcCfgOk_of_startedM` takes `srvAuthLb`; a client helper `serveViews_off`. And one self-caught: the
5-2 author stated the per-row bridges over a free `on` with an `(hon : on = b)` premise, which hides
their literals from the gate; 5-4 restated them at the literal, as frozen (stage 4's critique 7).

Principles exercised: a view of a merged spec is checked at each literal against each resource's
variance (here the off view needs `|==>`, so the registration laws are stated under an update);
before placing a new module, list what the moved code uses; state a bridge from its consumer's goal;
a one-mode law at its literal, never with an `(h : on = b)` premise, even when the premise makes the
gate's count look better.
