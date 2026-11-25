# dsv-fix6: the three refuted premises, restated narrowly as per-function axioms (#49)

2026-11-25. Upamanyu's decision (coordinator-E on #8, 2026-11-25T16:05:44Z, items 1-3): craq's `LogHyp`,
rabia's `zerolog.Hyps` and QuePaxa's `PbHyp`, refuted as stated (`notes/axiom-review/dsv-fix4/
{log-logger,zerolog,quepaxa-pb}.md`), are restated narrowly, reviewed again by the `axiom` skill, and become
per-function interim axioms as in fix 4 (`etc/dsv/README.md`, "Per-function axioms"). grpc's initializer
(item 4) and go-redis's (item 5) are not touched.

**State (2026-11-25, third session): rabia done; QuePaxa done (review: see below); craq not started.**
- **Gates (2026-11-25, at `eb7cf0b3fd`, rabia only): all passed** (rerun after the disk was freed:
  full build, links, tcb and the 64 collections, goose, gen-init, kitgen, models, gh-inbox, k8s tests, ...).
  So rabia alone (`b4c6c1c758` + notes) could be queued as it stood.
- **rabia (item 2 below): done.** `a28755b089`'s 16 zerolog axiom files and `HypsHoldLinked.lean` restored;
  `Spec.lean`'s `New.spec` is `New(interface.nil)` with post `loggerOk lg`, `Logger.level.spec` takes
  `l ↦{dq} lg ∗ loggerOk lg` and gives the points-to back. `loggerOk lg := □ loggerMade lg`, `loggerMade`
  an opaque with no law, **fixed** in `Spec.lean`. Review: `notes/axiom-review/dsv-fix6/zerolog.md`,
  **survives** with conditions; doc bug `nonissues/rabia-getloglevel-doc-panics.md`. TCB: +16 axioms, one
  premise fewer.
- **QuePaxa (item 3): done at `3a6222e221`**, simpler than the token design below: the owned case stays the
  whole struct `l ↦ v` but asks `⌜stateOk mi v.state'⌝` (`Msg.lean`: `state` unset or the type's own
  `MessageInfo`, `replicaMI i`/`clientMI i` = `arrayIndexRef MessageInfo i (globalAddr file_…_msgTypes)`,
  the generated `ProtoReflect`'s `mi`); the shared case's invariant content `rt*` also states `stateOk` and is
  `@[no_expose]` (sealed: no client can take the runtime fields out and store). `sizeCache` stays free (Marshal
  sizes before it marshals with the cached sizes). Closes the fix-4 review's A (owned `state` of another type)
  and B (a client storing `sizeCache` through the invariant). Proof changes: `pt*_share` takes `(hst : stateOk
  …)` (sites: `imod pt*_share ⊤ _ _ ?st $$ H` + `case st => exact stateOk_zero _`); `access_sep_pure` for the
  Access instances; `Kv.wp_residentExecute`/`wp_Execute`, `Exec.wp_applySMRLogic`/`wp_executeClientBatches`
  posts gain `⌜∀ o ∈ outs, stateOk (clientMI 0) o.state'⌝` (Usm shares them, `bigSepL_fupd_mono_mem`);
  `Fetch.wp_HandleFetch`'s post and loop invariant carry `stateOk (replicaMI 3)`; Propose's shared proposal
  `x = {Pc with …}`. The fix-4 axiom files `proto/{Marshal,Unmarshal}.lean` are back (headers dsv-fix6) and
  `quepaxa_remote_robust.spec` lost only the premise `PbHyp` (`remoteStepBound` kept). Built:
  `quepaxanet.{TopLevelRobustness,NonVacuityLinked}`, full `lake build`. TCB: +2 axioms
  (`raxos.hyp.proto.{Marshal,Unmarshal}.wp_proof`); baselines not yet updated (wait for the review).
  Review: `notes/axiom-review/dsv-fix6/quepaxa-pb.md`: **refuted as stated, survives with one condition**.
  A and B are closed; **counterexample C**: `marshalPre`/`unmarshalPre` ask only `isPkgInit proto`, so a
  Marshal/Unmarshal from a package-variable initializer or an early `init()` of the message's own package
  (before `file_*_msgTypes` is built) is "proved" safe and panics in Go (index out of range / nil deref,
  tested). QuePaxa never does this. **Remark**: `replicaMI i`/`clientMI i` are not the real address
  (`file_*_msgTypes` is a slice variable: `&msgTypes[i]` points into its heap array), so `stateOk` is
  literally false of the real heap though no translated program can observe it.
  **Next (exact):** (1) in `Msg.lean`, add the declaring package's `isPkgInit` to each kind of `marshalPre`
  and `unmarshalPre` (`pkg_id.raxos.replica.src` for the six consensus kinds, `pkg_id.raxos.proto.client`
  for `ClientBatch`; persistent), and thread it at the callers (`cbMarshal.spec` already holds the
  client's; the gRPC codec path `qpCodec`'s callers, `grep -rln 'marshalPre\|unmarshalPre' Dsverify`);
  (2) make `replicaMI`/`clientMI` opaque per-type tags (`opaque replicaMI : Nat → Loc`, docstring: the
  address of `msgTypes[i]` in the slice's backing array, not the variable) so the docstring is true;
  (3) rebuild `quepaxanet.{TopLevelRobustness,NonVacuityLinked}` and the full build; (4) a fresh review
  (append to the same report or `quepaxa-pb-2.md`); (5) on survival: `etc/tcb-report.py --check --update`
  and `--collection etc/tcb-collections/dsv-quepaxa.txt --check --update` (+2 axioms, checked: exactly
  `raxos.hyp.proto.{Marshal,Unmarshal}.wp_proof` NEW, nothing else), index both dsv-fix6 reviews in
  `notes/axiom-review/README.md`, update `etc/dsv/README.md`'s fix-4 section (lines 70-89: PbHyp leaves
  "refuted stays a premise" and "Left premises"), `notes/STATUS.md`, then `etc/gates.sh`.
  **Until (1)-(4), `3a6222e221` must not be queued** (it replaces the premise by refuted axioms); `eb7cf0b3fd`
  (rabia) can be.
- **craq (item 1): not started.** Coordinator-E chose option 1 (errAny's fact in `Net/`, proved at its
  producers; stop if a `TopLevelRobustness` text changes).

## 1. craq: `log.(*Logger).Printf`/`Println` (and the package-level `log.Printf`/`Println`)

**Old premise** (`Craq/LogHyp.lean`, `LogHyp`): `l ≠ null →
{{ isPkgInit log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }} l.Printf msg arg {{ RET #(); arg ↦*{dq} xs }}`
(and `Println`), with `argOk v` = `nil`, or `fmt.ArgWf`, or a type with neither `Error` nor `String`, or
`models_lab.errAny v`. `log.Default` survived its review and is restated unchanged.

**Restated** (the same triples over a narrower `argOk`; nothing else changes, so on every argument list the
new condition admits, the old one did too):

    /-- The types fmt formats calling no `Format`/`GoString` at any place it visits: least fixpoint. -/
    inductive FmtPlain : go.GoType → Prop
      | basic   : IsBasicType t → FmtPlain t
      | named   : methodSet t !! "Format" = none → methodSet t !! "GoString" = none →
                  methodSet t !! "Error" = none → methodSet t !! "String" = none →
                  FmtPlain (underlying t) → FmtPlain t          -- a named type, its underlying type
      | struct  : (∀ f ∈ fields, exported f → FmtPlain f.ty) → FmtPlain (StructType fields)
      | ptr     : FmtPlain t → FmtPlain (PointerType t)          -- the pointee, at depth 0
      | slice/array/map : FmtPlain of the element (and key) types
      -- no constructor for an interface-typed field: its dynamic value is not known

    def argOk (v : GoInterface) : IProp GF :=
      nil ∨ ⌜fmt.ArgWf ii⌝ ∨ ⌜FmtPlain ii.ty⌝ ∨
      (models_lab.errAny v ∗ ⌜ErrFmtPlain e.ty⌝)   -- `Format = none ∧ GoString = none`, and under `%#v`
                                                    -- the visited fields `FmtPlain` (as `FmtPlain` minus
                                                    -- the `Error = none` of the top type)

(Perennial's `fmt/Args.lean` `argOk` requires `Format = none` and a `stringMethodSpec`; this adds the
recursion it does not need, as its `fmt` model never visits fields.) The review's attack 9 (fmt reads a
top-level pointee with no permission) is closed by asking, in the `ptr` case at the top level, a persistent
points-to of the pointee (craq's `*store.Item` is `itemPtr`, persistent; `*transport.NodeMeta` is
`metaPtr p dq m`, so that one site keeps a fraction and gets it back).

`LogHyp.wp_Printf`/`wp_Println` (the package-level functions, proved over Perennial's no-op model) take the
same narrowed `argOk`: today they step the no-op over the wide one (the Perennial finding,
`notes/perennial-changes.md`, "`TrustedCode/log.lean`'s no-op ...": #56 records the model's gap but says no
proved path passes such an argument; craq's coordinator does).

**The blocker found.** The errors craq logs are mostly `errAny` values whose type the proof does not know:
the node's `Read` (tail's `LatestVersion`), `Start`, `Write` (×2), `CommitM`, `ReqProp` (×2) and
the coordinator's `AddNode` (×3) and `RemoveNode` (×3) log an error from an RPC (Net's `callPost`, third
disjunct: `models_lab.errAny err`) or one passed up from it. `errAny` says only "some `Error()`", so
`ErrFmtPlain` is unprovable there. The producers are concrete (`Net/Proof/net/rpc/Errs.lean`: `errors.New`'s
`*errorString`, the net extension's `*OpError`, the codecs' `errors.New` errors), so the route is:
**`models_lab.errAny` gains `⌜ErrFmtPlain e.ty⌝`** (`Net/Proof/models_lab/Errors.lean`), proved at its
producers (`errAny_newVar`, `errAny_errorString`, `errAny_resErr`, `opErr_errAny`, the generated codecs'
`dec` obligations via `pbgen`/`jsongen`'s templates), and the `icases`/`unfold errAny` sites adjusted (95
mentions in `Net/`; every Net kit rebuilds). Smaller alternatives, each needing coordinator-E's word: a
craq-local `errLog` returned by craq's `Iface` specs (still needs Net's `callPost` to carry the fact), or
the kit's Go logging `err.Error()` at those sites (as `node.go:135` and `coordinator.go:161` already do), a
program change.

**Retirement route** (`notes/dsv-axiom-routes.md`'s style): `*Logger`'s methods are **Perennial-trusted
code** first (`TrustedCode/log.lean`: `Logger.Printf`/`Println` beside its `Printf`/`Println`, with #56's
condition), then **translate** with #56's plan (Go models of `log` over `fmt.Appendf`/`Appendln` once the
reflection stages S0+S0.5 land); the axiom's argument condition becomes the `fmt` model's.

## 2. rabia: `zerolog`

**Old premise** (`Dsverify/Proof/github_com/rs/zerolog/Spec.lean`, `Hyps`): `∃ ownEvent, EventSpecs`;
`Logger.level.spec`: `l ≠ null → {{ isPkgInit }} l.M() {{ e, RET #e; ownEvent e }}`, no resource of `l`;
`New.spec`: every `w`, `{{ isPkgInit }} New(w) {{ lg, RET #lg; True }}`; `Msg`, the field methods,
`ParseLevel("warn")`, `SetGlobalLevel` as in the file.

**Restated: `New` restricted to `nil`** (the simpler of the two the decision allows, and all rabia calls:
`internal/logger/logger.go:95`, `zerolog.New(nil)`; `New` replaces a `nil` writer by `ioutil.Discard`,
whose `Write` never panics; the other choice, a recorded writer with its `Write` spec, would need a
writer-spec vocabulary rabia never uses):

    opaque loggerOk : Logger → IProp GF            -- persistent (a law, axiom)
    axiom New.wp_proof : {{ isPkgInit zerolog }} New(interface.nil) {{ lg, RET #lg; loggerOk lg }}
    axiom Logger.<M>.wp_proof (M ∈ Trace Debug Info Warn Error) : ∀ l lg dq,
      {{ isPkgInit zerolog ∗ l ↦{dq} lg ∗ loggerOk lg }} l.M() {{ e, RET #e; l ↦{dq} lg ∗ eventTok e }}

(`l ≠ null` follows from the points-to and is dropped.) The field methods, `Msg`, `ParseLevel("warn")` and
`SetGlobalLevel` are the old fields verbatim (they survived the review, with its conditions 1-9). Each
claims no more than `Hyps` on rabia: `New` at `nil` is an instance of `New` at every `w`, with a post
`loggerOk lg` that only the level methods consume; the level methods ask more. Proof changes:
`InitLogger.spec`'s post becomes `loggerOk lg` (`internal/logger/{Spec,InitLogger}.lean`);
`Server__TerminalLogger.lean` stores `lg` in `tLogger` (owned: pass `dq = 1`); `KVSExecutor.lean` reads
the logger through `Proxy`'s field (`proxyFields`' `HLogNN`): `proxyFields` gains
`structFieldRef Proxy "Logger" p ↦□ lg ∗ loggerOk lg`, established where the `Proxy` is built from
`InitLogger`; `HypsHoldLinked.lean` (from `a28755b089`) builds the class from the axioms; `etc/dsv/rabia.py`'s
`discharged` as in `a28755b089`.

**Retirement route:** **translate** zerolog v1.23.0 with bodies (`notes/dsv-axiom-routes.md`, §1's
zerolog row: goose takes it but `ch = newCallerHook(...)`, `[[skip]]`); `loggerOk` becomes the logger's
representation and the 16 axioms theorems.

## 3. QuePaxa: `proto.Marshal`/`Unmarshal`

**Old premise** (`Dsverify/Proof/raxos/Hyp.lean`, `PbHyp`): `Marshal` over `msg.marshalPre m Ψ`,
`Unmarshal` over `msg.unmarshalPre bs m Ψ`, whose representations (`msg.pt*`) own or share the whole
message struct, runtime fields `state`/`sizeCache` included, with any value.

**Restated (the representation, not a gate):** the message representations split each struct into its
program fields and protobuf's runtime fields; the runtime fields are held only by a sealed protobuf token
`pbRt l` (`@[no_expose]`, opaque: no law lets a client open it or store through it), with `state` zero or
the type's own `MessageInfo` (`file_…_msgTypes[i]`) and, in the shared case, `sizeCache ∈ {0, size v + 1}`
for the immutable value. The program's representation never hands out `state`/`sizeCache`; `Marshal` and
`Unmarshal` take and give back the token; a whole-struct copy of a same-typed message keeps it (a law).
Proof changes: the `msg.pt*` representations and `msg.pbRtN` (QuePaxa's `Proposer`/`Recorder` message
proofs), every construction of a message (it gets the token from the allocation, zero runtime fields).
Claims no more on QuePaxa: the old precondition held for every runtime-field value, this one for the two
the representation allows.

**Retirement route:** **Go model**, the protobuf-go registry/runtime model of #37 (`7166942039`), where
`state`/`sizeCache` are the model's own fields; until then the axiom.

## What remains, in order

1. ~~rabia~~ (done, above).
2. craq, option 1 (decided).
3. QuePaxa's representation refactor.
4. For each: a fresh `axiom`-skill review given only the axiom and its Go (`notes/axiom-review/dsv-fix6/`),
   the statement's premise removed (`TopLevelRobustness` only loses a premise), `etc/tcb-report.py
   --check --update` and the kits' collections, `etc/dsv/README.md`'s fix-4 section ("a refuted axiom stays
   a premise") updated, then `etc/gates.sh`.
