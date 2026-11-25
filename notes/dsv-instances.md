# dsv-instances: non-vacuity instances for the landed dsverify kits (paxos, rabia, QuePaxa)

> **Folded in by math-rand-isinit (2026-11-24).** This branch's finding (below) is fixed there:
> `math/rand`'s `isPkgInit` is Perennial's `isInit`, the `Intn` fields and the kits' `math.rand.InitHyp`
> are discharged by Perennial's proofs, and the rabia/QuePaxa/gryff instance modules are built
> (`notes/math-rand-isinit.md`). The text below is the record of 2026-11-24 00:52Z, unchanged.

Branch `dsv-instances`, off origin/lean 0f41838346 (Perennial 47ec64a9d). The rule (user, #24,
2026-11-24): a kit's top-level statement with hypothesis-class premises counts as closed only if
each class has a BUILT instance (a test-only module, in the gates), built from proved specs where
they exist, else from the existing interim axioms, else from local axioms in the test module that
state the library's real behaviour. A field that cannot be built is a finding: stop for that kit.

Result: **paxos** has no hypothesis-class premise (closed as it is). **rabia** and **QuePaxa** stop
at the same finding: the `math/rand` `Intn` premise cannot be built since Perennial 47ec64a9d (the
pin lean took at ea51674d0f, 2026-11-24 00:05Z). No instance module was added; no statement is
changed.

## The premises

### paxos (`Dsverify/Spec/github_com/xiang90/paxos/examples/paxosnet/TopLevelRobustness.lean`)

Only the language model's classes, which every statement of the repository takes:
`GoGlobalContext`, `GoLocalContext`, `go.Semantics`, `cmd.{orch,client0..3,server1..5}.Assumptions`
(goose's per-program unfolding assumptions), `net.FieldAssumptions`, `go.BasicIntoValInj`. No
`InitHyp`, no hypothesis class, no data class. Nothing to inhabit; the statement is closed under
the rule (as `etc/dsv/README.md` already says: "Paxos needs none").

### rabia (`Dsverify/Spec/rabia/examples/rabianet/TopLevelRobustness.lean`)

Language model: as paxos (twelve programs' `Assumptions`). Each premise below is
`∀ G L, letI := heapAt G L; C remoteGF`:

| class | kind | file |
|---|---|---|
| `github_com.rs.zerolog.InitHyp` | InitHyp (names only) | `Dsverify/Proof/github_com/rs/zerolog/Init.lean` |
| `github_com.gogo.protobuf.proto.InitHyp` | InitHyp (names only) | `.../gogo/protobuf/proto/Init.lean` |
| `github_com.gogo.protobuf.proto.Hyps` | hypotheses (RegisterEnum/Type/File) | `.../gogo/protobuf/proto/Spec.lean` |
| `github_com.gogo.protobuf.gogoproto.InitHyp` | InitHyp (names only) | `.../gogo/protobuf/gogoproto/Init.lean` |
| `github_com.go_redis.redis.v8.InitHyp` | InitHyp (names only) | `.../go_redis/redis/v8/Init.lean` |
| `os.signal.InitHyp` | InitHyp (names only) | `Dsverify/Proof/os/signal/Init.lean` |
| `math.rand.InitHyp` | InitHyp | `Dsverify/Proof/math/rand/Init.lean` |
| `github_com.rs.zerolog.Hyps` | hypotheses (events, ParseLevel, SetGlobalLevel, New) | `.../rs/zerolog/Spec.lean` |
| `math.rand.Hyps` | hypotheses (`rands`: NewSource/New/Rand.Intn; `Intn`) | `Dsverify/Proof/math/rand/Spec.lean` |
| `os.signal.NoSignals os.signal.quietSigs` | environment assumption | `Dsverify/Proof/os/signal/Spec.lean` |

### QuePaxa (`Dsverify/Spec/raxos/examples/quepaxanet/TopLevelRobustness.lean`)

Language model: as paxos (twelve programs). Premises:

| class | kind |
|---|---|
| `gopkg_in.yaml_v2.InitHyp`, `github_com.go_redis.redis.v8.InitHyp`, `io.ioutil.InitHyp`, `encoding.gob.InitHyp`, `google_golang_org.grpc.InitHyp`, `google_golang_org.grpc.codes.InitHyp` | InitHyp (names only) |
| `math.rand.InitHyp` | InitHyp |
| `qv : raxos.hyp.QpVocab remoteGF` | data (`GrpcVocab`, `MapVocab`) |
| `raxos.hyp.PbHyp` (Marshal, Unmarshal), `RandHyp` (Seed, Intn), `UtcHyp`, `SortHyp`, `PrintlnHyp` | hypotheses |
| `raxos.hyp.grpc.GrpcHyp qv.grpc` (NewServer, RegisterService, Serve, WithInsecure, Dial, Invoke) | hypotheses over the vocabulary |
| `raxos.hyp.grpc.GrpcWorldHyp qv.grpc` (world_alloc) | ghost-state hypothesis |
| `raxos.hyp.sync.MapHyp qv.map` (ivt, own_timeless, own_zero, Load, Store, Delete) | hypotheses over the vocabulary |

(all in `Dsverify/Proof/raxos/Hyp.lean` except the `InitHyp`s, each in its package's
`Dsverify/Proof/<pkg>/Init.lean`).

## Finding: the `Intn` premise (rabia `math.rand.Hyps.Intn`, QuePaxa `raxos.hyp.RandHyp.Intn`)

Both state the package-level `rand.Intn(n)` as

    ∀ n, 0 < sint.Z n → {{ isPkgInit pkg_id.math.rand }} @! math.rand.Intn #n {{ x, RET #x; ⌜0 ≤ x < n⌝ }}

(`Dsverify/Proof/math/rand/Spec.lean`, `math.rand.Intn.spec`; `Dsverify/Proof/raxos/Hyp.lean`,
`raxos.hyp.math.rand.Intn.spec`). It cannot be built:

1. Since Perennial 47ec64a9d (commit 2cd4d8e8, "math/rand: translate and prove the top-level ...
   Intn"), `Intn` is translated: `math.rand.Assumptions`, part of every rabia and QuePaxa
   program's `Assumptions` (rabia's `consensus`, QuePaxa's `replica/src` and `quepaxanet` import
   math/rand), has `Intn_unfold : FuncUnfold Intn [] Intn.impl` and
   `globalRand_unfold : FuncUnfold globalRand [] globalRand.impl`. `Intn.impl` is
   `globalRand().Intn(n)`; `globalRand` (Perennial's trusted model) does an atomic `Load` of the
   package variable `globalRandGenerator` (then a `CompareAndSwap` if it is nil).
2. The premise's `isPkgInit pkg_id.math.rand` is the main tree's instance
   `Perennial.mathRand_is_pkg_init_inst := define_is_pkg_init iprop(True)`
   (`Proof/math/rand/Base.lean`; ea51674d0f kept it: "The main tree keeps its own True instance
   for math.rand"). So the precondition holds no resource for `globalRandGenerator`'s cell.
3. Perennial's proved spec (`Perennial/Spec/math/rand/Intn.lean`, proved in
   `Perennial/Proof/math/rand/Intn.lean` from `globalRand.spec` and `Rand.Intn.spec`) has the same
   shape but over Perennial's own instance, `define_is_pkg_init isInit`, where `isInit` is the
   invariant that owns `globalRandGenerator` (`sync.atomic.ownPointer`) and records the generator
   (`Perennial/Proof/math/rand/Base.lean`). The premise is that spec with `isInit` replaced by
   `True`: it is not derivable from it, and it is false of the translated body (it claims `Intn`
   safe from any state, including one where math/rand's initializer never allocated
   `globalRandGenerator`; there the body's `Load` is stuck). An axiom stating it would not be the
   library's real behaviour, so no instance was written.

Before 47ec64a9d, `Intn` was names only and the premise was satisfiable like the other names-only
specs. Checked in Lean (scratch module `Dsverify/Scratch/InstancesCheck.lean`, commit d9387d4a45, built on fk-lean1
and dropped): (1) and (2) above, as `rfl`/field projections, on Lean's axioms only.

The fix (not done here, it changes the main tree's math.rand instance and so every statement over
it): give `pkg_id.math.rand` Perennial's `isInit` instance in the main tree (`Proof/math/rand/Base.lean`
drops its `True` instance and imports `Perennial.Proof.math.rand.Base`; `Proof/math/rand/Init.lean`
becomes Perennial's `math.rand.initialize'.wp_proof`). Then:
- both `Intn` fields are **discharged** by Perennial's `math.rand.Intn.wp_proof` (with
  `globalRand.wp_proof`, `Rand.Intn.wp_proof`) -- proved, no axiom beyond Perennial's trusted
  `globalRand`/`runtime_rand` models;
- the kits' `math.rand.InitHyp` is **discharged** by Perennial's `initialize'.wp_proof`.
  (It is dischargeable even today, with the `True` fact: the main tree proves exactly that
  `wp_initialize'` in `Proof/math/rand/Init.lean`, over Perennial's translated initializer, no
  axiom; the part cannot import that file only because `Proof.runtime.PkgInitExt` and
  `Net.Proof.runtime.PkgInitExt` declare the same names, so gen-init would generate it into the
  part, math.rand moving from the kits' `HYP_INITS` to `MAIN`. `etc/dsv/rabia.py`'s reason,
  "Perennial leaves its initializers untranslated", is out of date since 47ec64a9d.)
- the main tree's `rand.Int63n.wp_proof`/`rand.Float64.wp_proof` axioms (precondition without
  `isPkgInit`) have the same problem for `Int63n` (translated since 47ec64a9d) and should go the
  same way.
Watch the name: Perennial now declares `Perennial.math.rand.Intn.spec`, the same name as
`Dsverify/Proof/math/rand/Spec.lean`'s; a module importing both fails (dups). Rename the part's
(e.g. into rabia's namespace) or replace it by Perennial's.

Changing the premise (strengthening it to Perennial's instance) changes the landed statements:
under the STANDING RULE that needs Upamanyu's sign-off on #8.

## Discharge candidates

Now (proved specs only, Perennial 47ec64a9d's translated initializer): rabia's and QuePaxa's
`math.rand.InitHyp` (as the main tree's `Proof/math/rand/Init.lean`, generated into the part).
After the fix: rabia `math.rand.Hyps.Intn` (a field;
the class goes once `rands` does too, see below), QuePaxa
`RandHyp.Intn` (a field; `RandHyp.Seed` stays, `Seed` is names only). rabia's `math.rand.Hyps.rands`
names `Rand.Intn` (now translated and proved in Perennial, over Perennial's `isRuntimeRand`), but
also `New`/`NewSource` (names only): not dischargeable yet.

No other premise was examined for discharge: the kits stopped at the finding.

## For the instance modules (when the finding is fixed)

- Tiers: a module outside `Spec/`/`Proof/` roots is `base` (tier-check: base imports no spec/defs/
  proof); the scratch module here was flagged (`base->defs`). An instance module imports proofs and
  links, so it must be a linking module: e.g. `Dsverify/Proof/<kit>/.../InstancesLinked.lean`
  (`*Linked` is linking) or listed in `etc/tier-linking.txt`.
- Trust base: `proof_roots` takes `Link`, `MainLinked`, `Results`, `TopLevelRobustness` as roots;
  an `InstancesLinked` module is not a root and no statement or proof imports it, so its local
  axioms stay out of `.lake/tcb.json`. The gates build it (the `Dsverify` lib's glob `Dsverify.+`
  is in `defaultTargets`).
- `InitHyp`: `etc/dsv/README.md` forbids an `instance` of an `InitHyp` anywhere; build them as
  `theorem`s (`⟨fun g h => ...⟩`), not `instance`s.
- Names-only `InitHyp`s: the precedent for local axioms is the main tree's retired
  `opaqueInitsOk` (`∀ v ∈ [X.init, ...], {{ True }} v #() {{ RET #(); True }}`) and `initFuncsOk`
  (`∀ f ∈ [init.«k», ...], {{ True }} @! f #() {{ RET #(); True }}`), commit 9c90920def and
  successors; the walk is `wp_package_init`, `wp_auto`, one `wp_apply` per initializer.
- Local axioms over names-only functions are stated, as the repository's interim axioms are, for
  every Go context (`GoGlobalContext`, `go.Semantics`); they are satisfiable only in the contexts
  where the names resolve to Go's code, which is the trust the main tree's axioms already take.

## Checks (head of the branch)

tier-check `--check`: ok at the final head (the scratch module failed it, `base->defs`, and is
dropped); `gen-init --check`: 273 files up to date; `proof_roots.namespace()`:
`Perennial.EtcdGrove.`; dups (`dups.py` over the Dsverify roots' closure with Perennial
47ec64a9d): 4, the regex's known false positives (`go.inductive`, `is`, `of`, `per`).

fk-lean1 had no Perennial 47ec64a9d: added as `/home/ubuntu/eg/perennial-47ec64a9d` (worktree of
its perennial.git, `.lake` copied from ccfeb3895, `lake build` ok, 1513 jobs). Locally,
`/shared/perennial-47ec64a9d` is a source worktree (not built), for the Python checks.
