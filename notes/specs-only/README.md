# The specs-only branch: a complete set of intermediate specs for etcd

Branch `specs-only`, off `lean` at `037bf21c75` (2026-11-09). The user's request, in short:

> Come up with new intermediate specs for all of the parts of etcd we have already verified, as a
> search problem in which backtracking (proving the "wrong" intermediate spec, then strengthening it
> and re-proving when a new feature arrives) is the cost to avoid. The goal is to verify all of etcd,
> including leases, authorization, durability, compaction, snapshots. Produce a specs-only branch:
> ONLY specs, no proofs, over **opaque** predicates (and opaque ghost-name types) whose meaning is
> fixed by the specs of the top-level functions. Work top-down from a linearizability spec:
> determine what must hold lower down to enable each proof higher up. Judge each spec for
> **completeness** against all its users, for **soundness** by an informal proof plan (in terms of
> resources) of the spec from the lower-level specs, kept as block comments in the Lean files, and
> for **locality** by the spec skill's guidance. Drive completeness with **minimal Go snippets** of
> client usage: an agent given a batch of related specs and the snippets should agree that the
> snippets are provable (panic-free) from the specs, and an agent scanning the users of that API
> should agree that the snippets capture every aspect the callers rely on. Judge each batch of
> interacting functions with an agent separate from other batches.

What the branch holds:

- the Goose translations (`Code/`, `GeneratedProof/`, `TrustedCode/`, `ManualProof/`, `GooseLang/`,
  `Bbolt/`) and the two extension preludes (`Proof/DurablePrelude.lean`, `Proof/OsFsPrelude.lean`),
  unchanged: the specs are about this code;
- `Spec/`: the new specs (below). The old `Spec/`, `Proof/`, `interface/` and the parts
  `RaftWitness/`, `PorcupineDag/` are deleted on this branch;
- `examples/specreq/`: the Go requirement snippets (below);
- `notes/specs-only/`: this plan, the batches, the requirement hand-offs (`req/`) and the reviews
  (`reviews/`).

The old specs and proofs, for reference (read-only, never edit): the worktree
`/home/ubuntu/etcd-grove/.claude/worktrees/specs-ref` (detached at `037bf21c75`), or `git show
037bf21c75:<path>`. Its `notes/` (STATUS, decisions, the plans) record why each old spec is the
way it is; its `issues/`, `nonissues/` the known bugs and preconditions. The skill
`.claude/skills/spec/` (PRINCIPLES.md, examples/) is the guidance on what makes a good spec; it
applies here in full, except what is about proofs, links, the trust-base scripts and landing.

The Go code: the pinned sources are in the Go module cache (from `examples/`, `go list -m -f
'{{.Dir}}' go.etcd.io/etcd/server/v3`):

| module | directory |
|---|---|
| etcd server, client, api, pkg, cache (`a4d2bb17`) | `/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/{server,client,api,pkg,cache}/v3@v3.0.0-20261107170612-a4d2bb1720b9` |
| raft (`565c2bd`) | `/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/v3@v3.0.0-20261028061729-565c2bda9e6d` |
| bbolt (`743299d`) | `/home/ubuntu/go/pkg/mod/github.com/upamanyus/bbolt@v0.0.0-20261104031046-743299d8cec8` |
| this repository's examples (users: txnlin, k8s, raft kv, lintest, ...) | `examples/` |

The Lean translation of a function is in `Code/<pkg>/*.lean` (search for the function's name);
which functions are translated with bodies is in `Code/<pkg>.toml`.

## What a spec is here

### Files

- `Spec/<pkg>/Api.lean` (big packages may split it: `Model.lean` for the pure model, `Api.lean`
  for the resources and laws): the package's **vocabulary**:
  - ghost-name types, **opaque**: `opaque KVNames : Type := Unit`;
  - pure models of the package's abstract state, **transparent** (`structure`, `inductive`,
    `def` by recursion): the model is the meaning of the specs, so it is spelled out;
    no `theorem`s about it (a fact the clients need is a law, below);
  - resource predicates, **opaque**: `opaque etcdKV (γ : KVNames) (σ : KVState) : IProp GF :=
    iprop(True)` (the body is only Lean's inhabitation witness; nothing can unfold it);
  - **laws**, as obligations, never axioms: `def etcdKV_excl.spec : Prop := ∀ γ σ σ', etcdKV γ σ ∗
    etcdKV γ σ' ⊢ False` (persistence, timelessness, agreement, exclusivity, fractions, the
    intro/elim laws clients use). A law is part of the API exactly like a function's spec: the
    implementation proves it, a client uses it.
  - the block comment at the top: what each predicate means (in words, and the **intended
    realization**: how the package's proof would define it from its callees' vocabulary and its own
    ghost state and invariants), and the list of requirement snippets of the API.
- `Spec/<pkg>/<fn>.lean`: one function's Hoare triple, `def <fn>.spec : Prop` (`<Type>__<Method>`
  file names as before: `kv__Put.lean`, `def kv.Put.spec`). Its block comment (`/- ... -/`
  before the `def`; a docstring `/-- -/` on the def says what the triple says, in words):
  - **Users**: the Go call sites (file:line in the pinned source, grouped by pattern; for a
    many-caller function, the patterns with one example each) and the snippet covering each
    pattern;
  - **Proof sketch**: the resources the proof holds and how it gets them (the invariants it opens,
    the ghost state it updates, the callee specs it applies, in order, with what each gives); the
    linearization point of an atomic update; for a loop or a goroutine, what it carries;
  - **Changes**: from the old spec (`specs-ref`'s file, if any): what was relaxed, strengthened or
    restated, and why; "unchanged" is a fine answer;
  - **Margin**: where the post is weaker than what the code guarantees.
- No `theorem`, `axiom`, `sorry`, `instance` or proof anywhere. Every obligation is a `def ... .spec
  : Prop`. Something that cannot be stated without a proof (a typeclass instance) is stated as a law
  instead.
- A trust boundary (a library this repository does not verify: grpc, protobuf, zap, os, ...) gets
  its specs in `Spec/<its pkg>/` in the same form; its block comment says they are assumed, and why
  they are true of the library (its code or documentation). Perennial's own specs of the standard
  library (`sync`, `context`, `time`, ...: `Perennial.Proof.*`, the dependency) may be imported and
  cited; they are not ours to restate.

### Lean conventions

```lean
/- <block comment: Users / Proof sketch / Changes / Margin> -/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3   -- the package's translation
public import Spec.PkgInit.go_etcd_io.etcd.client.v3     -- `isPkgInit` of the package (generated)
public import Spec.go_etcd_io.etcd.client.v3.Api         -- its vocabulary (and its callees' Api
                                                          -- only if the statement mentions them)
@[expose] public section
noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3          -- the package's namespace (table below)

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- <what the triple says> -/
def kv.Put.spec : Prop :=
  ∀ (kv : Loc) ..., ⌜...⌝ →   -- pure premises go inside {{ }} as ⌜⌝ conjuncts, preferably
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ... }}
    (App (App (Val (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Put"))
      (Val #ctx)) ...)
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ... }}
end spec
end ClientV3
end EtcdGrove
end Perennial
```

Opaque predicates take `variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
[hG : HeapGS HasLC.hasLC GF]` (`HeapGS` needs the first three).
`isPkgInit pkg_id.X` needs `Spec.PkgInit.X` (generated by `etc/gen-specs-pkginit.py`, one module per
translated package; its user part is the opaque `PkgInit.pkgInitDef pkg_id.X`: a fact about a
package's globals after initialization is a law `X.init.spec` of the package that needs it). Look at the old
spec of the function (`specs-ref`) for the program expression of a method or function call (the
`@!!` form and the argument currying), and at `Spec/smoke/Api.lean` for a compiled example of all of
the above. Package namespaces: the Go package's last path elements in UpperCamel
(`ClientV3`, `Concurrency`, `Leasing`, `Recipes`, `Cache`, `BTree`, `V3rpc`, `EtcdServer`, `Read`,
`Apply`, `Txn`, `Lease`, `Auth`, `Mvcc`, `Backend`, `Schema`, `Bbolt`, `BboltCommon`, `Freelist`,
`Raft`, `RaftPb`, `Tracker`, `Quorum`, `ConfChange`, `Rafthttp`, `Membership`, `Snap`, `Wal`,
`Cindex`, `Wait`, `IdUtil`, `Notify`, `Schedule`, `Adt`, `TraceUtil`, `EtcdServerPb`, `Grpc`,
`Proto`, `Zap`, ...); a new one: pick it the same way and list it in your batch's report.

Build: `etc/specs-build.sh --dir Spec/<pkg>` (or module names). It serializes `lake build` across
agents sharing this worktree (never run `lake build` directly). Every file of a batch must build.
Specs that do not type-check are not specs.

### Shared vocabulary: who owns what

- The **top-level model** of what a client observes (`EtcdState`: the revisioned KV with its
  compaction, the leases, the auth state, the cluster's members) and the client's resources
  (`isClient`, `etcdState`) are the anchor batch's (W0): `Spec/go_etcd_io/etcd/api/v3/Model.lean`
  (the pure model; shared by every layer that wants it: a server layer may import it) and
  `Spec/go_etcd_io/etcd/client/v3/Api.lean`.
- Ambient boundary libraries, owned by W0 so that every batch shares one vocabulary: the logger
  (`Spec/go_uber_org/zap/Api.lean`: a persistent `isLogger`), metrics, and the context (`Spec/context`
  only if Perennial's context spec does not serve).
- grpc (client connections and server) and protobuf's `proto`: batch 2a's.
- A package's vocabulary is its own batch's. A batch never edits another batch's files: it writes
  what it needs from them in `notes/specs-only/req/<their pkg path with _>.md` (append a section
  headed by your batch id): the need in plain terms, the Go snippet of the use, and which of your
  proof sketches depends on it. The callee's batch reads its `req/` file first.

### Abstraction and locality

The spec skill's principles hold. The ones this effort turns on:

- **Opaque, abstract vocabulary.** A spec mentions its package's opaque predicates and pure models,
  and a callee package's vocabulary only where the caller's *clients* must see it (a server
  constructor taking a backend handle). No implementation records, ghost names of the
  implementation, internal namespaces, or callee-internal predicates in a statement.
- **One spec per function, general enough for every mode** (auth on and off, leases, compaction,
  restarts, snapshots, membership changes): a mode is part of the state, not a second spec.
- **Relax what the old specs assumed only for the proof's convenience** (a put without a lease, a
  first start only, no compaction, a size bound that the code turns into an error rather than a
  panic). When the code returns an error, the spec says so (an error disjunct the caller sees), not
  a premise that rules the input out. A premise stays only if the code needs it (it panics or hangs
  otherwise) or a caller cannot do without the restriction; say which.
- **Durability, crashes and restarts are inside the spec**, where the code handles them: a server's
  durable state is client-owned ghost state split as in raft's durable node API (the persistent
  part the client's choice is about), so a restart is a fresh volatile half over it.
- **Linearizability is the caller's atomic update in the triple** (TaDa, not HoCAP).
- **Every premise has a source the caller sees**: a spec or a law of an API.

## Requirement snippets (Go)

For each API (a batch's exported functions), the batch writes minimal Go snippets of how its users
use it, in `examples/specreq/<alias>/` (Go package `<alias>`, e.g. `examples/specreq/clientv3kv/`;
one or a few files per API). They are the completeness requirements: each captures one aspect the
callers rely on, much smaller than the callers' code (one simple example per usage pattern, not
one per call site).

- Each snippet is a function with a header comment:

  ```go
  // REQ clientv3kv/put-then-get: a read after an acknowledged write sees it (or a later write).
  // Users: client/v3/concurrency/stm.go:NNN, examples/etcd/txnlin/..., k8s etcd3 store.go:NNN
  // Assumes: no other client writes key k (an invariant the caller keeps).
  // Specs: kv.Put.spec, kv.Get.spec; laws: etcdState_..., ...
  func ReqPutThenGet(ctx context.Context, c *clientv3.Client, k string) { ... }
  ```

- **What the caller relies on is an explicit `panic` on its violation** (`if len(resp.Kvs) != 1 {
  panic("put-then-get: lost write") }`), so that "the snippet is panic-free under its stated
  assumptions" is exactly "the specs give what the callers rely on". A snippet that only calls the
  API checks only that the preconditions can be met and the call does not panic, which is also a
  requirement worth one snippet.
- Errors the callers handle are handled as the callers do (retry, return, ignore); errors they treat
  as impossible are `panic`s, with the assumption that makes them impossible in `Assumes:`.
- They must compile: `cd examples && go vet ./specreq/<alias>/`. A package that `examples` cannot
  import (an `internal` package: bbolt's `internal/common`, ...) gets its snippets with `//go:build
  ignore` at the top; they must still be gofmt-clean Go that would compile in the package
  (`gofmt -l` prints nothing).
- Running them is optional. If a snippet needs a running cluster to be meaningful, it may be a
  `_test.go` using `go.etcd.io/etcd/tests/v3/framework/integration` (as `examples/` already does);
  say so in its header.

## The review of a batch

Three judgments, the first two by agents separate from the author and from other batches:

1. **Provability (soundness, snippets)**: given the batch's specs, vocabulary and snippets, and the
   callee specs the sketches cite: (a) each snippet is provably panic-free from the specs under its
   stated assumptions (the reviewer sketches the proof: which spec at which call, which law, what
   invariant the snippet's caller would keep); (b) each spec is true of the Go code (no panic under
   its pre, the post holds on every path, including errors) and its proof sketch is plausible from
   the cited callee specs (a resource it uses comes from somewhere; an invariant's content is
   stated; an atomic update fires once); (c) nothing vacuous (a predicate whose laws all hold at
   `True`, a disjunct always true).
2. **Completeness (users)**: scan every user of the batch's API (the pinned etcd, raft, the examples,
   the Kubernetes code in `Code/k8s_io` and its Go source) and classify the uses into patterns; each
   pattern is covered by a snippet, and each spec's pre is one each user can establish (with the
   values it actually passes: its context, its options) and its post gives what each user needs
   next.
3. **Locality and abstraction**: by the spec skill (the author's, and both reviewers note what they
   see): footprint-only specs, no implementation vocabulary, no unneeded premise, laws for what
   clients would otherwise unfold.

Reports go to `notes/specs-only/reviews/<batch>-<provability|completeness>-<round>.md`; the author
repairs; a second round only if the first found a hard-rule problem. A batch is done when both
reviewers have no first-tier finding left (or the remaining ones are recorded as open questions for
the user in the batch's section of `batches.md`).

**Integration** (after all waves): for each batch, a provability reviewer re-checks every proof
sketch against the callee specs as they finally are (not the `req/` notes), and the mismatches are
repaired (in the callee if the need is real, in the caller if the sketch was wrong).

## Batches and waves

`notes/specs-only/batches.md`.
