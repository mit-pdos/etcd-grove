# Changes to Perennial this repository needs

A running list of the Perennial changes (Goose, the standard-library models and specs, the proof
framework) that proofs here are waiting on or working around. Each is a general change, designed
and reviewed on its own on a branch off Perennial's `lean` and landed by Perennial's workflow
(CLAUDE.md, "Changes to Perennial"); never a change shaped by one proof. Add an entry when a
proof hits a limitation (with the local workaround); move it to "Landed" with the Perennial commit
when the pin reaches it, and drop the workaround.

Each entry: what is missing, who needs it, the workaround here, the proposed change, status.

Started 2026-10-22 with the Kubernetes etcd3 store survey (`notes/k8s-etcd3-plan.md`, branch
`k8s-etcd3-goose`, `notes/k8s-etcd3-goose.md` there). Earlier limitations are recorded where
they were found (`notes/STATUS.md`, `notes/decisions.md`) and not yet collected here.

Perennial pin at the start: `a39a3d14c` (Perennial's `lean` head on 2026-10-22).

## Open

### `append` does not model `growslice`'s `maxAlloc` limit (2026-11-14, branch `wal-small14`)

Go's `append` panics ("growslice: len out of range") once the new capacity times the element size
passes `maxAlloc` (`2^48` on linux/amd64); Perennial's `go.append` assumes only that the new length
does not overflow an `int` (`sumAssumeNoOverflowSigned`). A slice built by appends is therefore
bounded only by `2^63` in the model, and `sort.Strings.spec` needs at most `2^62` elements (Go's
`heapSort` overflows past that). Local workaround: the trusted `File.Readdirnames.impl` of the
`LinuxFs` part assumes fewer than `2^44` names before each append (`notes/wal-fsext-plan.md`, W7-W12
log, third session; pending the user's review). General fix: `append` (and `make`) assume
`newLen * elemSize ≤ maxAlloc`, as they assume the overflow, and `wp_slice_append` returns the bound.

### An indexed handshake idiom (2026-11-13, branch `wal-cut2`)

- **The gap.** `Chan/Idioms/Handshake` hands the sender one proposition `Q` for every exchange, so a
  protocol whose returned resource depends on the round (the WAL's file pipeline: file `n` for the
  claim on the name of file `n + 1`) cannot be stated over it.
- **Local workaround.** `LinuxFs/Proof/.../storage/wal/HandshakeN.lean`: `isHsn γ ch P Q`, `P` and `Q`
  indexed by the exchange, each side's count a ghost-variable half (`hsnSnd`, `hsnRcv`).
- **Proposed change.** Move it to `Chan/Idioms/` (the plain handshake is the case of constant
  `P`, `Q` with the counts dropped).

### `notCrashed` before a step: `wp_notCrashed_acc`, `wp_atomic_nc` (2026-11-13, branch `wal-ncau`)

- **The gap.** The generation's `notCrashed` is in the bounded language's state interpretation
  (`gooseBstateInterp`, `Lifting.lean:752`), and no lifting lemma lets the update before a step use
  it (as `wp_ext_acc` does for an extension's state). An invariant whose crash branch is
  `crashed ∗ tok` (the WAL's `walInv`) can then be opened only inside a physical step's own proof,
  not by a client's atomic update opened (`wp_atomic`) around an `os` call's step.
- **Who needs it.** Every WAL unit over `fsExt` that opens `walInv` in a client update nested in an
  `os` spec's atomic update (`notes/wal-fsext-plan.md`, W1 log, fourth and fifth sessions); also the
  older entry "No WP step lemma refutes the generation's `crashed`" below (its `wp_crashed_elim`
  follows from `wp_notCrashed_acc` and `notCrashed_crashed`).
- **Local workaround (proved, no axiom).** `GooseLang/Ext/Fs/NotCrashedAcc.lean`: for a non-value `e`,
  `wp_notCrashed_acc : (notCrashed -∗ |={E}=> notCrashed ∗ WP e @ s; E {{Φ}}) ⊢ WP e @ s; E {{Φ}}`,
  and `wp_atomic_nc [Atomic ↑s e] : (notCrashed -∗ |={E1,E2}=> notCrashed ∗ WP e @ s; E2 {{v, |={E2,E1}=>
  Φ v}}) ⊢ WP e @ s; E1 {{Φ}}` (iris's `wp_atomic`'s proof, with the token taken out of the first
  step's state interpretation and put back). Over them, `osAUnc`/`wp_aunc_step`
  (`LinuxFs/Proof/os/SharedAu.lean`).
- **Proposed.** Both lemmas in Perennial's `GooseLang/Lifting.lean`, beside `wp_ext_acc` (they use
  only `goose_bstateInterp_eq` and iris's `wp_unfold`); generic, nothing about `fsExt`.
- **Status.** Recorded; the local copies go when the pin has them.

### No translation of `hash/crc32`, `bufio`, `path/filepath`; no models of `io.ReadFull`/`io.Copy`, `fmt.Sscanf`, `strings.HasSuffix` (2026-11-13, branch `wal-fsext-translate`)

etcd's real WAL over `fsExt` (the part `LinuxFs/`) calls `crc32.MakeTable(crc32.Castagnoli)` and
`crc32.Update` (`pkg/v3/crc`), `bufio.NewReader` and `*bufio.Reader`'s methods (`fileutil.FileBufReader`,
the decoder), `filepath.Join/Base/Dir/Clean/Ext/Abs/Walk`, `io.ReadFull` (decoder.go:117), `io.Copy`
(repair.go:81), `fmt.Sscanf` (util.go:112, `parseWALName`) and `strings.HasSuffix`. Perennial
translates none of the first three (the default root `Perennial` names modules that do not exist),
and has the others names only. Workaround here: names-only translations in the part
(`LinuxFs/Code/{hash/crc32,bufio,path/filepath}.toml`, project etcd's part). Proposed: Perennial
translations with bodies (crc32's generic table path, bufio's `Reader`, filepath over `path`'s
lexical functions and `os` for `Abs`/`Walk`) and specs; `io.ReadFull`/`io.Copy` with bodies over the
`Reader` interface. Not yet proposed; the trust decision is open (no model was written).

**`hash/crc32` (2026-11-13, branch `wal-leaf-enc`): a trusted model, pending the user's review.**
`LinuxFs/TrustedCode/hash/crc32.lean` models `MakeTable` and `Update` (`trusted` in
`LinuxFs/Code/hash/crc32.toml`) as Go's portable code: `MakeTable(Castagnoli)` allocates the table of
`simplePopulateTable(Castagnoli)` (a Lean constant computed bitwise, `castagnoliTableArr`), any other
polynomial panics; `Update` is `simpleUpdate` reading the table it is given. The pure vocabulary is
`LinuxFs/Spec/hash/crc32/Model.lean` (`crc32c`, with the check vector proved by kernel evaluation,
table-driven and bitwise). Evidence: `examples/stdlib/crc32/crc32_test.go` (go1.27.3 linux/amd64:
the whole table, the check vector, 20,000 random inputs and splits against Go's SSE4.2 path).
Deviations, documented in the model: other polynomials panic; `MakeTable(Castagnoli)` allocates a
fresh table where Go returns one shared pointer. **Proposed upstream**: the same model in Perennial's
`TrustedCode/hash/crc32.lean` (with `crc32.toml`'s `trusted`), generalized to every polynomial by a
GooseLang `simplePopulateTable` (or by translating `crc32_generic.go` with bodies and trusting only
`Update`'s dispatch to it), with `IEEE` alongside; then this part's names-only `hash/crc32` and the
local model go.

### `io.ReadFull`/`ReadAtLeast` and `binary.Read`'s fast path without bodies (2026-11-13, WAL leaf specs, branch `wal-leaf-std2`)

- **Missing.** Perennial's `io.toml` translates `io` names-only for `ReadFull`/`ReadAtLeast`, and
  `encoding/binary.toml` only the byte orders (`Read` goes through `reflect`), so neither call can be
  stepped. The WAL's decoder calls both (decoder.go:117 `io.ReadFull(fileBufReader, data)`,
  decoder.go:227-231 `binary.Read(r, binary.LittleEndian, &n)` of an `*int64`).
- **Workaround here.** Two trust-boundary axioms, pending the user's review:
  `io.ReadFull.wp_proof` (`Spec/io/ReadFull.lean`, over a stream reader `io.readerStream`,
  `Proof/io/ReaderStream.lean`) and `binary.ReadInt64LE.wp_proof` (`Spec/encoding/binary/
  ReadInt64LE.lean`, over the triple of its `io.ReadFull` call). **Why not a part-local translation
  (as `bufio`'s):** a part may replace a package only if no module it imports reaches Perennial's
  copy (the part's `os`/`io/fs` replace Perennial's because the part also has its own importers of
  them). `io` is imported by Perennial's `fmt`, `strings`, `bytes`, `bufio`'s part copy, ..., which
  the WAL's translation imports: a `LinuxFs/Code/io.lean` declaring `Perennial.io.ReadFull` would
  clash with Perennial's `Perennial.Code.io` in every such module, and a function's `FuncUnfold` can
  come only from its package's own `Assumptions`. So the bodies have to come from Perennial.
- **Proposed.** (1) `io.toml`: translate `ReadAtLeast` and `ReadFull` with bodies (`ErrShortBuffer`,
  `EOF`, `ErrUnexpectedEOF` already are), and prove in `Perennial/Proof/io/` the spec of
  `Spec/io/ReadFull.lean` (the stream-reader vocabulary `io.readerStream`/`io.readFullOk` moves there
  with it): a loop over `r.Read(buf[n:])` with the invariant "`ys` delivered, `buf` is `ys ++ rest`,
  `S (r0 ++ ys)`", the exit's error comparison `err == EOF` an interface comparison of
  `*errorString`s (no panic). (2) `encoding/binary.toml`: translate `Read`, `intDataSize` and
  `decodeFast` with bodies and `reflect` names-only (the reflect fallback is unreachable for the
  fast-path types, as `Read`'s spec premise `intDataSize data ≠ 0` would say), and prove
  `ReadInt64LE`'s spec (and `ReadUint64`'s) over them; or a trusted model of `Read` restricted to the
  fast path, if goose cannot translate the type switches. Then the two axioms here become
  `theorem`s with the same statements (the specs are already over Perennial's names). Not yet
  proposed.

### Operations on untyped rune constants have no step (2026-11-13, WAL leaf specs, branch `wal-leaf-std2`)

- **Missing.** Goose emits `Separator == '/'` (`GoOp GoEquals go.untypedRune`) and `string(Separator)`
  (`Convert go.untypedRune go.string`) of `internal/filepathlite`'s untyped constant as run-time
  operations, and Perennial's semantics has no rule for either (`UntypedIntSemantics` converts untyped
  integers to the integer types only). Go evaluates both at compile time.
- **Workaround here.** A hypothesis class `UntypedRuneSemantics`
  (`LinuxFs/Proof/internal/filepathlite/UntypedRune.lean`, like `UntypedIntToFloat64Semantics`):
  equality of untyped integers, and `string(c)` an uninterpreted string that is the one byte `c` for
  ASCII `c`; `filepathlite.FromSlash`/`Base` (and what calls them) take it as an instance. To be
  added to `etc/gen-link.py`'s `SEM_PREMISES` when the package is linked. **Pending the user's
  review** (a semantic assumption).
- **Proposed.** Goose folds constant expressions of untyped constants (the language's "Constant
  expressions"), or Perennial's `UntypedIntSemantics` gains the two steps. Not yet proposed.

### `Sprintf`'s `%0Nx`, `Sscanf`'s `%0Nx` of a `uint64`, `Time.Format` (2026-11-13, WAL leaf specs, branch `wal-leaf-std2`)

- **Missing.** Perennial's model of `Sprintf` (`Perennial/TrustedCode/fmt.lean`) formats `%d`, `%v`,
  `%0Nd` and `%x` exactly, but from a `%0Nx` on its output is arbitrary (`intVerb` accepts a width
  only before `d`); `Sscanf` has no model (names-only); `time.Time.Format` has no body. The WAL's
  `walName` is `Sprintf("%016x-%016x.wal", seq, index)` (util.go:117), `parseWALName` scans it back
  with `Sscanf(str, "%016x-%016x.wal", &seq, &index)` (util.go:112), and `cleanupWAL` names the
  broken directory with `time.Now().Format("20060102.150405.999999")` (wal.go:299).
- **Workaround here.** Trust-boundary axioms, pending the user's review: `fmt.SprintfWalName`,
  `fmt.SscanfWalName` (`Spec/fmt/`, the pure model `Proof/fmt/WalName.lean`: `walNameStr`,
  `scanWalName`, with the round trip proved) and `time.Time.Format` (some string). Go evidence:
  `examples/stdlib/fmtwalname/` (the Lean models transcribed and compared with `fmt` on edge values,
  100,000 random pairs and 200,000 random strings) and `examples/stdlib/timeformat/` (no panic on
  200,000 random layouts and times, any location).
- **Proposed.** (1) The `Sprintf` model's `intVerb` returns the verb too and accepts `%0Nx` as it
  accepts `%0Nd`; `formatHex` takes the width and pads with zeros after the sign, as `%0Nd` does
  (Go's `fmtInteger` with the `zero` flag: `Sprintf("%05x", -255)` is `"-00ff"`); the spec relation
  `fmt.SprintfOut` gains the case. Then `SprintfWalName` is a corollary of `wp_Sprintf` (the
  argument list is two `uint64`s, `fmt.ArgsWf`). (2) A model of `Sscanf` for a format of literal
  bytes and `%x`/`%0Nx`/`%d` of unsigned integers, transcribing `fmt/scan.go`'s `doScanf` on those
  verbs (`SkipSpace` over-approximated as here: an input byte that may begin a space makes the rest
  arbitrary), with `scanWalName` as its instance. (3) A trusted model of `Time.Format` returning an
  arbitrary string (Perennial's `arbitraryString`), so its spec is proved. Not yet proposed.

### `sort.Sort`'s spec as a function of its input (2026-11-09, specs-only batch 3b)

Perennial's `sort.Sort`/`sort.Slice` specs say only that the result is some sorted permutation of
the input. Go's sort (pdqsort) is deterministic: the output is a function of the input slice and
the comparator. etcd's sorted ranges (`txn.sortRangeResults`) need the reply to be a function of the
store, so that a writing transaction's answer is fixed at commit (`notes/specs-only/batch-3b.md`,
decision 1: `Txn.goSort`, and 2c's read registry, 3a's `applyStep_fun`). The general change: state
the sort's result as `goSort less xs` for a pure, opaque-but-functional `goSort` with the
sorted-permutation law, so any client can use determinism. Not shaped by one proof: determinism is
a fact of Go's implementation every caller may rely on. Not yet proposed upstream.

### Goose leaves a `select` case's variable unbound in the `default:` branch (2026-11-09, specs-only batch 2b)

In etcd's `serverWatchStream.recvLoop` (`server/etcdserver/api/v3rpc/watch.go`), a type switch's
`default:` branch reads the switched variable `uv`; the translation leaves `uv` unbound in that
branch, so the branch is stuck in the model (a model artifact: Go runs it). Found while writing the
specs-only branch's watch-server specs, which restrict the scope to well-formed client requests
partly because of it (`notes/specs-only/batch-2b.md`). To fix in Goose (bind the switched value in
every branch, `default` included); not yet reported upstream.

### `sort.Sort`'s size premise (2026-11-03, mvcc's API, branch `mvcc-api`)

- **Missing.** Perennial's proof of `sort.Sort` (`Perennial/Proof/sort/Sort.lean`, over `pdqsort`)
  requires at most `2 ^ 62` elements (its heapsort fallback's index arithmetic), a bound no Go
  program needs (a slice that long cannot exist in memory).
- **Needed by.** etcd's `sortRangeResults` (`txn/range.go:125`), through every spec that hands it a
  range's results.
- **Workaround here.** The size bound is stated once, locally, where a range's results are produced:
  `stateOk` in mvcc's `Range` contracts (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiState.lean`),
  proved from the store's whole-history receipt; not a law of the store's state (the user,
  2026-11-03: "we're going to ultimately get rid of the explicit size limit assumptions ... by
  improving perennial itself, so I want those assumptions as local as possible").
- **Proposed change.** Prove `sort.Sort` without the bound (from the slice's length being an `int`,
  or the heap indices computed without overflow), then drop `stateOk`'s length conjunct.
- **Status.** Not started.

### Contexts derived from a parent that is not an `isContext` (2026-11-08, k8s 7f; to be decided in the 7f-4 Draft)

- **Missing.** Two facts about contexts that etcd's require-leader stream handlers need, both
  general, neither settled yet (`notes/k8s-7f-scope.md`, §3, revision 2):
  - **(P-RL1)** a `Value` law for `WithCancel` over a general parent: for `k ≠ cancelCtxKeyAny`,
    `(WP parent.Value(k) {Φ}) -∗ WP child.Value(k) {Φ}`. It needs a premise that the parent's
    dynamic type is not one Go's `context.value` reads the fields of directly (`*valueCtx`,
    `*timerCtx`, `withoutCancelCtx`), or a description of such a parent's fields. As first phrased
    ("the child's `Value` is the parent's", any `isContext` parent) it was false: for
    `&cancelCtxKey` the child returns itself, and grpc's stream context is a `*valueCtx` chain
    (the 7f Scope review). `wp_WithCancel_any` already keeps the `ContextDesc`. The require-leader
    handler may need only a fact about grpc's `metadata.incomingOf`, which is this repository's
    (a reviewed trust-boundary fact), so P-RL1 may be unnecessary.
  - **(P-RL2)** derivations (`WithValue`, `WithCancel`/`WithTimeout`) over a parent with a weak
    contract: its `Done` as `isContext`'s, its `Err` any error after `Done` (etcd's
    `cancellableContext` returns `ErrGRPCNoLeader`, which `isCtxErr` excludes). Go's child takes
    `parent.Err()` on the parent's cancellation, so the child has the weak contract too. Natural
    form: `isContext` generalized over the predicate its errors satisfy.
- **Needed by.** The require-leader branch of etcd's stream interceptor, which Kubernetes' etcd3
  store reaches on every watch (`clientv3.WithRequireLeader`), and the Watch and LeaseKeepAlive
  handlers' derived contexts (`Tracer.Start`, `LeaseRenew`'s `WithTimeout`): stage 7f-4.
- **Workaround here.** Today the premise `v3rpc.runsNoRequireLeader` excludes the branch; the user
  decided (2026-11-08) to delete it, so 7f-4 needs these facts, as local lemmas until a Perennial
  change lands.
- **Status.** P-RL1 landed (2026-11-08) as `ctxValue`/`ctxValueFrom` (Perennial `ddc0f0acc`; see
  "Landed", "`Context.Value` at keys other than `&cancelCtxKey`"): `ctxValueFrom parent child`
  in `WithCancel`'s and the deadline constructors' posts, for any parent with a `ctxValue`; a
  `*valueCtx` parent (grpc metadata) through `ctxValue_valueCtx` from its fields, which this
  repository's `WithValue` spec would have to state. P-RL2 not started; the 7f-4 Draft states it.
  For 7f-4 (`notes/k8s-7f4-rebaseline.md`, R-1): grpc's run context gives its library facts only in
  the WP form (`grpcRunCtx`), which does not cross `WithCancel`; the re-baseline proposes the chain
  form in grpc's model.

### Fatal runtime errors are not in the model: `netpollinit` on file-descriptor exhaustion (2026-11-07, the review of `os-init-lean`)

- **Missing.** Go has failures that are neither a panic nor an error result: `fatal error: ...`
  ends the process (not recoverable). The first file `os` opens (`os.OpenFile` → `newFile` →
  `poll.FD.Init`) starts the runtime's netpoller; if its `epoll_create1` or `eventfd` fails, e.g.
  for lack of file descriptors (`ulimit -n` 5 or 6 with soft = hard, so `syscall`'s rlimit raise
  does not help), Go dies with `fatal error: runtime: netpollinit failed`. This repository's
  osFsExt `Open` (`GooseLang/Ext/OsFs/Impl.lean`) returns a file or an errno, so a program that
  opens a file has a proof though Go may die at that call (the adversary's program:
  `$CLAUDE_JOB_DIR/tmp/rv7/adv/t2/main.go` of session 0d784765). On `lean` before `os-init-lean`
  too.
- **Workaround here.** None yet; recorded in the extension's "Soundness discipline" docstring.
- **Proposed change.** A run-ending outcome a model can take (the model's `Open` may end the run
  where Go's runtime aborts), and Perennial's docs (`docs/KNOWN_LIMITATIONS.md`) listing the class of
  fatal runtime errors (`netpollinit`, out of memory, concurrent map writes detected, ...) and how
  each is modelled. For osFsExt alone: `Open`'s first call may exit the program.
- **Status.** Open.

### Struct field locations of different struct types at one base address (2026-11-04, bbolt, batch 14)

- **Limitation.** `structFieldRef` is an abstract function of `go.Semantics`
  (`GoSemanticsFunctions`); only `structFieldRef_plain` ties a field of a *plain* struct to
  `base + offset`. For a non-plain struct (any with pointer, slice, map or interface fields) nothing
  relates `l.[T, f]` to `l` or to `l.[T', g]` of another struct type `T'`. So holding `l ↦ v` for a
  fresh `&node{…}` does not show that `l` is not the location of an object of another struct type
  whose fields one owns separately (`l.[Bucket, "InBucket"] ↦ …`).
- **Needed by.** bbolt's writer heap (`Inv/WtxHeap`): one map of objects keyed by location, nodes
  (owned as whole struct points-tos) and buckets (owned field by field, the root bucket being
  `tx.root`, a field of `Tx`); a fresh node's location could not be shown to be no bucket's.
- **Here.** Planned (batch 14 of `notes/bbolt-proof-plan.md`, not yet applied): the heap's objects per kind, nodes
  and buckets in separate maps, liveness per kind, so a fresh node needs only "no node object at
  `l`", which the points-to conflict gives.
- **Proposal.** A law of `go.Semantics` that field locations are tied to their base for every
  struct type (each field of `T` at `l` is `l + off_T(f)` for some layout offset, offsets of
  distinct fields distinct, and the first field at `l` itself), or at least that
  `structFieldRef T f l ≠ structFieldRef T' g l'` unless `l = l'` and the offsets agree; then a
  whole points-to at `l` excludes every field points-to at `l` of another type with a field at
  offset 0. Needs a semantics review (trusted base): it constrains every model of `go.Semantics`.
- **Status.** Not started (proposal only).

### `|==>` binds tighter than `∗` in iris-lean's notation (2026-11-04, bbolt, U5)

- **Limitation.** In Lean's Iris notation `|==> A ∗ B` parses as `(|==> A) ∗ B`, unlike Rocq Iris
  (where the update extends to the right); `|={E}=>` is not affected. A statement written the
  Rocq way silently means something weaker.
- **Needed by.** Every Iris statement here; U5 found one (`Inv/State`'s `st_update`, fixed by
  parentheses). A grep of bbolt's `Inv/`, `Model/` and `Spec/` finds no other.
- **Here.** Parenthesize `|==> (A ∗ B)`.
- **Proposal.** iris-lean: give `|==>` the precedence of Rocq's (or of `|={E}=>`), or a linter
  warning on `|==> A ∗ B`; a note in Perennial's `IRIS_PROOF_MODE.md` meanwhile.
- **Status.** Not started.

### `sort.Search`'s spec does not name the evaluated indices (2026-11-04, bbolt's read path, U6)

- **Limitation.** Perennial's `sort.Search` spec gives the result's position (the first index
  where the predicate holds) but not that a result `< n` was one of the indices the closure was
  evaluated at, so a closure with a side effect on the evaluated indices (bbolt's `searchPage`
  sets a captured `exact` flag when the key at the evaluated index equals the sought one) cannot be
  reasoned about.
- **Needed by.** bbolt's `Cursor.searchPage`/`search_r` (U6).
- **Here.** U6 proved a stronger spec from Perennial's translated `sort.Search`
  (`Proof/go_etcd_io/bbolt/Read/SearchEv.lean`: an invariant indexed by the evaluated indices).
- **Proposal.** Perennial's `sort.Search` spec with the closure's invariant indexed by the
  evaluated indices (the result `< n` among them), as U6's.
- **Status.** Not started.

### `delete` on a named map type has no semantics (2026-11-04, bbolt's freelist, U2)

- **Limitation.** `MapSemantics.delete_map` unfolds `go.delete` only at a literal map type
  (`[go.MapType key_type elem_type]`), while `len_map` takes any type whose underlying type is a
  map (`[t ↓u go.MapType ..]`). Goose emits `delete [pidSet.ty]` for `delete(f.freemaps[size],
  start)` (`pidSet` is `map[common.Pgid]struct{}`), which therefore has no WP.
- **Needed by.** bbolt's hashmap freelist (`hashMap.delSpan`; `shared.Allocate`, `mergeSpans`).
- **Here.** `PidSetDeleteUnfold` (`Proof/go_etcd_io/bbolt/internal/freelist/Lemmas/HashDelete.lean`):
  the literal map type's rule at `pidSet`, taken as a hypothesis by the proofs that need it (an
  assumption on the semantics, to be discharged by the Perennial change).
- **Proposal.** Generalize `delete_map` as `len_map` was: any type whose underlying type is a map.
- **Status.** (2026-11-04) Branch `delete-map-named` of Perennial (`6e6b05af3`, off `lean`
  `4c8617a9e`, pushed): `delete_map {t ..} [t ↓u go.MapType ..]`, `wp_mapDelete_underlying` (the
  literal-type `wp_mapDelete` unchanged, derived), test `MapWrapper_delete` in unittest's
  `NamedMapAssignment.lean`; the touched modules build. Not landed: it changes the trusted
  semantics (`Perennial/Golang/Defn`), which Perennial's workflow (`AGENTS.md` item 4,
  `fix-semantics` skill) lands only with the user's sign-off and the trusted-base review. Once it
  lands: bump the pin and drop `PidSetDeleteUnfold`.

### `strings.ToLower` has no spec (2026-11-04, bbolt's `internal/common`)

- **Limitation.** `strings.ToLower` is names-only in Perennial, with no spec.
- **Needed by.** bbolt's `common.Verify` (`getEnvVerify` is `strings.ToLower(os.Getenv(...))`,
  `IsVerificationEnabled` compares with `strings.ToLower(verification)`).
- **Here.** (2026-11-05, bbolt final wave D, the user approved the new trust) a local
  trust-boundary axiom, `Spec/strings/ToLower.lean` / `Proof/strings/ToLower.lean`:
  `{{ True }} strings.ToLower s {{ (r : GoString), RET #r; True }}` (any `hlc`, like
  `os.Getenv`'s): it returns, without panicking, some string. `Verify` is proved over it and
  `os.Getenv`'s (`Proof/go_etcd_io/bbolt/internal/common/Lemmas/VerifyNP.lean`).
- **Proposal.** Perennial provides a translated or specified `strings.ToLower` (pure Go; its ASCII
  fast path and its `strings.Map(unicode.ToLower, s)` path), at least "returns some string"; then
  drop the local axiom.
- **Status.** Not started in Perennial; local axiom in place.

### `sort.SliceIsSorted` and `reflect.DeepEqual` have no spec (2026-11-05, bbolt's `internal/freelist`)

- **Limitation.** Both are names-only in Perennial (they work through reflection: `SliceIsSorted`
  takes the slice's length with `reflectlite.ValueOf(x).Len()`, `DeepEqual` walks its arguments'
  dynamic types).
- **Needed by.** bbolt's hashmap freelist: `hashMap.Init` panics unless its page ids are
  `sort.SliceIsSorted`; `hashMap.mergeSpans`' `Verify` check panics unless `reflect.DeepEqual`
  finds its free maps equal (two `map[Pgid]struct{}`).
- **Here.** (2026-11-05, the user approved the new trust; until then hypotheses of bbolt's
  `links_pending`) local trust-boundary axioms: `Spec/sort/SliceIsSorted.lean` /
  `Proof/sort/SliceIsSorted.lean` (on a slice, with a `less` that answers `lt` on indices of the
  slice and keeps a resource: returns whether no `less(i, i-1)`, calling `less` only on such
  indices), and `Spec/reflect/DeepEqual.lean` / `Proof/reflect/DeepEqual.lean`
  (`spec_pgidSet`: on two `map[Pgid]struct{}` held by map points-tos, which are non-nil, returns
  whether they have the same keys; stated at that one type, as the map points-to is not indexed by
  the Go type). Each file header says why it is true of Go.
- **Proposal.** Perennial proves `sort.SliceIsSorted` over a model of `reflectlite.Value.Len` on
  slices (its loop is plain Go), and gives `reflect.DeepEqual` a spec for maps of comparable
  scalar keys and `struct{}` values; then drop the local axioms.
- **Status.** Not started in Perennial; local axioms in place.

### `wp_load`/`wp_store` through a whole-struct points-to (2026-11-04, bbolt's `internal/common`, U1)

- **Limitation.** With `l ↦ v` for a whole struct `v`, `wp_load`/`wp_store` of one field
  (`l.[S, "f"]`) do not find the field's points-to: the struct points-to must be split by hand
  (`iStructNamed`) first and recombined after (`typedPointsto_combine`).
- **Needed by.** U1's accessor proofs (`Proof/go_etcd_io/bbolt/internal/common/`), and every
  proof that loads one field of a struct it owns whole (U8's `node.childAt`).
- **Here.** Split and recombine by hand.
- **Proposal.** An `IntoField`-style search in `wp_load`/`wp_store` that opens a whole-struct
  points-to at the field and closes it again.
- **Status.** Not started.

### General lemmas to move to Perennial (2026-11-04, bbolt)

- **U1's `Proof/go_etcd_io/bbolt/internal/common/Lemmas/Bytes.lean`**: byte points-to bounds,
  byte slices over a byte points-to, persistence; copied from Perennial's
  `unsafememory/Pages.lean`, an example's module that cannot be imported.
- **U2's `Proof/go_etcd_io/bbolt/internal/freelist/Lemmas/SliceLen.lean`**: an owned slice of
  `w64`s has fewer than `2^44` elements (its bytes lie below `maxAddr`).
- **Proposal.** Move both into Perennial's `Golang/Theory` (with the `Pages.lean` copies'
  origin), then drop the local copies. **Status.** Not started.

### Heap: allocation returns a meta token (2026-11-03, bbolt's invariant design)

- **Limitation.** GooseLang's allocation specs give the points-to of a fresh location but no
  `metaToken l ⊤` (iris-lean's `GenHeap` has `metaToken`/`metaInfo`; Iris HeapLang's `wp_alloc`
  hands out the token). Without it a library cannot attach ghost data to an object it allocates
  (`metaInfo l N x`: timeless, persistent, agreeing), so a predicate keyed by the object alone
  (`txBytes tx s b`, `boltBkt tx b n g`) cannot be tied to the ghost names of the object's owner
  in a pure law; a package fact cannot carry such a registry either (a fixed proposition: a ghost
  name inside it does not agree between two copies).
- **Needed by.** bbolt's API (`Spec/go_etcd_io/bbolt/Api.lean`): `txBytes_acc`, `boltTx_fill`,
  `boltCur_timeless` (the design `bbolt-inv/design.md`, D-C).
- **Here.** The γ-free predicates take the database's ghost name instead (`txBytes tx γ s b`,
  `boltBkt tx γ b n g`, `boltCur tx γ c …`, `curAt tx γ …`; decided by the coordinator, 2026-11-03;
  `notes/decisions.md`, "bbolt's API spec"). The backend carries `γ.db` already.
- **Proposal.** Every GooseLang allocation spec (`wp_alloc`, `GoAlloc`, composite literals'
  addresses) also gives `metaToken l ⊤`, as HeapLang's does; a general change, not shaped by
  bbolt. With it the extra `γ` could be dropped again (an API change then).
- **Status.** Not started.
### Thread tokens by level: a goroutine of a counted wait group has no token (2026-11-04, lease-expiry P1)

etcd's `EtcdServer.GoAttach` counts its goroutines in a wait group whose counter bound is the
thread bound: `Add` deposits the caller's `threadTok` in the group's invariant
(`Proof/.../etcdserver/InvGoAttach.lean:171-192`), and `fork` makes exactly one token for the new
thread (`wp_fork_tok`, `GooseLang/Lifting.lean:1806`). So a goroutine started by `GoAttach` holds no
token, and cannot itself `GoAttach` or call anything that takes `threadTok`, though Go does both:
`revokeExpiredLeases` (`server.go:860`) calls `ensureLeadership` and `GoAttach`es one goroutine per
expired lease, round after round. No pool inside this repository fixes it (three tokens for two
threads; `notes/lease-expiry-plan.md`, review round 2). Proposed general change
(`notes/bounds-plan.md` D2(b)): split a thread token by level, `threadTok ⊣⊢ [∗ l < L] levelTok l`,
`fork` giving the new thread all levels; a counted wait group then takes `levelTok 0` (bound `k + p <
2·threadBound`), and the goroutine keeps levels `≥ 1` to borrow from pools (lock order gives the
levels). Local workaround: `EtcdServer.revokeExpiredLeases.wp_proof` a marked `sorry` (the user's
approval, 2026-11-04). Not yet proposed on a Perennial branch.

### Adequacy that hands the program its extensions' start resources (2026-10-31, kvdurable)

- **Limitation.** None in Perennial: `goose_adequacy` already gives the WP proof
  `extsGlobalStart`/`extsLocalStart`; this repository's `init_adequate`
  (`examples/lib/etcdstart/Adequacy.lean`), the proposed generic closed theorem, dropped them.
- **Here.** `init_adequate_start` (`examples/lib/etcdstart/AdequacyStart.lean`), any extension list, the
  body's WP taking both start resources; `durable_init_adequate` (`examples/lib/etcdstart/DurableExt.lean`)
  for `[durableExt]`.
- **Proposal.** Land it in Perennial with `init_adequate` (one theorem, `init_adequate` its
  corollary for resources dropped).

### Slices: an empty slice literal is not nil (2026-10-29, authkv G2)

- **Limitation.** `wp_slice_literal` gives an arbitrary pointer for an empty literal, so a proof
  cannot show that `[]byte{}` is not `nil` (in Go it is not; `testCompareSliceToNil` shows it at the
  semantics level). etcd's watch server sends a from-key watch's range end as `[]byte{}`
  (`recvLoop`), so `createRangeOk` has two readings for the end `"\x00"`: "from the key on" or "the
  key alone" (`v3rpc/InvWatchStream.lean`; `notes/status-history.md`, the watch slice).
- **Needed by.** `watcher.Watch.spec`'s from-key watches (its premise `rangeEnd ≠ [W8 0]` excludes
  them today): authkv's root watch of every key (`Watch("", WithPrefix())`, G2,
  `notes/authkv-main-plan.md`).
- **Workaround here.** None; the user chose to wait for the general fix (2026-10-29).
- **Proposed.** `wp_slice_literal_nonnull` (`Perennial/Golang/Theory/Slice.lean`): the literal's
  pointer is non-null, from the backing array's typed points-to (`typedPointsto_not_null`, which
  holds at length zero too); `wp_slice_literal` unchanged, its corollary. A proof, not a semantics
  change: no trusted-base delta.
- **Status.** Landed on Perennial `lean` 2026-10-30 (`6da88b280`), in the pin with this bump
  (branch `pin-6da88b2`, `notes/STATUS.md`, "Perennial pin `6da88b280`"). `#print axioms`: Lean's
  three only.

### Context model: `WithCancel` keeps its parent's values (2026-10-30, authkv G2)

- **Limitation.** Perennial's `WithCancel` specs say nothing of the new context's `Value`: a
  `*cancelCtx` answers every key but its own `&cancelCtxKey` with its parent's value
  (`context.go`, `cancelCtx.Value`), so grpc's outgoing metadata (key `mdOutgoingKey{}`) is the
  parent's. The model cannot state it (`isContext`'s `Values` are unused, the entry below).
- **Needed by.** G2's watch (`notes/g2-watch-auth.md`, row (h)): the watcher's stream runs on
  `WithCancel(&valCtx{inctx})`, and the stream's metadata must be `inctx`'s.
- **Workaround here.** The local trust-boundary axiom `context.WithCancelValCtx.wp_proof`, strengthened
  in place with `⌜metadata.outgoingOf ctx' = metadata.outgoingOf inctx⌝` (the user's choice,
  2026-10-30).
- **Proposed.** A `Value` contract for `WithCancel`/`WithTimeout`/`WithDeadline` (delegation to the
  parent at every key but the context's own), on a Perennial branch by its own workflow, together
  with the `Values` clause below. (h) is retired when it lands.
- **Status.** Open.

### Context model: a descriptor's `Values` constrain nothing (2026-10-29, authkv round 1)

- **Limitation.** `isContext c d` never reads `d.Values` (its docstring: "unused"), so
  `isContext c d ⊢ isContext c { d with Values := ∅ }` and a spec's "no values" says nothing of what
  `c.Value(k)` returns. A law "a context with no values has no value at grpc's metadata key" is then
  false of every context; it was inconsistent with `AppendToOutgoingContext`'s axiom
  (`notes/axiom-review/outgoingOf-noValues.md`, branch `axiom/outgoingOf-noValues`).
- **Needed by.** authkv's `reqCtx` (its `anon` principal sends no token: `WithTimeout(Background())`
  has no outgoing grpc metadata); the same gap as the `WithCancel` entry below (the trace key).
- **Workaround here.** The trust-boundary axiom `context.WithTimeoutBackgroundMd.wp_proof`
  (`WithTimeoutBackground`'s post with `metadata.outgoingOf (ok ctx') = none`), for authkv's callers
  only; `WithTimeoutBackground.wp_proof` stays proved.
- **Proposed.** `isContext`'s `Value` clause at every key: `c.Value(k)` returns `d.Values !! k` (or
  nil), with the derived contexts' specs saying their `Values` (a `cancelCtx`/`timerCtx` the
  parent's, a `valueCtx` the parent's with one more). Then "no values" is meaningful, the `Md`
  spec is proved, and the outgoing-metadata fact a law over grpc's key.
- **Status.** Open.

### Sync: locking a fresh mutex at any invariant (2026-10-30, kvreconf-final)

`sync.init_Mutex` takes `▷ R`, the lock invariant, when the mutex is made. A goroutine that allocates
a mutex and locks it before the invariant holds cannot use it: kvreconf's `StartCluster` locks
`c.mu` and then inserts the founders, and `clusterLockInv` holds only at the `Unlock`. The lock is
needed because the replicas' `run` goroutines, started inside the loop, call `c.replica`. The
workaround here is `wp_Mutex_Lock_fresh` in `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/MutexFresh.lean`.
It is proved, with no axiom, from Perennial's exported unsealing equations and `lock.lock`'s code:
`Lock` of a wholly owned mutex at `false` gives `isMutex m R ∗ ownMutex m` for any `R`, and the
first `Unlock` establishes `R`. Proposed: the same lemma next to `init_Mutex` in Perennial's
`Proof/sync/Base.lean`, after which the local copy goes. Status: not yet proposed.

### Tactics: `wp_auto` and `iunfold` unfold a `token` hypothesis to its model (2026-11-01, kvdurable)

- **Limitation.** In `Cluster.Crash`'s proof, a spatial hypothesis `crasher γ` (kvdurable's
  `def crasher γ := token γ.crt`) came out of `try wp_auto` unfolded past `token` and `own`, down to
  the `UPred` structure (`{ holds := fun n x => iSingleton … ≼{n} x.val, … }`). After that no spec
  can frame it and `iexact` cannot unify it with `crasher γ`. `iunfold isClusterC at Hc'` did the
  same to it, although it unfolds another hypothesis. A `curRep` hypothesis (`ghostMapElem`) in
  `Cluster.restart`'s proof went through `wp_auto` unchanged. Unconfirmed guess: something reduces
  the hypotheses' types to weak head normal form, and `token`/`own` unfold all the way there.
- **Needed by.** `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Cluster__Crash.lean`.
- **Workaround here.** `attribute [local irreducible] crasher in` on the theorem. The package
  init comes from `isClusterC` in a subgoal with only that hypothesis.
- **Proposed.** First a minimal reproduction (a `token` hypothesis through `wp_auto`), then keep
  the tactics from changing hypotheses they do not use.
- **Status.** Open.

### Tactics: `wp_if_destruct` on a loop condition left as `#(decide P) = #true` (2026-10-27)

- **Limitation.** After a `wp_for`, `wp_if_destruct` sometimes splits on `#(decide P) = #true`
  without peeling it to `P`, and `cleanup_bool_decide` (and `simp only [decide_eq_true_iff]`)
  makes no progress on it; unconfirmed guess: `P`'s `Decidable` instance is the one of a Lean
  `if` inside it. Elsewhere `cleanup_bool_decide` between `wp_for` and `wp_if_destruct` suffices.
- **Needed by.** `v3rpc/checkIntervals.lean`'s third loop (found in the pin bump to `edcadb1e5`).
- **Workaround here.** Convert the hypothesis by hand in each branch (`Decidable.byContradiction
  fun h => by simp [h] at Hif`).
- **Proposed.** Make `wp_if_destruct` (or `cleanup_bool_decide`) normalize `#(decide P) = #true`
  whatever `P`'s instance; first a minimal reproduction.
- **Status.** Open.

### Lemmas: `strings.split` of `strings.Join` (2026-10-27, D22 J-T)

Perennial's `Proof/strings/Base.lean` has `intercalate_split` (joining the fields of a split gives
the string back) but not the converse. J-T proves it locally for a one-byte separator no field
contains (`split_intercalate1`, with `splitAux_field`, in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Pipe.lean`: the `X-PeerURLs` header,
`setPeerURLsHeader`'s `Join` read back by the handlers' `Split`). Proposed: the general lemma (any
non-empty separator that is no infix of a field and does not overlap them) in Perennial's
`strings` proofs, and this repository's local copy removed.

### Channels: `recvAu_wand` with a fancy update in the wand (2026-10-27, branch `raft-api`)

- **Missing.** `recvAu_wand` (`Chan/AuSpec/ChanAuBase.lean`) turns a receive's update for `Φ1`
  into one for `Φ2` with a plain wand `Φ1 -∗ Φ2`; every commit of a receive ends at `⊤`
  (`={∅,⊤}=∗ Φ`), so a wand `Φ1 ={⊤}=∗ Φ2` is as sound, and is what a client needs that opens an
  invariant after the receive (raft's `isReadyChan_recvAu`: the `Ready`'s facts become the node
  API's under the cluster's invariants).
- **Workaround here.** `recvNestedAu_wand_fupd`/`recvAu_wand_fupd` in
  `Proof/go_etcd_io/raft/v3/NodeApiImpl.lean` (the same proofs, `iapply Hw` after the commit
  instead of `imodintro`).
- **Proposed change.** The two lemmas in Perennial beside `recvAu_wand` (and the same for the
  send and close updates), then the local copies go.
- **Status.** Open.

### Translation: `sort.StringSlice`'s methods (2026-10-25, leases T3, branch `leases-t3`)

- **Missing.** Perennial's `sort` declares the type `sort.StringSlice` but none of its methods
  (`Len`, `Less`, `Swap`, `Sort`, `Search`), so `sort.StringSlice(keys).Sort()` does not resolve.
- **Needed by.** `lessor.Revoke` (`server/lease/lessor.go`): it sorts the lease's keys before
  deleting them (`notes/leases-plan.md`, L2d).
- **Workaround here.** A trust-boundary spec, `Spec/sort/StringSlice__Sort.lean` (the statement
  of Perennial's `sort.Strings.spec`), an axiom.
- **Proposed change.** Translate the methods in Perennial's `sort` and prove `Sort` as
  `sort.Strings` is proved; then the axiom here goes.
- **Status.** Open.

### Tooling: incremental proof checks, and long `·` blocks as auxiliary theorems

- **Missing.** A way to check a proof after an edit without elaborating the whole file
  (`lake build` and `lake env lean` start over each time; Perennial's tutorial checks a file
  with `lake build`), and a way to keep the once-per-declaration work of a long Iris proof
  (instantiation, sharing, the kernel's check of one huge term) from being redone on every edit.
- **Needed by.** Every proof here and in Perennial; most for the longest
  (`watchGRPCStream.run`, 3368 lines: an edit near its end costs about its fresh time).
- **Workaround here.** `etc/lean-check.py` (a kept Lean server; `--fast`, `-e`, `--goal`,
  `--split`) and `Proof/AbstractBullets.lean` (option `abstractBullets`), both generic: the
  script names no project, the tactic module nothing of this repository's.
- **Proposed change.** Move both to Perennial (`etc/lean-check.py`, the tactic in its
  `PerennialMeta` library), document the loop in `docs/PERENNIAL_PROOF_TUTORIAL.md` beside
  `lake build`; `lean-check.py` here then imports nothing of its own (`SPLIT_MODULE`).
- **Status.** Open (2026-10-26, `notes/STATUS.md`, "Checking proofs while editing them").
- **Concurrent clients (2026-10-27).** With eight agents checking files through one server (the
  pin bump to `edcadb1e5`), the server stopped answering twice (its log silent, `Watchdog error:
  Cannot read LSP message: Stream was closed`), kept 33 files open past `--max-open 12`, and once
  reported a file as passing that `lake env lean` showed broken (`checkParallel`). The fallback was
  `lake env lean FILE`. To fix before it moves: eviction under load, and a client timeout.

### Specs: `(*Time).After`

- **Missing.** The pointer-receiver form of `time.Time.After` (Perennial's `Proof/time/PtrMethods.lean`
  has `Add`, `Before`, `Sub` only).
- **Needed by.** etcd's TTL keeper (`simpleTokenTTLKeeper.run`: `nowtime.After(tokenendtime)` on an
  addressable `Time`; the auth plan's S5e, 2026-10-25).
- **Workaround here.** `auth/TokenKeeperRun.lean`'s `time_wp_ptr_After`, the shape of
  `Time.wp_ptr_Before_of`.
- **Proposed change.** `Time.wp_ptr_After_of`/`Time.wp_ptr_After` beside `Before`'s.
- **Status.** Open.

### Specs: `sort.Search` without monotonicity

- **Missing.** A spec of `sort.Search(n, f)` for a predicate that need not go from false to true:
  Perennial's (`Perennial/Spec/sort/Search.lean`) takes `IsMonoPred f n`; without it, the binary
  search still returns an index in `[0, n]` (its loop keeps `0 ≤ i ≤ j ≤ n`).
- **Needed by.** `authStore.RoleGrantPermission` (`server/auth/store.go`): it searches a role's
  permissions by key, and nothing records that a role record's permissions are sorted (the auth
  plan's S4d, 2026-10-24).
- **Workaround here.** `auth.wp_Search_any` (`Proof/go_etcd_io/etcd/server/v3/auth/SearchAny.lean`),
  a proof of that weaker fact over Perennial's translation of `sort.Search`.
- **Proposed change.** `sort.wp_Search_any` (or a spec whose monotonicity premise is optional)
  in Perennial's `Proof/sort`, general; then the local copy goes.
- **Status.** No longer needed here (2026-10-27): the auth plan's E3z fork fix
  (`issues/etcd-auth-grant-permission-same-key.md`) replaced the search by a filter, and
  `SearchAny.lean` is gone (in git history). The general spec is still a reasonable Perennial
  change, with no client here.

### Goose: a parenthesized untyped constant expression in a bitwise operation

- **Missing.** Goose translates `c | ('x' - 'X')` (`internal/strconv.lower`) as an untyped
  subtraction the semantics cannot step, whereas a lone constant (`c | 0x20`) comes out as
  `#(W8 32)`: an untyped constant expression is not folded before it meets a typed operand.
- **Met by.** Perennial's `strconv` change (`c022dbe42`, 2026-10-25): `lower` is a trusted model,
  goose's translation of `return c | 0x20`.
- **Proposed change.** Fold untyped constant expressions in goose (Go's `go/constant` gives their
  values), under Perennial's semantics-change workflow; then `lower`'s model goes.
- **Status.** Open.

### Tactics: `word`'s caches shared between parallel declarations

- **Missing.** Deterministic elaboration under a parallel build. `word`'s caches
  (`Perennial/Std/Word/Cache.lean`: `wordCache` and `failCache`, process-global `IO.Ref`s) are
  shared between the declarations Lean elaborates in parallel within one module, so whether a
  `word` call hits the cache, and hence the heartbeats a proof uses, depends on which declaration
  ran first. A proof near its heartbeat limit then fails on some runs only (and a cached failure
  could in principle leak between contexts). The same class as the flaky `stepLeader.lean` build
  (`notes/flaky-stepleader-build.md`, fixed in Perennial `fb1ecb030`, "no global mutable state
  shared between parallel declarations").
- **Needed by.** `Proof/go_etcd_io/raft/v3/raft__Step/MsgStorageAppendResp.lean`'s
  `wp_Step_MsgStorageAppendResp_snap` (D22 S-d3b): it ran out of 1000000 heartbeats once under a
  parallel full build (2026-10-21) and passes alone, on the same tree. Any proof near its limit.
- **Workaround here.** That theorem's limit raised to 4000000, with a comment citing
  `notes/STATUS.md`, "`word`'s shared cache" (what is proved is unchanged).
- **Proposed change.** The caches keyed per declaration, or held in the tactic's own state
  (`MetaM`/`TacticM` state, or an environment extension reset per declaration), so that a
  declaration's elaboration does not depend on its siblings'.
- **Seen again, within one declaration** (2026-10-27, the compactor pilot): in
  `v3compactor.Periodic.getCompactInterval`/`getRetryInterval`'s proofs, `word` in the two sibling
  branches of one `if` (hypotheses `h < pd` and `¬ h < pd`) gave a proof the kernel rejected
  ("application type mismatch": the second branch's goal closed by the first branch's cached term,
  built over the other hypothesis). So a cached proof does leak between contexts, as the paragraph
  above feared, and fails at the kernel rather than silently. Workaround there: no `word` in sibling
  branches (`rfl`/`omega` and `BitVec.toInt_sdiv_of_ne_or_ne` instead), with a comment.
- **Seen again** (2026-11-01, kvdurable's `openStorage`): `word` in a `prev = 0` branch of a
  `wp_if_destruct` (hypothesis `¬ 0 < prev`) gave a proof the kernel rejected, built over the
  sibling branch's `0 < prev`; and a `word` side goal later in the same proof failed with "unknown
  free variable" (a cached term over a hypothesis of another goal). Workaround there: `omega` on
  `BitVec.toNat` for the first, the `word` fact proved at the top of the proof for the second.
- **Status.** Not started (found 2026-10-21, `raft-retarget`, now on `lean`).

### Specs: a law for `Done()` of an `isContext` context (2026-10-27, the compactor pilot)

- **Missing.** `isContext` (an `abbrev` of `isContextDef`) has no law for calling `Done()`: clients
  `iunfold context.isContextDef` and take its `#HDone` field (the compactor's `Run` proofs, the
  client's `lessor`/`watchGRPCStream` proofs, leasing's).
- **Needed by.** The spec-first recipe's rule that a client does not unfold another package's
  definitions (`notes/spec-first-plan.md`, phase 3); the freeze of the compactor's specs.
- **Workaround here.** The unfold, kept until the law lands.
- **Proposed change.** `context.isContext_Done : isContext c s ⊢ {{ True }} c.Done() {{ ch γch,
  RET #ch; isContextDone s ch γch }}`, next to `isContext_pers`: branch `context-done-law` of
  Perennial (`3c384b081`, off `lean` at `edcadb1e5`; worktree `/shared/perennial-ctxdone`), checked
  against the pinned `6b58510f9` (the same `isContextDef`), not yet built or landed there.
- **Status.** Landed on Perennial's `lean` (`3c384b081`, 2026-10-27), just past the pin `edcadb1e5`
  (2026-10-27), which did the uniform-function-results migration: the next pin bump brings it, and
  the compactor's `Run` proofs switch to the law then.

### Specs: a law for calling a `cancelSpec` cancel function (2026-10-27, the compactor pilot's phase 4)

- **Missing.** `context.cancelSpec cancel γ P` (a `def`: `□ ∀ Φ, □ P -∗ ▷ (ContextClosed γ -∗ Φ #()) -∗
  WP cancel #() {{ Φ }}`) has no law for the call: clients `iunfold context.cancelSpec` and apply it
  (the compactor's `Periodic.Stop`/`Revision.Stop`, the client's `newClient`, `lessor.resetRecv`).
- **Needed by.** The spec-first recipe's rule against cross-package unfolds (`notes/spec-first-plan.md`,
  phase 3).
- **Workaround here.** The unfold, justified at the compactor's freeze with `isContextDef`'s
  (`notes/decisions.md`, "The compactor pilot's freeze").
- **Proposed change.** `context.cancelSpec_call : cancelSpec cancel γ P ⊢ {{ □ P }} cancel #() {{ RET #();
  ContextClosed γ }}`, next to `cancelSpec_weaken`.
- **Status.** Not started; to land with the next Perennial change (the compactor's proofs switch at the
  pin bump that brings `isContext_Done`).

### Specs: `context.WithCancel`'s cancel function not `nil`

- **Missing.** `context.WithCancel`'s specs (`context.WithCancel.spec`, `wp_WithCancel_Background`,
  `wp_WithCancel_gen_of`, ...) return the cancel function with its triple (`cancelSpec`) but not
  that it is not `nil`, which is true (it is the closure `func() { c.cancel(true, Canceled, nil) }`,
  a `func.mk`; the proof's `simp only [recv_eq_func_mk]` sees it) and which a caller that tests the
  function against `nil` needs.
- **Needed by.** `pkg/v3/schedule`'s `fifo.Schedule` (2026-10-22, branch `fifo-sched`): it panics
  when `f.cancel == nil`, and before `Stop` `f.cancel` is the context's cancel function.
- **Workaround here.** `Proof/go_etcd_io/etcd/pkg/v3/schedule/WithCancel.lean`: local copies of
  `wp_WithCancel_gen_of` and `wp_WithCancel_Background_of` with `⌜cancel ≠ func.nil⌝` added
  (`wp_WithCancel_Background_nn`); no axiom.
- **Proposed change.** `⌜cancel ≠ func.nil⌝` in the postconditions of `WithCancel`'s specs (and of
  `WithTimeout`/`WithDeadline`'s, whose cancel functions are closures too).
- **Status.** Not started (found 2026-10-22).

### Proof idioms: a closed theorem from a program's initializer and body

- **Missing.** A form of `goose_adequacy` for the usual closed theorem: a program
  `init #() ;; body` run from a fresh state (`IsInit`) with one thread, the receipt and thread
  bounds `n + 1`, `n + 2` of an `n`-step execution, the right to initialize (`ownInitializing`)
  from the empty package state, and the conclusion with `v.isPanic = false` for each final value
  (from `UnrecoveredPanic`'s exclusion). Every closed theorem repeated these steps.
- **Needed by.** The examples' closed theorems (2026-10-22, D36): kv's, the counter's and
  kvwitness's over `goose_adequacy`; the etcd examples' over this repository's
  `goose_adequacy_start` (`Proof/runtime/Start.lean`), which stays here.
- **Workaround here.** `Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/Adequacy.lean`:
  `init_adequate` (over `goose_adequacy`, its WP obligation `progOk0`: the initializer's triple
  and the body's WP from the package's predicate and the main thread's token, at every ghost-state
  instance at the state's local context), `adequate_of_unrecovered`, `ownInitializing_of_empty`;
  no axiom. (`etcd_adequate`, the same over `goose_adequacy_start`, is this repository's.)
- **Proposed change.** `init_adequate`, `adequate_of_unrecovered` and `ownInitializing_of_empty`
  in `Perennial/GooseLang/Adequacy.lean` (or beside `IsInit` in `Perennial/Golang/Theory/Pkg.lean`).
- **Status.** Not started (2026-10-22).

### Goose: field selection through a type alias of a struct

- **Missing.** `getStructInfo` (`goose/types.go:358`) matches `*types.Named` without
  `types.Unalias`, so a selector on a value of an alias type (`clientv3.Event = mvccpb.Event`) is
  rejected (`[impossible(go)]: expected (pointer to) struct type for base of selector`).
- **Needed by.** The k8s etcd3 watcher (`parseEvent`, `event.go:80`; `watchChan.startWatching`,
  `watcher.go:516`) and compactor (`compactor.fromWatchResponse`, `compact.go:308`). Not the
  store's unary methods.
- **Workaround here.** The three functions names-only (survey branch's `etcd3.toml`); the
  compactor configured off.
- **Proposed.** `types.Unalias` on the type and on a pointer's element in `getStructInfo`. Tried
  in a scratch copy of the pinned translator: the three translate and their `Code` and
  `GeneratedProof` elaborate; nothing else changes.
- **Status.** Landed (2026-11-04, the user's sign-off on the plan, G1 of
  `notes/k8s-compactor-plan.md`): Perennial `898c0ddc5` (`fix-semantics` Case 31), pinned here
  since 2026-11-04 (branch `pin-898c0ddc5`). The two lines, with tests of a value, a pointer to an
  alias and an alias of a pointer, and the semantics test `testStructFieldThroughAlias`, proved.
  No translation here changed at the pin; its first user is the compactor's watch loop (Q1 (b)).
  `etcdstart.Collect`'s workaround (`mvccpb.Event` for `clientv3.Event`) is gone (2026-11-04): it
  ranges over `wresp.Events` directly, its proof unchanged.

### Goose: imports of packages whose types a body names, and same-named packages

- **Missing.** When a body uses a method or value whose type belongs to a package the Go file
  does not import, Goose adds no import for it, and `pkgRef` (`goose/goose.go:2967`) refers to it
  through an imported package of the same name if there is one. The second is a silent
  mistranslation: `storage.InvalidError.Error` calls apimachinery's `utilerrors.Aggregate.Error`,
  emitted as the standard library's `errors.Aggregate`.
- **Needed by.** The k8s etcd3 store: `utilfeature.DefaultFeatureGate.Enabled` names
  `featuregate.FeatureGate` (`New`, `store.Delete`, nine functions in all);
  `storage.InvalidError.Error`.
- **Workaround here.** `util/feature.toml` imports `featuregate` names-only, so the name reaches
  importers; `InvalidError.Error` names-only (unreached by the store's paths).
- **Proposed.** Import the Lean module of every package whose types a translated body names, and
  make `pkgRef` an error, never a substitution, when the package is not imported under its own
  name.
- **Status.** The substitution is fixed in the pin `ad74ee4f6` (`e5e31069a`: `pkgRef` names a package by
  its own path). The workarounds here remain: the DaemonSet's D2 exclusions (their bodies are named
  hypotheses, `Spec/**/*_body.lean`, of the unlinked phase-5 proofs), `util/feature.toml`,
  `cacher.toml`. Next: drop the D2 exclusions and discharge the body hypotheses by the generated
  unfolds; the missing imports (the first half) are not checked yet.
- **Also the watch cache (2026-10-26, branch `kep-6404`, `notes/kep-6404-plan.md`).** The cacher's
  `processEvent`, `UpdateResourceVersion` and `waitUntilFreshLocked` use the cacher's `metrics`
  variables, of component-base's `metrics` types (`CounterVec`, `HistogramVec`), which the cacher
  does not import: the substitution names them `cacher.metrics.CounterVec` (`Unknown identifier`).
  Workaround here: `cacher.toml` drops its import of the cacher's `metrics` (both are then named
  by their paths) and the names arrive through `consistency`'s public import of the cacher's
  `metrics` and its of component-base's (names only). Its cost: `watchCacheEvent`, whose
  `timeline` field is a `metrics.DispatchTimeline`, is axiomatized (`translate_types` skips a type
  naming a package not imported), so `processEvent` and `UpdateResourceVersion`, which build one,
  cannot be proved until the general fix.
- **Also the DaemonSet controller (2026-10-27, branch `k8s-daemonset-proof`; gap D2 of
  `notes/k8s-daemonset-goose.md`).** Kubernetes names nearly every API and client package `v1`, so
  the substitution hits the controller's main path: `syncDaemonSet` (component-base's
  `metrics.CounterMetric` named as the controller's `daemon/metrics`), `RealPodControl.createPods`
  and `DeletePod` (client-go's typed `PodInterface` named as `k8s.io/api/apps/v1`'s), `ComputeHash`
  (the standard library's `hash.Hash32` as `pkg/util/hash`'s), the node-affinity `Match`es
  (metav1's `ObjectMeta` as core/v1's); ten functions names only. **Tried**: `pkgRef` returning the
  package's own path always (the substitution loop deleted) in a scratch copy of the pinned
  translator: all ten translate and their modules elaborate (the interfaces' modules are in scope
  through public imports), and no other file of the project changes. Now the most needed of the
  open Goose changes for the DaemonSet proof.

### Specs: the builtin `max` (2026-10-26, branch `kep-6404`)

- **Missing.** No spec of the predeclared `max` (`functions go.max [t, t]`): each proof proves its
  own: raft's `wp_max2_uint64` (`raft/v3/InvTracker.lean`), mvcc's `sw_wp_max_int64`
  (`watchableStore__syncWatchers.lean`), the watch cache store's `wp_max_uint64` (`cacher/store/
  DefsWCS.lean`).
- **Proposed.** A spec of `max`/`min` on the integer types in Perennial's predeclared theory.
- **Status.** Not started.

### Goose: a constraint interface's `comparable` term (2026-10-26, branch `kep-6404`)

- **Missing.** `translate_types` accepts an interface that embeds `comparable`
  (client-go's `tools/cache.Object`: `interface { GetName() string; GetNamespace() string;
  comparable }`) and emits `go.type_term.TypeTerm go.comparable`, which Perennial does not define
  (`Unknown identifier go.comparable`).
- **Needed by.** Nothing yet: the watch cache's store names `tools/cache`'s indexer types only;
  (2026-10-26) the local half of `tools/cache` (store, thread-safe map, indexers) does not use
  `Object`; the typed informers (`TypedResourceEventHandler[T Object]`, DaemonSet plan phase 4) will.
- **Workaround here.** `client_go/tools/cache.toml` without `translate_types`: the types it
  translates are listed by name (2026-10-26, `notes/k8s-clientgo-goose.md`, C6), `Object` stays
  axiomatized.
- **Proposed.** Either a `go.comparable` type set in Perennial's semantics, or Goose rejecting
  (axiomatizing) such an interface under `translate_types`, as it does other unsupported types.
- **Status.** Not started.

### Goose: an axiomatized type alias is declared under another name than its uses (2026-10-26, client-go survey C3)

- **Missing.** An axiomatized alias is declared `axiom X : go.GoType` (`goose/types.go:65`) but
  referred to as `X.ty` like every type.
- **Needed by.** client-go's workqueue (`klog.Logger = logr.Logger` in its configs).
- **Workaround here.** klog's config imports `github.com/go-logr/logr` (names only), so the alias
  translates.
- **Proposed.** Declare the axiomatized alias as `X.ty`.
- **Status.** Not started.

### Goose: `min`/`max` of a named integer type (2026-10-26, client-go survey C4)

- **Missing.** `min(a, b)` on `time.Duration` is rejected (`comparison between non-assignable
  types`): `goose.go:926` joins the first parameter's underlying type with the others' types.
- **Needed by.** client-go's `flowcontrol.Backoff.Next` and `tools/cache`'s
  `threadSafeMap.Transaction` (names only here).
- **Workaround here.** The two names only.
- **Proposed.** Emit `go.min` at the parameters' (named) type and let its semantics take the
  underlying type (type choices are the Lean semantics', Perennial's `AGENTS.md`); joining the
  underlying types in Goose also works (tried in a scratch copy: both translate and elaborate) but
  makes that choice in Goose.
- **Status.** Fixed in the pin `ad74ee4f6` (`0227e444b`: `min`/`max` take the type `go/types` reports);
  the two functions are still names only here.

### Goose: a struct field named like a type of its package (2026-10-26, client-go survey C5)

- **Missing.** In `S.TypeAssumptions` (in `S`'s namespace), a field type that is a package type of
  the same name as a field (`intstr.IntOrString`'s field `Type` of type `Type`) resolves to the
  field's projection (`(y : Type')` is `IntOrString.Type'`).
- **Needed by.** `k8s.io/apimachinery/pkg/util/intstr.IntOrString` (the DaemonSet's rolling-update
  fields).
- **Workaround here.** `intstr`'s structs axiomatized (`translate_types_except_structs`).
- **Proposed.** Qualify package-level types in the generated lemmas (`_root_.Perennial.<pkg>.T'`).
- **Status.** Not started.

### Goose: range over a string (2026-10-26, client-go survey C1)

- **Missing.** `for i := range s` over a string (`[unsupported]: range over string`).
- **Needed by.** apimachinery's `resourceversion.isWellFormed` (the consistency store's
  comparisons).
- **Workaround here.** `isWellFormed` names only (a trust-boundary spec, or a trusted model as the
  byte loop, which computes the same result).
- **Proposed.** Range over a string, stepping by `utf8` decoding (needs a model of
  `utf8.DecodeRuneInString`).
- **Status.** Fixed on Perennial's `lean` (`474911152`, with `wp_string_for_range`; in the pin since
  `edcadb1e5`); `isWellFormed` is still names only here.

### Tactics: `wp_apply` after an atomic spec applied with `iapply` (2026-10-27, client-go consistency)

- **Missing.** In a proof that applies a logically atomic spec (the `<<{ … }>>` triples of
  `Perennial/ProgramLogic/AtomicFupd.lean`) with `wp_bind; iapply spec $$ [...]`, a later
  `wp_apply lem $$ [...]` in the continuation (after the atomic update is closed) silently does
  nothing: no error at the tactic, the declaration reports only "unsolved goals" at its `by`, and
  `wp_apply_core` there fails with "unknown free variable" and "declaration has metavariables".
  Seen in `Proof/k8s_io/client_go/util/consistency/consistencyStore__WroteAt.lean` (the call of
  `ownerRecord.WroteAt` after `ensureWrittenRecord`'s atomic spec). `wp_apply` directly on the
  atomic spec has the same symptom.
- **Workaround here.** `wp_bind; iapply lem $$ [...]` for the later call too, then `inext; iintro`
  its postcondition.
- **Proposed.** Find the metavariable `wp_apply` leaves (probably the continuation `Φ` of the
  atomic spec, instantiated late, whose context then loses a local cleared by `wp_auto`), and make
  `wp_apply` support atomic specs directly.
- **Status.** Not started.

### Specs: `fmt`'s `ArgWf` for named non-integer basic types (2026-11-05, k8s etcd3 stage 7b)

- **Missing.** `fmt.wp_Sprintf` admits a named type's argument only when its underlying type is an
  integer (`IsIntArgType`, with `fmt.NoFmtMethods`); `types.UID` (`type UID string`, no methods) is
  formatted by `storage.Preconditions.Check` with `%v`.
- **Workaround here.** `types.UID` added to `fmt.methodlessNamedTypes`, the list of the trust-boundary
  axiom `fmt.SprintfNamed.wp_proof` (`Spec/fmt/SprintfNamed.lean`), next to `LeaseID`.
- **Proposed.** `ArgWf` admits a named type with `fmt.NoFmtMethods` whatever its basic underlying
  type (the output of a non-integer one arbitrary from its directive on, as `SprintfOut.other`); with
  `NoFmtMethods` from goose's method sets, the list and the axiom go.
- **Status.** Not started.

### Specs: `fmt`'s `ArgWf` for a method-less map argument (2026-10-27, client-go informers)

- **Missing.** Perennial's `fmt.Errorf` spec requires each argument well formed (`ArgWf`), which
  has no case for a value of a named map type without a `String`/`Error` method (`sets.Set[string]`,
  printed with `%v`). client-go's `AddIndexers` passes two.
- **Workaround here.** `Proof/k8s_io/client_go/tools/cache/ErrorfSet.lean` proves
  `wp_Errorf_setArgs` from the model with the faithfulness of that case as its premise.
- **Proposed.** An `ArgWf` case for maps whose type has no formatting method (the value printed
  structurally; the spec needs only that `Errorf` returns a non-nil error).
- **Status.** Not started.

### Tactics: `wp_load` misses a field of a whole-struct points-to with a generic-struct field (2026-10-27, client-go listers)

- **Missing.** With `s ↦{dq} (⟨ri⟩ : daemonSetLister)` in context (a struct whose one field is the
  generic `listers.ResourceIndexer[T]`), `wp_load` of `s.[daemonSetLister, "ResourceIndexer"]`
  reports "could not find a points-to in context covering the address", although the generated
  `AccessStrict` instance `daemonSetLister_access_load_ResourceIndexer` exists and applies when
  used by hand.
- **Workaround here.** Specs state the field points-to (`s.[daemonSetLister, "ResourceIndexer"] ↦
  ri`); constructors split the allocation with the instance's `access_strict`
  (`Proof/k8s_io/client_go/listers/apps/v1/NewDaemonSetLister.lean`).
- **Status.** Not investigated.

### Tactics: `iframe` leaves persistent hypotheses unframed after `iapply` of an atomic spec (2026-10-27, client-go listers)

- **Missing.** After `iapply (atomicSpec ...) $$ [Hr] HAU`, the precondition goal
  `isPkgInit ∗ isCache … ∗ typedOK …` (all available as `□` hypotheses) is not closed by `iframe`;
  `isplitr; iexact H` per conjunct is needed. Similarly after `wp_apply (wp_Pop …) $$ [Hpop Hdn]`
  for `isFIFO`/`processOk` in `controller__processLoop.lean`.
- **Status.** Not investigated.

### Semantics: `sync.Mutex{}` (2026-10-26, client-go workqueue)

- **Missing.** `sync.Mutex`'s model has underlying type `go.bool` (`TrustedCode/sync.lean`), and a
  composite literal at a named type steps at its underlying type, so `&sync.Mutex{}` reaches
  `CompositeLiteral go.bool (LiteralValueV [])`, which has no step (composite literals step at
  structs, arrays, slices, maps and pointers only).
- **Needed by.** client-go's `newQueue` (`sync.NewCond(&sync.Mutex{})`); the backend's
  `backend.wp_mutexLit` (`storage/backend/MutexLit.lean`) states the same gap as an axiom.
- **Workaround here.** A hypothesis class, `EtcdGrove.MutexLitSemantics`
  (`Proof/sync/MutexLitSemantics.lean`, in `SEM_PREMISES`): the empty literal of `go.bool` is
  `false`.
- **Proposed.** An empty composite literal of a type whose underlying type is not a struct (and
  has no literal rule) is its zero value; or `sync.Mutex`'s model as a struct.
- **Status.** Not started.

### Semantics: `float64(c)` of an untyped integer constant (2026-10-27, client-go workqueue)

- **Missing.** `backoff > math.MaxInt64` with `backoff : float64` is emitted as `Convert
  go.untypedInt go.float64 #c` at run time, and `UntypedIntSemantics` converts untyped integers to
  the integer types only.
- **Needed by.** client-go's `TypedItemExponentialFailureRateLimiter.When`.
- **Workaround here.** A hypothesis class, `EtcdGrove.UntypedIntToFloat64Semantics`
  (`Proof/k8s_io/client_go/util/workqueue/UntypedIntToFloat.lean`, in `SEM_PREMISES`): it steps to
  an uninterpreted float of the integer, as `float64(n)` of a typed integer does.
- **Proposed.** Goose folding the constant conversion, or the step in `UntypedIntSemantics`.
- **Status.** Not started.

### Specs: `container/heap` (2026-10-27, client-go workqueue)

- **Missing.** No specs of `container/heap` in Perennial. This repository states `heap.Push`,
  `heap.Fix` (the lessor's), `heap.Init`, `heap.Pop` (the work queue's) as trust-boundary axioms
  over the contract `heap.heapIface` (`Proof/container/heap/Defs.lean`); `Init` and `Pop` are
  stated up to a permutation (no heap order).
- **Proposed.** Proved specs in Perennial (the package is plain Go over `heap.Interface`).
- **Status.** Not started.

### Specs: `reflect`

- **Missing.** Perennial translates `reflect` (`Perennial/Code/reflect.lean`) but has no specs.
- **Needed by.** The k8s etcd3 store's unary methods: apimachinery's `conversion.EnforcePtr`
  (`reflect.ValueOf`, `Kind`, `Elem`) and `reflect.New(v.Type())` in `Delete` and
  `GuaranteedUpdate`; lists add `MakeSlice`, `Append` and `Value`'s methods (`growSlice`,
  `getNewItemFunc`). Plan phase 1.
- **Workaround here.** None yet; local trust-boundary specs if the Perennial change is not ready
  by phase 1.
- **Proposed.** Specs of the `reflect` subset generic code uses on pointers and slices: `ValueOf`,
  `TypeOf`, `Kind`, `Elem`, `New`, `Indirect`, `MakeSlice`, `Append`, `Len`, `Cap`, `Set`,
  `Interface`, over Perennial's model of interface values and types.
- **Status.** Not started.

### Standard library: packages not translated, and functions without specs

- **Missing translations.** `encoding/json`, `encoding/base64`, `path` (Perennial translates
  none of them; `iter` is Perennial's since the pin `edcadb1e5`, 2026-10-27).
- **Missing specs.** (2026-10-26) client-go's leaf libraries add `sync.WaitGroup.Go`,
  `container/heap.Init`/`Pop`, `math.Pow`, `os.LookupEnv`, `time.Time.Add/Before/Sub`,
  `math/rand.New`/`Rand.Float64` (the full list per package: `notes/k8s-clientgo-goose.md`).
  Earlier: `strconv.ParseInt`, `ParseUint`, `FormatInt`, `FormatUint`, `ParseBool`;
  some of `strings`; `fmt.Sprint`, `Sprintln`, `Fprintf`; `os.Getenv`; `json.Marshal`,
  `Unmarshal`; `base64.RawURLEncoding`'s methods; `path.Join`, `Clean`. (2026-10-24, rafthttp stage 7d)
  `io.MultiReader` (names-only: an axiom here, `Proof/io/MultiReader.lean`, stated over the
  snapshot pipe's `readerStreams`); `bytes.Buffer`'s methods (a struct without method bodies: the
  k8s-etcd3 axioms `ownBuffer_new` and `Buffer.Write`, which the snapshot sender also uses). (2026-10-25,
  rafthttp stage 7e) `fmt.Sprintf` of non-basic arguments (`fmt.SprintfArgs`, over `fmt.argsOk`, as
  `Printf`/`Errorf`: Perennial's `wp_Sprintf` takes basic types only); `(*time.Duration).String`
  (`time` is translated without `Duration.String`, so its pointer wrapper is missing too).
- **Needed by.** The k8s etcd3 store and `k8s.io/apiserver/pkg/storage`: continue tokens (JSON in
  base64), `prepareKey` (`path`), resource versions (`strconv`), `GetList`'s iterators (`iter`).
- **Workaround here.** The three packages names-only in this repository's configuration (survey
  branch: `Code/encoding/{json,base64}.toml`, `Code/path.toml`); specs as
  needed, local until proposed.
- **Proposed.** Translations (or trusted models) of the three in Perennial's standard library, and
  the specs above, each with the subset proofs use.
- **Status.** Not started. (2026-10-22) Local trust-boundary specs here for `strings.HasSuffix`,
  `strings.Contains` (`Spec/strings/`). (2026-10-23) Also `strings.TrimSuffix` (`Spec/strings/TrimSuffix.lean`: Perennial's
  `strings` has no body for it) and `path.Join` for the one case `etcd3.New` uses
  (`Spec/path/Join.lean`: `Join(["/", p])` of a clean absolute `p` is `p`, `PathCleanAbs`).
  (2026-10-24, the auth plan's A3) The server's `UserAdd`/`UserChangePassword` call
  `base64.StdEncoding.EncodeToString`: a package *variable* of the names-only package, whose load
  needs a points-to the package's fact (`True`) does not give; they stay names only until a model
  of `encoding/base64` (and of `golang.org/x/crypto/bcrypt`'s `GenerateFromPassword`) exists.

### `reflect.Value` held in a variable: its typed points-to is `sorry`

- **Limitation.** `reflect` is names-only, and its axiomatized types' generated instances
  (`GeneratedProof/reflect.lean`: `Value_typed_pointsto`, `Value_into_val_typed`) are
  `sorry -- axiomatized type`. Any function that stores a `reflect.Value` in a variable (a
  parameter is one: Goose allocates it) needs them, so a proof of it rests on a `sorry`.
- **Needed by.** The k8s etcd3 store's `Delete` and `GuaranteedUpdate`: `v, _ :=
  conversion.EnforcePtr(out)` is passed to `conditionalDelete`, `deleteOnce`, `updateOnce`,
  `getCurrentState`, `stateFromEtcdResponse`, which make a fresh object with
  `reflect.New(v.Type()).Interface().(runtime.Object)` (`notes/k8s-etcd3-plan.md`, "What blocks
  where"). `Get` and `Create` do not use it.
- **Proposed.** An opaque `reflect.Value` with real instances (a translated struct whose fields
  are not modelled, or a hand-written typed points-to that only allows moving the value), plus
  specs of `Value.Addr`/`Type`/`Interface`/`Elem`/`Set` and `reflect.New` for pointer-to-struct
  values. Designed and reviewed on its own (Perennial's trusted base).
- **Workaround here** (the user's choice, 2026-10-22: axioms here now, a trusted model with proved
  reasoning principles later). `Proof/reflect/Values.lean`: the two instances as axioms of higher
  priority than the generated `sorry`s; opaque predicates relating a `Value` to a Go type and a
  location (`reflElem`, `reflPtr`, `reflType`) and `reflect.New`'s allocation (`reflNew`, with
  `reflNew_pointsto`); the specs of `reflect.New`, `Value.Addr`/`Type`/`Interface` and
  `conversion.EnforcePtr` as axioms (`Spec/reflect/`, `Spec/k8s_io/apimachinery/pkg/conversion/`).
  Go's `reflect` works on the runtime's representation (type descriptors, `unsafe.Pointer`,
  interfaces as two words), outside the semantics, so the model will be trusted, its principles
  proved from it.
- **Status.** Not started in Perennial.

### `reflect.Type` in a struct field: the struct's instances rest on a `sorry` (2026-10-27, client-go reflector)

- **Limitation.** `reflect` is names-only (`Perennial/Code/reflect.toml`: `translate = ["!*"]`), so
  `reflect.Type` (a Go *interface* type) is an axiomatized Lean type whose generated instances
  (`GeneratedProof/reflect.lean`: `Type'_typed_pointsto`, `Type'_into_val_typed`) are
  `sorry -- axiomatized type`. A translated struct with a `reflect.Type` field gets its own
  instances from them when it is generated, so every proof that touches such a struct's fields
  reaches the `sorry`s; a later higher-priority instance (as `Proof/reflect/Values.lean` does for
  `reflect.Value`) does not help, the struct's instance is already elaborated.
- **Needed by.** client-go's `Reflector` (`expectedType reflect.Type`): the reflector's proofs
  (`Proof/k8s_io/client_go/tools/cache/Reflector__*.lean`, phase 4 of
  `notes/k8s-daemonset-plan.md`) rest on the two `sorry`s (in `etc/tcb-baseline.txt` and the
  client-go collections since 2026-10-27).
- **Proposed.** Translate `reflect`'s type declarations (`translate_types`, or `Type` alone: an
  interface type, whose values Perennial represents as any interface's), keeping its functions
  names only. A Perennial change, designed and reviewed on its own.
- **Two incoherent instances (2026-11-10, k8s 7e-2).** `Proof/reflect/Values.lean` now gives
  `reflect.Type'` a higher-priority `TypedPointsto` (`type_typed_pointsto`: `heapTypedPointsto` from
  the axiom `type_intoVal_inj : go.IntoValInj reflect.Type'`, so it depends on `hG` and `intoVal`) and
  an `IntoValTypedUnderlying` axiom (`type_into_val_typed`), so that `getNewItemFunc` (which
  allocates a `reflect.Type` cell) no longer reaches the generated `sorry`s. The generated
  `Type'_typed_pointsto`/`Type'_into_val_typed` still exist, and the reflector's
  `Reflector.expectedType` field was elaborated against them: the two instances are incoherent
  (a proof that mixes a struct's `Type'` field with a `Type'` cell would not connect them). Not
  unsound, but only a fix at the source (above) gives one instance.
- **Status.** Not started.

### Goose: a names-only package's constants are values of unknown shape

- **Need.** A names-only package's constants are axiomatized `val`s
  (`k8s.io/apiserver/pkg/features.AllowUnsafeMalformedObjectDeletion`). Binding one (`let x :=
  features.F`, as Goose translates a call argument) is a beta step whose premise is that the value
  is not a panic (`pure_beta`), which nothing says of an axiom.
- **Workaround here.** `Proof/k8s_io/apiserver/pkg/features/Values.lean`: a trust-boundary axiom
  that this constant is not a panic value, used by `store.Delete`'s proof (`wp_pure` with it in
  the context).
- **Proposed fix.** Goose could translate a names-only package's constants (their values are
  constant expressions, never code), or emit with each axiomatized constant the fact that it is a
  value of its Go type (`#(c : V)` for a Lean type `V` of the constant's type), from which
  `isPanic_intoVal` gives the premise.
- **Status.** Not started.

### Goose: interface types whose methods name an alias stay axiomatized (G1)

- **Limitation.** Goose's `getStructInfo`/type translation does not see through type aliases
  (`notes/k8s-etcd3-goose.md`, G1): a type naming an alias is skipped by `translate_types`, so it
  is axiomatized. (2026-10-23) `k8s.io/apiserver/pkg/storage/feature.FeatureSupportChecker`
  (`CheckClient(ctx, client, storage.Feature)`, `storage.Feature = string`) stays axiomatized even
  with its imports configured (G4's fix made `client` concrete).
- **Needed by.** `etcd3.New` calls `feature.DefaultFeatureSupportChecker.CheckClient(...)`.
- **Workaround here.** The `storage/feature` package's fact (`checkerInit`,
  `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean`) is the call's own WP, the variable's load
  included, so no proof touches the axiomatized type's `sorry` instances.
- **Proposed fix.** `types.Unalias` in Goose where it resolves a named type (G1).
- **Status.** Not started. G1's fix (`getStructInfo`, Perennial `898c0ddc5`) covers field
  selection only: at that pin `feature.FeatureSupportChecker` is still axiomatized.

### `≤u` has no transitive instance (conversion to a defined type of a named interface)

- **Limitation.** `InterfaceSemantics.convert_to_interface` needs `to ≤u go.InterfaceType elems`;
  `≤u` (`UnderlyingEq`) is found from one `<u` step only (`unfold_to_underlying_eq`,
  `Golang/Theory/PostLifting.lean`), and `UnderlyingDirectedEq`'s docstring mentions a transitive
  instance that does not exist. A defined type of a named interface (`type Codec Serializer` in
  `k8s.io/apimachinery/pkg/runtime`: `Codec <u Serializer.ty <u interface{Encoder; Decoder}`) then
  has no conversion step.
- **Needed by.** The k8setcd3 driver's `Main` (`etcd3.New(..., codec{}, ...)`, 2026-10-23).
- **Workaround here.** A local instance proved from the two `TypeAssumptions` (`haveI` in
  `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Main.lean`); no axiom. Also met by
  client-go's pager (2026-10-28, `k8s-daemonset-proof`): `meta.List` (`type List
  metav1.ListInterface`), two named types deep; a local instance `metaList_underlying`
  (`Proof/k8s_io/client_go/tools/pager/Defs.lean`), no axiom.
- **Proposed fix.** An instance `[t <u t'] [t' ≤u t''] : t ≤u t''` (in place of
  `unfold_to_underlying_eq`, terminating since `<u` is directed), or the docstring corrected.
- **Status.** Not started.

### `time.Time.IsZero` has no model

- **Missing.** Perennial's `time` translation at the pin has no `(*Time).IsZero` method, so a
  call to it does not step.
- **Needed by.** client-go's `retryWithDeadlineImpl.After` (`tools/cache/retry_with_deadline.go`:
  `if r.firstErrorTime.IsZero() ...`), called by `Reflector.watch` on every watch error
  (2026-10-28, `k8s-daemonset-proof`, phase 4 fifth round).
- **Workaround here.** `retryWithDeadlineImpl.After`'s spec is a named hypothesis (`?` in
  `etc/link-lean-first-k8scache.txt`, `links_pending`): it updates the retry's own fields and
  returns; no axiom.
- **Proposed change.** `Time.IsZero` in Perennial's `time` model (true exactly of the zero value)
  with its spec beside `Time.Sub`'s.
- **Status.** Not started.

### The type set of an interface with an embedded interface

- **Limitation.** `typeSetTermContains t (TypeTerm t')` is `t = t'`
  (`Golang/Defn/Interface.lean`), and Goose translates an embedded interface (`type Serializer
  interface { Encoder; Decoder }`) as `TypeElem [TypeTerm Encoder.ty]`. Go's type set of a term
  that is an interface is that interface's type set, so in the model no concrete type is in
  `Serializer`'s (or `Codec`'s) type set: a type assertion to such an interface panics where Go
  succeeds (the model is less defined, so proofs stay sound, but such an assertion cannot be
  verified).
- **Needed by.** Nothing yet (found 2026-10-23 while converting the driver's codec to
  `runtime.Codec`; conversions and method calls do not consult type sets).
- **Proposed fix.** In `typeSetTermContains`, a term whose underlying type is an interface
  contributes that interface's type set (`typeSetContains t t'`); a semantics change, through
  Perennial's `fix-semantics` workflow.
- **Status.** Not started.

### `os.Getenv`, `strconv.ParseBool`, `strconv.ParseInt` have no specs

- **Limitation.** All three are names-only in Perennial (no body, no spec).
- **Needed by.** `k8s.io/apiserver/pkg/storage/etcd3`'s `init` (`watcher.go`: whether
  `KUBE_PANIC_WATCH_DECODE_ERROR` parses as true), which the driver's initialization runs.
  (2026-10-27, branch `k8s-leaf-cache`) `ParseInt`: client-go's thread-safe store
  (`tools/cache`, `parseRVForMetricsWithTruncation`, the resource-version metric).
- **Workaround here.** Trust-boundary specs (`Spec/os/Getenv.lean`, `Spec/strconv/ParseBool.lean`,
  `Spec/strconv/ParseInt.lean`, axioms in `Proof/`): each returns some value.
- **Proposed fix.** Specs in Perennial (`ParseBool` can be translated: it is pure).
- **Status.** Not started.

### Goose: a type defined over a type of a package the file does not import (G3)

- **Limitation.** `grpclog.LoggerV2` is `type LoggerV2 internal.LoggerV2`; `grpclog/internal` is
  not translated, so `LoggerV2` is axiomatized and a conversion to it does not step.
- **Needed by.** `etcd3`'s `init` (`logger.go`: `grpclog.SetLoggerV2(klogWrapper{})`).
- **Workaround here.** `etcd3`'s `klogWrapper_toLoggerV2` (generated into its `Init.lean` from
  `etc/gen-init.py`): the conversion returns some interface value.
- **Proposed fix.** Translate `grpclog/internal` names-only (configuration here), or G3's general
  fix in Goose (`notes/k8s-etcd3-goose.md`).
- **Status.** Not started.
- **Also `hash` (2026-10-22, branch `kvhasher`).** Perennial does not translate `hash`, so mvcc's
  `kvHasher` (a `hash.Hash32` field) was an axiomatized type with `sorry` instances, the
  repository's last two `sorry`s. Workaround here: `hash` types-only in this repository
  (`Code/hash.toml`, `-lean-root hash=`, as `encoding/hex`), which makes Goose translate
  `kvHasher` as a struct. Proposed: `hash`'s interfaces in Perennial's standard library (and
  `hash/crc32`'s model, which would make `newKVHasher`, `kvHasher.WriteKeyValue` and `Hash`
  provable); then this repository's `hash` translation goes.

### `encoding/binary`'s `Write`/`Read`, and protobuf at the bytes (2026-10-22, rafthttp stage 3, branch `rafthttp-plan`)

- **Missing.** Perennial translates `encoding/binary`'s byte orders but not `Write`/`Read`
  (names-only: they go through `reflect`); and `google.golang.org/protobuf` is names-only, so its
  `Size`/`Marshal`/`Unmarshal` have no spec there.
- **Needed by.** rafthttp's message codecs (`messageEncoder.encode`, `messageDecoder.decodeLimit`,
  the msgappv2 pair next): a length prefix written with `binary.Write` and read with `binary.Read`,
  and raft's messages marshalled.
- **Workaround here.** Trust-boundary axioms: `Spec/encoding/binary/{WriteUint64,WriteUint8,
  ReadUint64}.lean` (Go's fast path of an integer, stated over the writer's `Write` / the reader's
  `io.ReadFull`), and generic protobuf specs over a per-type wire model (D38a:
  `Proof/google_golang_org/protobuf/proto/InvProto.lean`'s `PbType`, `Spec/google_golang_org/
  protobuf/proto/{Size,Marshal,Unmarshal}Pb.lean`).
- **Proposed.** Specs of `binary.Write`/`Read` of fixed-size integers in Perennial (or a trusted
  model of their fast path); and, if the generic vocabulary proves itself across the codecs and
  the older per-type specs move onto it, `PbType` and its three specs as Perennial's protobuf
  boundary.
- **Status.** Not started.

### The `WaitGroup` join idiom's `Add(n)`, and `Sprintf` of a `Stringer` (2026-10-23, rafthttp stage 4d, branch `rafthttp-plan`)

- **Missing.** (1) `sync.join.WaitGroup.wp_Add_of` (and `sync.tokJoin`'s) covers `Add(1)` only,
  though `sync.WaitGroup.Add.spec` takes any delta. (2) `fmt.wp_Sprintf` admits arguments of
  predeclared basic types only (`fmt.ArgsWf`): an argument with a `String` method (a
  `types.ID`) is outside it, though Go's formatting then only calls that method.
- **Needed by.** (1) rafthttp's `pipeline.start`, `p.wg.Add(connPerPipeline)` (`4`). (2) rafthttp's
  `peerStatus.deactivate`, `Sprintf("failed to %s %s on %s (%s)", action, s.id, source, reason)`.
- **Workaround here.** (1) `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/
  WaitGroupAdd.lean`, `wgJoin_wp_Add4_of` (`wp_Add_of`'s proof with four ghost steps; proved, no
  trust). (2) `Spec/fmt/SprintfID.lean`, a trust-boundary axiom for `types.ID` arguments (as
  `SprintfNamed`, `SprintfClientPtr`).
- **Proposed.** (1) `wp_Add_of` for a delta `n` (`0 < n`, the bound `num_added + n < 2^31`),
  giving `n` `ownDone`s (a `[∗list]` over `List.replicate n`); the `Add(1)` statement derived.
  (2) `wp_Sprintf` over arguments whose `String`/`Error` method has a given spec (a WP returning
  some string), covering `Stringer`s generally.
- **Status.** Not started.

### `fmt.Errorf`'s result: a fresh pointer error (2026-10-23, rafthttp stage 4e, branch `rafthttp-plan`)

- **Missing.** `fmt.Errorf.spec` gives only that the error's `Error()` returns some string; it does
  not say the error is a fresh pointer (`*fmt.wrapError` or `*errors.errorString`: `IsPointerError`,
  as `errors.New.spec` says), so a caller cannot show it differs from a package's error variable.
- **Needed by.** rafthttp's `checkPostResponse`, whose `fmt.Errorf` errors must not be
  `errMemberRemoved` (`postErr`: `pipeline.post`'s caller reports only that one on `errorc`).
  (2026-11-04, bbolt U4c) bbolt's `DB.allocate` compares `DB.mmap`'s error (an `fmt.Errorf`
  error on its error paths) with `ErrMaxSizeReached` (`err == ErrMaxSizeReached`, stuck unless a
  side's dynamic type is known comparable): `Mmap/Remap`'s `DB.mmap.spec` states its error
  `errPtrTyped` instead, which `fmt.Errorf.spec`'s post would give with `IsPointerError`.
- **Workaround here.** None yet: `checkPostResponse` is a spec only. (Stage 5e-3) The stream
  reader's `dial` uses a local trust-boundary spec, `Spec/fmt/ErrorfPlain.lean`: with no `%w` the
  error is an `*errors.errorString` (Go's `Errorf` returns `errors.New(s)`), whose `Error()`
  returns the message, so a leaf of an error tree (`errors.Is` of it, in `run`).
- **Proposed.** `fmt.Errorf.spec`'s postcondition with `IsPointerError err` (for a format without
  `%w`), as `errors.New`'s; or the `*errors.errorString` form above.
- **Status.** Not started.

### `strings.TrimSuffix` without a spec (2026-10-23, rafthttp stage 5e-3, branch `rafthttp-plan`)

- **Missing.** Perennial translates `strings.TrimSuffix` names-only and has no spec for it
  (`TrimPrefix` has one).
- **Needed by.** rafthttp's `streamReader.dial` (a `412`'s body, `TrimSuffix(string(b), "\n")`).
- **Workaround here.** `Spec/strings/TrimSuffix.lean`, a trust-boundary axiom: some string.
- **Proposed.** A translation or model of `TrimSuffix` with a spec (the string without the suffix,
  if it ends with it), as `TrimPrefix`'s.
- **Status.** Not started.
### Tactics: framing up to the projections of a structure instance

- **Missing.** The proof mode's matching of a hypothesis against a goal (`iframe`, the `$$`
  arguments of `iapply`/`ihave`) does not see through the projection of an anonymous constructor:
  `dghostVar (γ.withPhys p).rst dq v` does not frame `dghostVar γ.rst dq v`, nor `crevFrozen γ`
  the premise `crevFrozen (γ.withPhys p)`, though they are definitionally equal (`rfl`) and Lean's
  `exact` accepts them.
- **Needed by.** The store's names at the current physical names (`mvcc.StoreNames.withPhys`,
  D22 receiver epochs S5b, 2026-10-22): every proof that works at `γ.withPhys p` and uses a
  logical fact of `γ`.
- **Workaround.** Explicit rewrites by `rfl` lemmas (`mvcc.isStore_withPhys`, ..., the
  `withPhys_simp` tactic of `InvStore.lean`), lemmas bridged in term mode
  (`readerPool_checkout_p`, `revMuInv_open_cur`), and `revMuBody` with separate logical and
  physical names.
- **Proposed.** iris-lean's (not Perennial's) frame and specialization matching could unify up to
  `whnfR` of projections of constructor applications (structure eta), as Lean's `isDefEq` does at
  reducible transparency for `instances`. Not proposed yet: to be weighed against the cost of
  every match.
- **Status.** Open (observed; no change drafted).

### Context: `Canceled`'s message cell in `context`'s package facts

- **Missing.** Perennial's context initialization allocates `Canceled` with `errors.New("context
  canceled")` and persists the `errorString`'s `s` field, but `isInit`'s `"#HCanceled"` keeps only
  `isTypedErr`: a proof cannot tell `Canceled` apart from another `errors.New` value (D37, D19k).
- **Needed by.** `ctxErrClientAllW_of` (`client/v3/ErrorsNewOk.lean`): a context's error is no
  caller's `errors.New` value (`errCellOk`), for the Kubernetes driver's sentinel errors.
- **Workaround here.** `context.ErrAny` (this repository's trust-boundary axiom) states the cell
  of `Canceled`'s value and that `DeadlineExceeded`'s is no `*errorString` (true of Go).
- **Proposed change.** `"#HCanceled"` with the cell (`x.[errorString, "s"] ↦□ "context
  canceled"`, as this repository's `errStrCell`), and `"#HDeadlineExceeded"` with its dynamic type
  (`deadlineExceededError`); then `ErrAny` drops the two facts.
- **Also needed by** (2026-10-27). Now that method sets are known (pin `6b58510f9`), this is all the
  premises `EtcdGrove.ContextReadErrs` and `ContextErrsClient` of the server examples' closed
  theorems still need: the dynamic types of the two values (then their method-set parts follow by
  `go_type_set`).
- **Status.** Not started (found 2026-10-23).

### `encoding/base64` (the auth plan's E2u, 2026-10-26; E2x)

- **Missing.** Perennial has no `encoding/base64`, not even names-only. etcd's
  `EtcdServer.UserAdd` and `UserChangePassword` hash the password with bcrypt and put the hash in
  the request base64-encoded (`v3_server.go`); the k8s etcd3 store's continue tokens are JSON in
  base64.
- **Workaround here** (E2x, 2026-10-26; the user chose this over a Perennial model). The package is
  names-only in this repository's configuration (`Code/encoding/base64.toml`, the k8s-apiserver
  project's translation; the etcd project maps `encoding/base64=` to it, `etc/goose.py`). Its
  package fact (`Proof/encoding/base64/Base.lean`, `base64Init`) says `StdEncoding` holds a fixed
  `*Encoding` whose `EncodeToString` returns the opaque `encoding.base64.stdEnc` of its argument's
  bytes; the trust-boundary axiom `StdEncoding_init` (`Proof/encoding/base64/Init.lean`,
  `etc/gen-init.py`) establishes it. `auth.stdB64Enc` is that `stdEnc`, and `selectPassword`'s
  boundary spec says its decoding of such an encoding has no error, so `EtcdServer.UserAdd` is
  proved to propose a `pwSure` request (`server_user_add_sure`).
- **Proposed change (later).** `encoding/base64` in Perennial: `StdEncoding` (a package variable
  with its fact), `EncodeToString` and `DecodeString` with a model of the standard encoding (or at
  least `DecodeString (EncodeToString b) = (b, nil)`), translated or as trusted models. It would
  turn `StdEncoding_init`'s method clause and `selectPassword`'s decode clause into theorems, and
  serve the k8s etcd3 store's continue tokens.

### `wp_load` of a struct field through a fractional points-to (2026-10-27, DaemonSet plan phase 3)

- **Missing.** Loading a field (`![t] (StructFieldRef T f l)`) needs `l`'s struct points-to at
  fraction 1 for `wp_auto` to split it; at a fraction `dq` (a persistent configuration, a shared
  `*Preconditions`) the load is stuck.
- **Workaround here.** Persistent structs are stated field by field (the model's `cfgAt`); a
  fractional one is split by `iStructNamed` and recombined with `typedPointsto_combine` around the
  loads (`Server.remove`'s preconditions, the `ObjectMeta` accessors).
- **Proposed change.** The field-access instance (`solve_pointsto_access_struct`) at any fraction.

## Landed

### `Context.Value` at keys other than `&cancelCtxKey`; goose's multi-type type-switch case (landed 2026-11-08, Perennial `f137bdd8a` and `ddc0f0acc`; pin bumped 2026-11-08)

- **Was missing.** (1) Perennial's `context` specs gave `Value` only at `&cancelCtxKey`, and
  `WithCancel`'s posts dropped the new context's read-only parent field, so no proof could follow
  `value(c.Context, key)` (sweep repairs 1 B2-F1; k8s 7f P-RL1). (2) goose translated a type-switch
  case `case T1, ..., Tn:` testing `T1` twice and never `Tn` (`typeSwitchStmt`'s `getCond(i)` over
  `c.List[1:]`), unsound when the case body panics; found writing (1).
- **Landed in Perennial.** `f137bdd8a` (fix-semantics Case 35, signed off by the user): `getCond(i +
  1)`, the semantics test `testTypeSwitchLastType`, the unittest `multiTypeSwitchLast`; only
  `context.value` and goose's unittest re-translated (no translation in this repository has a
  multi-type case: the pin bump's `etc/goose.py` changed no file). `ddc0f0acc`
  (`docs/design/context-value.md`): `Proof/context/CtxValue.lean`, `ctxValue x k R` (`x.Value(k)`
  and `context.value(x, k)` return a result in `R`), `wp_value`, `ctxValue_Value`, the laws
  `ctxValue_{background,todo,cancel,timer,valueCtx,other}` (L2/L3 for a key that is not a `*int`,
  `notIntPtrKey`), and `ctxValueFrom parent ctx'` in the posts of `WithCancel.spec`,
  `wp_WithCancel_any`, `wp_WithCancel_Background`, `WithDeadlineCause`/`WithDeadline`/`WithTimeout`
  and the `*_Background` deadline results.
- **Here.** The pin bump adapted nine destructuring patterns (the posts' new trailing conjunct);
  no statement changed. B2/B2b (the axioms `context.ValueStartTime`/`ValueKeepAlive`) use it next.

### Package initialization: a monotone package map; `os`'s initializers translated (landed 2026-11-03 to 2026-11-04; used here 2026-11-07)

- **Was missing.** (1) Perennial's `wp_initialize'` theorems returned an arbitrary package map, so a
  proof here could not keep "this package is initialized" across another initializer: the
  trust-boundary axiom `initLb_of_spec` (`Proof/runtime/PkgInitExt.lean`, D19e). (2) `os`'s
  initializer was untranslated: the axioms `os.opaqueInitsOk` (26 variable initializers),
  `os.initFuncsOk` (`init.0`) and `os.Stderr_init`, which every closed result through raft rests on.
- **Landed in Perennial.** `1aab4c42b`/`46e5bb5df`: `ownInitializing`'s map is a monotone ghost
  map, `initLb_of_initSpec` (any proof keeping `ownInitializing g` keeps its lower bound). The
  goose and standard-library work for `os`: `11ac2f242` (`internal/oserror`, `io/fs`'s variables),
  `37313e9d3`/`a2a531d4d`/`8b6fcecf7` (unnamed struct types, fix-semantics Case 30;
  `sync.OnceFunc`/`OnceValue`), `e109f7928`/`350766064` (an imported package's constant emitted
  as its value, Case 32: `runtime.GOOS` is `"linux"`, so `os` does not import `runtime`),
  `def87774c` (Case 33, the user's decisions: `syscall`'s `init.0`, the RLIMIT_NOFILE raise, a
  trusted no-op, `exec` being outside the model; `runtime_envs`/`runtime_args` an arbitrary
  `[]string`; `Stdin`/`Stdout`'s initializers trusted no-ops, the variables left unallocated, so
  code using them has no proof; `Stderr`'s allocates the variable with a fresh pointer that is not
  a `File`, because raft's logger stores `os.Stderr`).
- **Used here (2026-11-07, branch `os-init-lean`).** `initLb_of_spec` is a theorem
  (`etc/gen-init.py`: `initLb_of_initSpec`). This repository translates its own `os`, `syscall`,
  `io/fs` (project bboltfs, `os=` for every project), so Perennial's `os` work is mirrored in the
  local configurations rather than imported: `Code/{os,syscall,io/fs}.toml` translate the same
  initializers (and every type, `translate_types`), two new local packages `internal/poll` and
  `internal/syscall/unix` (Perennial's import Perennial's `syscall`, which must not share a closure
  with this repository's), the same trusted models in `TrustedCode/{os,syscall}.lean` (with their
  specs, `Proof/{os,syscall}/Models.lean`), and `etc/gen-init.py` steps for the five initializers.
  Gone: `os.opaqueInitsOk`, `os.initFuncsOk`, `os.Stderr_init`, `syscall.opaqueInitsOk`,
  `syscall.initFuncsOk`, `io.fs.opaqueInitsOk`. After the branch's review: `Stderr`'s model stores
  a `GoPrealloc` address (in `(0, maxAddr)`, no cell; not `Alloc #()`, whose cell a store could
  overwrite, nor `maxAddr + 1`, which a program walking addresses could tell from Go's), and
  `arbitraryStrings` may return `nil` or `[]string{}` (Perennial `69236efdb`).
- **Still open.** `syscall.Errno.Error` is still trusted (`Code/syscall.toml`; an arbitrary
  string): its body (`errors[e]`, else `"errno " + strconv.Itoa(int(e))`, Go 1.27.3) is now
  translatable, but its spec (`errno_stringMethodSpec`, `errnoErrOk`) then needs `isPkgInit syscall`
  for the `errors` table, which reaches bbolt's five `errnoErrOk` users and `os`'s `ErrorOk`/
  `OpenFile`.

### `time.isTicker` is forgeable by a struct copy (2026-11-03, branch `ticker-followups`)

- **Limitation.** Perennial's `isTicker t ch γ` (`Perennial/Proof/time/Base.lean`) is `C ↦□ ch ∗
  initTicker ↦□ true ∗ bag`, with no unforgeability token like `isTimer`'s `newTimerMade`. A copy
  `u := new(time.Ticker); *u = *t` meets it (both fields are read through `t`'s persistent
  points-tos and written into `u`), and the proved `Ticker.Reset` spec says `u.Reset(d)` returns,
  while Go fails: measured with go1.27.3, "fatal error: unlock of unlocked lock" (the runtime's timer
  state after the `Ticker` header is not copied). `u.Stop()` returned in the same experiment, but
  also runs the runtime's `stopTimer` on memory that is not a timer.
- **Needed by.** Nothing here copies a ticker; every client gets its ticker from `NewTicker`
  (`serverWatchStream.sendLoop`, `streamWriter.run`, `syncWatchersLoop`, `newRaftNode`, the auth
  token keeper, kvdurable's and kvreconf's replicas). The concern is the spec's soundness as a
  library spec.
- **Here.** Nothing: since 2026-11-03 this repository's own ticker axioms are gone (their `Reset`
  admitted a forged `v.C = t.C`, false of Go, `notes/decisions.md`, "The ticker where it is made")
  and the clients use Perennial's specs (proved from its trusted models until `432c32f28`, its
  axioms since).
- **Proposal.** An opaque `newTickerMade t` in `isTicker`, given only by `NewTicker`'s spec, as
  `newTimerMade` for timers.
- **Status.** Landed on Perennial's `lean` as `432c32f28`, design A: the trusted models of
  `NewTicker`, `Ticker.Stop` and `Ticker.Reset` removed, the three made axioms, and `isTicker`
  holding the runtime timer's `newTimerMade` (a copy has none). In the pin since 2026-11-04 (the bump
  to `4c8617a9e`, branch `pin-4c8617a9e`); nothing here needed a change for it.

### The thread and receipt bounds as instances (2026-11-01, bounds plan B1; landed `6e3ca6ca3`)

- **Limitation.** A proof needing `threadBound GF` or `receiptBound GF` small took the bound as a
  premise, restated by every spec up to the adequacy theorem (46 Spec files for the thread bound,
  the `threadBound`/`receiptBound` chain in 20; `notes/bounds-plan.md`).
- **Change.** `Perennial/ProgramLogic/Bounds.lean`: the `Prop`-valued classes `ThreadBoundLe GF k`
  and `ReceiptBoundLe GF k`, with `le`/`le_of`/`lt_of`/`weaken` and `of_eq` for the adequacy
  theorem (an example in `ThreadTokensTest.lean`; the proof reference's thread-token section).
  Nothing trusted. Landed as Perennial `6e3ca6ca3`; the pin moved to it on 2026-11-01.
- **Follow-up, `pow_succ`** (branch `bound-classes-pow`): an instance at `2 ^ e` gives one at
  `2 ^ (e + 1)` by instance search, so each spec states its own power of two.
- **Use here.** B1: each spec's section takes the instance at the bound its proof needs, the specs
  drop the premises, and each closed result builds its instances from its adequacy choice.

### `fmt.Sprintf`: `%x` of an integer, and named integer types (2026-10-31)

- **Missing (at the pin `6da88b280`).** `fmt.wp_Sprintf` admitted arguments of predeclared basic
  types only (`fmt.ArgsWf`), and its `SprintfOut` left `%x` arbitrary: concurrency's
  `Sprintf("%s%x", pfx, s.Lease())` (a `LeaseID`, `type LeaseID int64` without methods) needed a
  trust-boundary axiom here, `fmt.SprintfNamed.wp_proof` (`Spec/fmt/SprintfNamed.lean`), whose
  output was arbitrary from the `%x` on.
- **Landed** (2026-10-31) in the pin `d62b13ac1`: `21b7311b5` (`%x` of an integer,
  `SprintfOut.hex`), `a4e2fb9e6` and `d62b13ac1` (a named integer type without formatting methods
  formatted as its underlying integer, through `TypeAssertUnderlying2`: `fmt.IsIntArgType`,
  `fmt.NoFmtMethods`, `SprintfOut.str_x_named_int64`). The axiom stays (still true, now with a
  determined output); dropping it needs `fmt.NoFmtMethods` of `LeaseID`'s type, from a
  `go.MethodSetIs` fact (`notes/STATUS.md`, "Perennial pin `d62b13ac1`").

### An interface embedding interfaces is an exact type set (2026-10-27, DaemonSet plan phase 3, gap C8)

- **Missing (at the pin).** Goose writes an interface that embeds interfaces with the embedded
  ones as type terms (`TypeElem [TypeTerm Object.ty]`), and `typeSetContains` reads a type term
  as that exact type: an assertion of a concrete type to such an interface panics in the
  semantics where Go's succeeds. The model API server's `copyObject`
  (`o.DeepCopyObject().(object)`, `object` embedding `runtime.Object` and `metav1.Object`) is a
  `sorry` (`notes/k8s-apimodel-goose.md`).
- **Landed** (in the pin since `6b58510f9`: `8ef540a62`, `d30f71f36`, an interface written as all its
  methods, method sets emitted). `copyObject` proved (2026-10-28, pin `ad74ee4f6`): `DeepCopyObject`'s
  spec per type and each pointer type's membership in `object` by `go_type_set`.

### Goose: a promoted method of a generic struct, through a pointer (2026-10-26, client-go survey C2)

- **Missing.** For a generic struct `S[T]` with an embedded field, the pointer receiver's unfolding
  of a promoted method (`ptr_M_unfold` in `S.TypeAssumptions`, `goose/lean_types.go:338`) names the
  struct as `ctx.glangType(t.Obj(), t)`, the generic type without its type argument
  (`StructFieldRef delayingType.ty ...`, ill-typed); the value receiver's case uses `ty`.
- **Needed by.** client-go's workqueue (`delayingType[T]`, `rateLimitingType[T]`,
  `TypedBucketRateLimiter[T]`): every call through `TypedRateLimitingInterface[T]` (the DaemonSet
  controller's `Get`, `Done`, `AddRateLimited`) resolves through these unfolds.
- **Workaround here.** The promoted methods excluded in `Code/k8s_io/client_go/util/workqueue.toml`
  (no `MethodUnfold` for them); their specs are hypotheses of the work queue's results that reach
  them (2026-10-27, `notes/k8s-clientgo-goose.md`, "What C2 leaves unlinked").
- **Proposed.** `glang.VerbatimExpr(ty)` for the struct there (one line; tried in a scratch copy of
  the pinned translator: workqueue's translation then elaborates, nothing else changes), with a
  Goose test of a generic struct embedding an interface.
- **Landed** (2026-10-28) in the pin `ad74ee4f6` (`21c6ea377`, `02109a551`: the unfolding names the
  instantiated struct; Case 18 of `fix-semantics`). The exclusions in `workqueue.toml` are gone and
  the 14 promoted methods proved (each the embedded queue's): the work queue's `Link.lean` has no
  pending hypotheses.

### Goose: a deferred call drops its variadic argument (2026-10-27, client-go workqueue)

- **Missing.** `deferStmt` (`goose/goose.go:2128`) calls the deferred function `$f` with
  `$a0 .. $a(n-1)` for the call's `n` syntactic arguments, but `callExprPrelude` binds the
  arguments as the callee's parameters: for a variadic callee, the variadic slice is one more name
  (`$a1`, `slice.nil` when no variadic argument is passed). So `defer
  utilruntime.HandleCrashWithLogger(logger)` (`HandleCrashWithLogger(logger, handlers ...)`)
  becomes `$f $a0`, a partial application: the deferred function never runs. (With variadic
  arguments passed, presumably the converse: more names applied than bound.)
- **Soundness.** The model is not Go's: a deferred variadic call does nothing in it, so a proof says
  nothing about that call's effects (a trust-base bug, not a missing feature).
- **Needed by.** client-go's workqueue: `delayingType.waitingLoop` (`defer
  utilruntime.HandleCrashWithLogger(logger)`) and `Typed.updateUnfinishedWorkLoop`
  (`HandleCrashWithContext`); client-go's informers: `processorListener.pop` and `run`
  (`HandleCrashWithLogger`, one `sorry`, `ListenerDefs.lean`'s `deferred_HandleCrashWithLogger`).
- **Workaround here.** None: `delayingType.waitingLoop`'s proof leaves its two returns (where the
  deferred call runs) `sorry` (gap G-defer-variadic) rather than prove the model's no-op.
- **Proposed.** In `deferStmt`, apply `$f` to the names the prelude binds (the callee signature's
  parameter count for a variadic call); a Goose test of `defer f(x)` with `f(x int, ys ...int)`.
- **Landed** (2026-10-28) in the pin `ad74ee4f6` (`87c564ff5`, Case 20 of `fix-semantics`: `defer` and
  `go` pass a call's arguments by parameter, the variadic slice included). The `sorry`s are gone:
  `waitingLoop`'s two returns and `cache.deferred_HandleCrashWithLogger` (the listeners' `pop` and
  `run` take `HandleCrashWithLogger`'s boundary spec, as `waitingLoop` does).

### Goose rejects a store of `*new(T)` (2026-10-28, merge of `lean` into `k8s-daemonset-proof`)

- **Limitation.** Goose at `edcadb1e5` refuses `(*q)[0] = *new(T)` (client-go's
  `util/workqueue/queue.go`, `queue[T].Pop`): its check R4 (`docs/design/unsafe-memory.md`,
  `modelcheck.Assign`) flags a copy of a `T` between two memory places, which gc does not copy by
  value when they partially overlap. `*new(T)` is a fresh allocation: it overlaps nothing, so the
  statement is safe and the semantics' by-value copy is exact.
- **Needed by.** The work queue's `Typed.Get` (every worker's `processNextWorkItem`); `queue.Pop`
  was translated and proved before the bump (`queue__Pop.lean`).
- **Workaround here.** `queue[T].Pop` translated names only (`!queue[T].Pop` in
  `Code/k8s_io/client_go/util/workqueue.toml`); its spec a named hypothesis in the work queue's
  `Link.lean`; no axiom. (Goose's `trusted` applies to functions and variables, not methods.)
- **Proposed change.** In `modelcheck.Assign`, treat a dereference of a fresh allocation
  (`*new(T)`, and a composite literal's address) as a value, not a memory place.
- **Landed** (2026-10-28) in the pin `ad74ee4f6` (`a56246e8a`: a place whose base is a fresh object is
  not reported). `queue[T].Pop` is translated again, its proof restored (`queue__Pop.lean`).

### Goose: an excluded method keeps its unfold; a method set in the receiver's type-parameter names (2026-10-28)

Two bugs of the method sets Goose emits since Perennial `8ef540a62` (pin `6b58510f9`), found
translating client-go's `util/workqueue` (nothing on `lean` translates it, so `lean`'s build does
not see them). Each makes the generated `Code/k8s_io/client_go/util/workqueue.lean` fail to
elaborate:

- **An excluded declared method.** With `!queue[T].Pop` in the package's `translate` list (the
  workaround above), Goose emits no `queue.Pop.impl` but still lists `Pop` in the pointer type's
  method set with `ptr_Pop_unfold : MethodUnfold ... (queue.Pop.impl T)`: an unknown constant. A
  names-only function gets no `impl` and no unfold; an excluded method should get the same (or an
  `axiom` impl, as an axiomatized declaration does).
- **The type parameter's name.** `type Typed[t comparable] struct {...}` with methods on
  `*Typed[T]` (`queue.go`): `ptr_method_set : ∀ (t : go.GoType), go.MethodSetIs (go.GoType.PointerType
  (Typed.ty t)) [(go!"Add", some (Signature [T] ...)), ...]` binds `t` but writes the signatures
  with the methods' receiver parameter `T`: unknown identifier. The signatures must be substituted
  into the type declaration's parameter names (Go lets each method rename them).
- **Workaround here.** None that keeps the pinned translation (`etc/goose.py --check`): the
  committed `workqueue.lean` is patched by hand (an `axiom queue.Pop.impl`, `T` renamed `t` in
  `Typed`'s method set) until a Goose fix lands and the pin moves. **Blocks the merge into
  `lean`**: CI's `goose.py --check` rejects the patched file.
- **Proposed change.** Both in Goose's method-set emission (`goose/`): skip a method the filter
  does not translate (or emit its axiom), and rename the receiver's type parameters to the type's.
- **Landed** (2026-10-28) in the pin `ad74ee4f6` (`e549a845a`: a method's filter name is `T.m`;
  `ad74ee4f6`: a generic type's method set in its own type parameters). The hand patch of
  `Code/k8s_io/client_go/util/workqueue.lean` is gone; `etc/goose.py --check` passes.

### GooseLang: extensions outside Perennial, named in the syntax (2026-10-27, branch `worktree-durable-kv`)

- **Missing.** An extension's operations were positions in the program's list of extensions
  (`ExtsOp exts`), so the trusted model of a Go function implemented with one needed
  `[ElemExt E]` (data: the position), which goose had to add to the generated `Assumptions` of
  the package and of every importer, from a closed table of extension packages in goose
  (`extMapping`), with prelude imports under `Perennial.`: a project could not define an
  extension of its own.
- **Needed by.** The durable-state extension `durableExt` (`GooseLang/Ext/Durable/`, the Go
  package `examples/lib/durable`) and `examples/raft/kvfile`.
- **Workaround here.** None (goose treats `examples/lib/durable` as any package); until the pin
  reached the change, the extension's Lean modules built only against it, so the branch waited.
- **The change.** Perennial branch `ext-names` (`6fa3a85cc`..`25bd32450`, off `lean` `edcadb1e5`; every
  module builds, goose's tests pass): `GooseExt` has a `name` (the Go package's path) and no
  type of operations; an operation is named by two strings, `ExternalOp ext op e` (stepping
  with the program's first extension named `ext`, by its step of `op`), an opaque value by the
  extension's name and its encoding (`ExtCode`, `extVal E v`); `ElemExt E` and `HasExt E` are propositions (closing off a program proves them by
  `rfl`); goose knows nothing of extensions (its table, the binders and the extension preludes
  are gone). It supersedes branch `goose-ext-flag` (goose's `-ext`, the first attempt).
- **Status.** Landed on Perennial's `lean` as `25bd32450` (2026-10-28), after the trusted-base
  review (verdict OK; its adversarial pass found that Grove's stutter made an unknown operation
  name safe instead of stuck, fixed in `25bd32450`: only Grove's operations, `groveOps`,
  stutter). In the pin since 2026-10-28 (the bump from `edcadb1e5`; no translation but
  `examples/raft/kvfile`'s changed).
### Goose: range over a function (`iter.Seq`/`iter.Seq2`)

- **Missing.** Goose rejects `for k, v := range f` when `f` is a function (`[unsupported]: range
  over func(...) (only integers, maps, slices, channels and arrays are supported)`). The iterator
  functions themselves, closures calling `yield`, already translate.
- **Needed by.** The k8s etcd3 store's `GetList` (`store.go:825`, over `pagedChunks` or
  `streamChunks`): every list. Blocks `notes/k8s-etcd3-plan.md`'s phase 5. The standard library
  increasingly returns iterators (`maps.Keys`, `slices.All`, ...).
- **Workaround here.** `store.GetList` names-only (survey branch's `etcd3.toml`); alternatives: a
  Goose fork of k8s.io/apiserver rewriting the loop, or a trusted model.
- **Proposed.** Desugar the loop as Go's compiler does: call the iterator with a closure for the
  body that returns `false` on `break`, and records a `return` (with its values) or a labelled
  `break`/`continue` in flags checked after the call; plus the runtime check that `yield` is not
  called after it returned `false` (Go panics).
- **Landed.** Perennial `caa9d07ee` (2026-10-26), after uniform function results (`2b17d5f09`);
  reached by the pin `edcadb1e5` (2026-10-27). (2026-10-31) `store.GetList` translated with it
  (`notes/k8s-etcd3-plan.md`, stage 7a).

### The type set of an interface with an embedded interface

- **Limitation.** `typeSetTermContains t (TypeTerm t')` is `t = t'`
  (`Golang/Defn/Interface.lean`), and Goose translates an embedded interface (`type Serializer
  interface { Encoder; Decoder }`) as `TypeElem [TypeTerm Encoder.ty]`. Go's type set of a term
  that is an interface is that interface's type set, so in the model no concrete type is in
  `Serializer`'s (or `Codec`'s) type set: a type assertion to such an interface panics where Go
  succeeds (the model is less defined, so proofs stay sound, but such an assertion cannot be
  verified).
- **Needed by.** Nothing yet (found 2026-10-23 while converting the driver's codec to
  `runtime.Codec`; conversions and method calls do not consult type sets).
- **Proposed fix.** In `typeSetTermContains`, a term whose underlying type is an interface
  contributes that interface's type set (`typeSetContains t t'`); a semantics change, through
  Perennial's `fix-semantics` workflow.
- **Landed.** Perennial `8ef540a62` (pin `6b58510f9`, 2026-10-27): goose writes an interface type as all
  its methods, embedded interfaces included, and emits every named type's method sets, so
  `go_type_set` decides such memberships (k8setcd3's `objTyOk` with `runtime.Unstructured`).

### Translation: `strconv.ParseUint`, `time.Ticker` and `Time.After`

- **Was missing.** Perennial translated nothing of `strconv` and none of `time.NewTicker`,
  `Ticker.Stop`, `Time.After`.
- **Needed by.** etcd's simple token provider (`server/auth/simple_token.go`):
  `isValidSimpleToken` parses a token's raft index with `strconv.ParseUint`; the TTL keeper's `run`
  ticks with a `time.Ticker` and compares with `Time.After`.
- **Landed.** Perennial `13a60f492` (2026-10-24, branch `time-ticker`: `NewTicker`, `Ticker.Stop`,
  `Ticker.Reset` trusted models, a ticker's channel a bag of arbitrary times; `Time.After`
  translated, returning some `bool`) and `c022dbe42` (2026-10-25, branch `strconv-parse`:
  `strconv.ParseUint` for bases 2 to 36, over the pure model `internal.strconv.parseUint`; three
  trusted models: `stringslite.Clone`, `internal/strconv.lower`, six constant tables' no-op
  initializers). The pin moved to `24bef275e` (the auth plan's S5c); `strconv`'s initializer is
  Perennial's (raft's local `strconv.opaqueInitsOk` axiom gone), and `isValidSimpleToken` is proved
  (`tokenSimple_isValid`). Left: `FormatUint`, `Itoa`, `ParseInt`, `FormatInt`, base 0.

### Specs: `sort.SearchStrings`, `sort.Strings`

- **Was missing.** A spec of `sort.SearchStrings(a, x)` (the least index whose string is not below
  `x`, on a sorted slice) and of `sort.Strings` (Perennial translated `sort.Search` and the pdqsort,
  not these two wrappers).
- **Needed by.** `auth.hasRootRole` (`sort.SearchStrings(u.Roles, rootRole)`), the root-role
  shortcut of every permission check and of `IsAdminPermitted`; `UserGrantRole` (`sort.Strings`).
- **Landed.** Perennial `beb785eaf` (2026-10-24, branch `sort-strings`): both translated and proved
  (`sort.wp_SearchStrings` over `ListSorted go.GoStringLe`, `sort.wp_Strings` a sorted
  permutation), `cmp.Less` at `string`. The pin moved to it (the auth plan's S4b), `hasRootRole`
  is translated and proved (`Proof/go_etcd_io/etcd/server/v3/auth/hasRootRole.lean`), and S3's
  axiom is gone. `UserGrantRole` still is not proved: it appends to the message `UnsafeGetUser`
  returned, which the read contract gives read-only (`notes/decisions.md`, "S4b of the auth plan").

### Specs: `context.WithTimeout`/`WithDeadline` of `Background()`

- **Missing.** A spec of `context.WithTimeout(parent, d)` (and `WithDeadline`,
  `WithDeadlineCause`) whose parent is `context.Background()` (or `TODO()`): Perennial's
  `context.WithTimeout.spec` takes `isContext parent`, which `Background()`'s value is not (its
  `Done()` is `nil`). `WithCancel` has the counterpart (`wp_WithCancel_Background`,
  `WithCancelGen.lean`), and the pieces of the deadline case are there too (`wp_background_Deadline`,
  `wp_propagateCancel_background`, `isContext_timerCtx_of`).
- **Needed by.** The pattern of client/v3's documentation, `ctx, cancel :=
  context.WithTimeout(context.Background(), timeout)` around each call: the examples' call sites
  since 2026-10-23 (`notes/client-timeouts-plan.md`, D-T2, D-T3) and the server's read loop
  (`sendReadIndex`, the request path's unit 4a).
- **Workaround here.** The trust-boundary axiom `context.WithTimeoutBackground.wp_proof`
  (`Spec/context/WithTimeoutBackground.lean`: an `isContext` of some descriptor and a callable
  `cancel`), in the `read`, `server` and every etcd example's collection; the examples use it
  through `client.wp_WithTimeout_bg` (`Proof/go_etcd_io/etcd/client/v3/TimeoutCtx.lean`).
- **Proposed change.** `wp_WithTimeout_Background` and `wp_WithDeadline_Background` (the
  `Background()` parent of `WithDeadlineCause`'s proof, as `wp_WithCancel_Background` is of
  `WithCancel`'s), with the descriptor they give (`Deadline := some d`, `PDone := True`, fresh
  Done names). Then the axiom here becomes a theorem (one axiom fewer in the baseline and in
  those collections: the plan's T3).
- **Status.** Landed: Perennial `c25bef57e` (branch `with-timeout-background` off `lean`
  `d761e15b2`, 2026-10-23: `wp_WithDeadlineCause_Background_of`, `wp_WithDeadline_Background_of`,
  `wp_WithTimeout_Background_of` in `Proof/context/WithDeadlineBackground.lean`, exposed in
  `Results.lean`; `propagateCancel`'s spec takes any child for a `Background()` parent,
  `wp_propagateCancel_background_any`); the pin moved to it and the axiom here is the theorem
  `context.WithTimeoutBackground.wp_proof` over `wp_WithTimeout_Background` (one axiom fewer in
  the baseline and in the `read`, `server` and every etcd example's collection).

### Std, PostLifting: generic lemmas the client, the cache and the examples each proved a copy of

- **Missing.** Facts about Perennial's and Lean's own definitions, proved in several places here
  (`notes/dedup-plan.md`, C1-C4 and D): a points-to at `q` as two halves and back, with agreement
  (twelve copies by value type: `ptsto_w64_halves`, `loc_halves`, `chan_split`, ...), half a
  points-to fractional (`half_pointsto_fractional_loc`/`_chan`); `N.@x` disjoint from `N.@y` and
  `N.@z` (the `*_mask` lemmas); setting the first entry of a `replicate` padding (five copies);
  one more function of a `foldl (fun o g => g o)` (`opFold_take_succ`, `stmOptsFold_take_succ`,
  `cfgApply_take_succ`); indexing and prefix facts Lean core lacks (`zip_get_snd`,
  `getElem?_snoc_cases`, `prefix_drop_cons`, the `crl_*_mid` three, `flatten_getElem?`, ...);
  `GoStringLt` on cons cells (`client/v3/PrefixRange.lean`).
- **Needed by.** `Proof/go_etcd_io/etcd/{client,cache}/v3/`, `examples/{linkvtxn,lintest}`.
- **Workaround here.** None now (the local copies stayed until the pin moved).
- **Proposed change.** Perennial branch `dedup-lemmas` (`f97c83add`, off the pin `537c426e0`;
  worktree `/shared/perennial-dd`): `typedPointsto_half_split`/`_half_combine`/`_half_fractional`
  (`Golang/Theory/PostLifting.lean`), `mask_ndot_ne2` (`Std/Namespaces.lean`), the list lemmas
  (`Std/List.lean`, sections `list_index`, `subslice_take`, `join_same_len_index`),
  `goStringLt_cons_iff`/`_nil_cons`/`_not_nil` (`Golang/Defn/String.lean`). Theorems only.
  Then, here: each copy deleted and its uses pointed at Perennial's (the `_take_succ` three stay
  one-liners over `foldl_apply_take_succ`: `opFold` and its kin are in specs' statements).
- **Status.** Landed 2026-10-22: Perennial `lean` `f97c83add`, the pin since; the local copies are
  deleted (etcd-grove branch `dedup-pin`), their uses pointed at Perennial's (the server's
  `mask_ndot_ne2` at `nroot` and the three `_take_succ` one-liners over Perennial's; raft's
  `ptsto_halves` too). Found 2026-10-22.

### Proof idioms: a synchronous SPSC channel, a thread-token join, a ghost update at a fork

Three of the watch client's local workarounds (D25, `notes/decisions.md`, "S1c's findings" and
"R4's findings"; `notes/status-history.md`, "watch-resume"), proposed as general idioms.

- **Missing.** (1) Perennial's SPSC idiom (`Idioms/Spsc.lean`) does not tie its pending channel
  states to the sides' tokens, so the holder of both tokens of an unbuffered channel cannot show
  that nothing is in flight (Go's synchronous handoff). (2) Its `WaitGroup` join idiom
  (`sync.join`) bounds the `Add`s since the last `Wait` (`num_added < 2^31 - 1`), not the
  goroutines running. (3) `wp_fork_tok`'s premise is a plain wand: no ghost update (no invariant
  opened) at the fork step, which is not atomic (`Fork` may stutter).
- **Needed by.** The watch client's reconnection: `respc` and every substream's `recvc` (`run`'s
  epoch switch and a substream's restart need `sent = recv`); `waitCancelSubstreams`' local wait
  group (one `Add(1)` per resuming substream, F4); its goroutines' inner `go` statement, which
  refills a lent slot at the fork.
- **Workaround here (until the pin moves).** `Proof/go_etcd_io/etcd/client/v3/SyncSpsc.lean` (a
  copy of `Spsc.lean` with pending flags); `InvWcJoin.lean`'s local join (`wcjAdder`, `wcjDone`,
  `wcjDoneB`, `wp_wcj_Add`/`Done`/`Wait`) and its copy of `wp_fork_tok`, `wp_fork_tok_upd`.
- **Proposed change.** Perennial branch `idioms` (off `lean` `a39a3d14c`), one commit each:
  `3c3e83e2c` `Idioms/SyncSpsc.lean` (`isSspsc`, `sspscProducer`/`sspscConsumer`, `sspsc_sync`,
  the `recvAu`/`sendAu`/`closeAu` lemmas and `wp_sspsc_receive`/`send`/`close`); `9e52da638`
  `wp_fork_tok_upd` in `GooseLang/Lifting.lean` (`wp_fork_tok` derived from it, statement
  unchanged); `537c426e0` `Proof/sync/WaitGroupTokJoin.lean`, `sync.tokJoin` (`ownAdder`,
  `ownDone`, `WaitGroup.wp_Add`/`wp_Done`/`wp_Wait`, the counter backed by thread tokens; a slot's
  token lendable, `lend_acc`/`unlend_acc`, under a client's lending law `lendLaw N L`). New
  definitions and theorems only; no existing statement changes. Reviewed (`trusted-delta.py`: no
  tier 0-2 trust change), recorded with `etc/land.sh mark-reviewed`.
- **Status.** Landed 2026-10-22: Perennial `lean` `537c426e0` (`3c3e83e2c`, `9e52da638`,
  `537c426e0`), the pin since; the local copies are deleted (etcd-grove branch `perennial-idioms`).

### Small gaps met by rafthttp's stream writer (stage 5b, 2026-10-23)

- **Missing.** (1) A typed points-to's halves: `typedPointsto l v (own 1) ⊣⊢ half ∗ half` is
  proved only in an example (`goose/testdata/examples/channel/etcd_session/Base.lean`,
  `pointsto_halves`), not the library. (2) `len(ch)` of a channel: `wp_auto` does not unfold
  `functions go.len [chan]` (`FuncUnfold`'s `len_chan`) to `Channel.Len`, so `chan.wp_Len` applies
  only after `wp_func_call; wp_call`. (3) `make([]T, n)` of a large concrete `n` (rafthttp's 1 MiB
  `msgAppV2BufSize`): `wp_slice_make2`'s postcondition names `List.replicate n zero`, which the kernel
  unfolds when a proof frames it (a deterministic timeout); a spec with the contents abstracted
  (`∃ zs, sl ↦* zs ∗ ⌜zs.length = n⌝`) avoids it.
- **Needed by.** `streamWriter.close` (the writer's fields split between its goroutine and its
  lock), `streamWriter.closeUnlocked` (`len(cw.msgc)`), `newMsgAppV2Encoder` (its buffer).
- **Workaround here.** `rafthttp/Writer.lean`'s `typedPointsto_halves` and
  `typedPointsto_combine_halves`; `wp_func_call; wp_call` before `wp_Len`;
  `newMsgAppV2Encoder.lean`'s `wp_make_bytes_abs`.
- **Proposed change.** (1) The halves lemma in `Golang/Theory/PostLifting.lean`; (2) `len_chan`'s
  unfolding in `wp_auto`'s simp set; (3) `wp_slice_make2_abs`/`make3_abs` beside the existing specs.
  Not yet proposed.
- (2026-10-23, rafthttp stage 5c) **A non-blocking send on a bag channel** (`select` with a
  `default`): the bag idiom (`Idioms/Bag.lean`) has the blocking send only. Workaround:
  `rafthttp/Reader.lean`'s `bag_nonblocking_send_au` (`bag_send_au` without the waiting case).
  Proposed change: the lemma beside `bag_send_au`. Not yet proposed.
- (2026-10-24, rafthttp stage 6d) **`wp_apply` aborts silently inside a `wp_join` case**: in
  `raftNode.start`'s loop, `wp_apply HSend $$ [...]` of the transport's `Send` (an interface method,
  its spec a hypothesis whose precondition now holds the loop's `E.S`) throws "unknown free
  variable" (visible with `+noauto`) and, without `+noauto`, an abort that leaves the case's goal
  admitted with no error: the module builds with a `sorry` only `#print axioms` and
  `etc/tcb-report.py` see. Workaround here: `wp_bind` the call and `iapply` the hypothesis
  (`raftNode__start.lean`). Proposed change: find the escaping free variable (probably the case's
  generalized context) and make `wp_apply` report it as an error. Not yet proposed.
- (2026-10-24, rafthttp stage 6f) **An axiomatized type's `sorry` instances shadow its `TypeRepr`**:
  for a type Goose cannot translate (`net/http`'s `Request`, `Response`) the generated proof has
  `X_typed_pointsto`/`X_into_val_typed` as `sorry -- axiomatized type`, and instance search takes
  `TypeRepr X.underlying X` from them (`IntoValTyped.type_repr`) although the translation's
  `X.TypeAssumptions.type_repr` gives it: a field reference (`StructFieldRef`, `req.Header`)
  then reaches the `sorry` (`etc/tcb-report.py`), with no load or store of the whole value.
  Workaround here: `Proof/net/http/Boundary.lean`'s `Request_typeRepr`,
  `Request_underlying_typeRepr` (and `Response`'s), high-priority instances from the type
  assumptions. Proposed change: Goose emits no `IntoValTyped` instance for an axiomatized type
  (or one of low priority), so its `TypeRepr` comes from the type assumptions. Not yet proposed.
### `wp_apply`'s frame list can admit a goal silently

- **Missing.** In `mvcc.restoreChunk.wp_proof` (2026-10-23), `wp_apply (wp_spsc_send …) $$
  [$Hsp $Hprod HP]` followed by a bullet for `HP`'s subgoal elaborated with no error, but the
  rest of the enclosing bullet never ran and the theorem got a `sorryAx` (found only through
  "declaration uses `sorry`", located by printing the `sorryAx` terms' source names). Framing a
  prepared hypothesis (`$HP'`) instead proved it.
- **A second instance** (2026-10-23, `schema.authBackend.GetUser.wp_proof`, the auth plan's S1):
  `wp_apply (hRU l rt R Held D) $$ [$Htxf $Hrtx $HD] as HR` at the *deferred* `tx.RUnlock()` call
  (the goal `WP ((RUnlock #() ;; oldf #()) ;; #u) {{Φ}}` after `wp_with_defer`'s body returned),
  `hRU` a Lean spec whose instance names `D`, a variable introduced after the defer by an earlier
  `wp_apply ... as ⟨%D, ...⟩`: no error at the line, the rest of the proof runs on nothing, and the
  theorem ends with "unsolved goals" showing the goal as it was before the call. `wp_apply_core`
  of the same term fails with "unknown free variable" (`_fvar...`), while `have h := hRU l rt R
  Held D` elaborates, and `wp_apply` of the same shape worked for `hRL` two calls earlier (before
  `D` existed). Workaround: `wp_bind` the call, then `iapply (hRU ...) $$ [Hpkg Htxf Hrtx HD]`,
  prove the precondition goal by `iframe`, `inext`, `iintro HR`.
- **A third instance** (2026-10-26, `heap.up.wp_proof`/`heap.down.wp_proof`): `wp_apply HSwap $$
  %ys %p %jv [HR] as HR`, `HSwap` an Iris hypothesis (the `heap.Interface`'s `Swap` triple), after a
  `cases b` on a Boolean an earlier `wp_apply HLess ... as %b HR` introduced: no error, the
  following tactics "never executed", and only "declaration uses `sorry`"; `wp_apply_core` of the
  same reports "unknown free variable". The same `wp_apply` of `HLess` before the `cases` worked.
- **Workaround here.** Prepare the hypothesis with `ihave` and frame it with `$`; check every new
  proof for the "declaration uses `sorry`" warning; at a deferred call, `wp_bind` and `iapply`.
- **Proposed change.** Not designed: a minimal reproduction first, then make the tactic report
  the error instead of admitting.

### Std, String: the successor string and the order's facts

- **Missing.** Lemmas about `GoStringLt`/`GoStringLe` beyond the four in
  `Perennial/Golang/Theory/String.lean`: that `k ++ "\x00"` is the immediate successor of `k`
  (`GoStringLt k b → k ++ "\x00" = b ∨ GoStringLt (k ++ "\x00") b`, so `k < b ↔ k ++ "\x00" ≤ b`
  and `k < key ++ "\x00" ↔ k ≤ key`), that a string is below its proper extensions, that `""` is
  the least string, and `GoStringLe`'s transitivity/antisymmetry/totality.
- **Needed by.** etcd's point interval `[k, k ++ "\x00")` (the watchable store's watchers on a
  key, the auth store's point permissions and `checkKeyPoint`): `mvcc/InvWatchGroup.lean`
  (`strLt_succ_le`, `succ_ne_empty`, `ivlCmp_point_iff`), `adt/Contains.lean` (the same three,
  restated so that `auth` does not import `mvcc`), `auth/PermTree.lean` (`goStringLt_succ_iff`),
  `adt/Model.lean` (`strLt_append`), the B-tree's and the cache's `goStringLe_*`.
- **Workaround here.** The copies above.
- **Proposed change.** The lemmas in `Perennial/Golang/Theory/String.lean`, with `GoStringLe`'s
  order instance; the copies here then go.

### Sequential specs of an `RWMutex` no one else can reach

- **Missing.** Perennial's `RWMutex` specs need the lock allocated (`isRWMutex`/`ownRWMutex`,
  `init_RWMutex`); code that locks a mutex of an object not yet shared (etcd's `restoreIntoIndex`
  on the index it is rebuilding, `restore` on `s.revMu` inside `NewStore`) has no spec.
- **Workaround here.** `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/PlainRWMutex.lean`:
  `plain.wp_RLock`/`wp_RUnlock`/`wp_Lock`/`wp_Unlock` on owned memory (values `rwZero`, `rwR1`,
  `rwW`), and `plain.wp_Mutex_Lock`/`wp_Mutex_Unlock` for the trusted spin lock, proved over
  Perennial's translation (no assumption).
- **Proposed change.** The same lemmas in Perennial's `Proof/sync` (for `Mutex` and `RWMutex`),
  stated for any number of nested readers if needed; not yet designed.

### `wp_apply` of a hypothesis fails as "unsolved goals" at the proof's `by`

- **Missing.** In `mvcc.store.restore.wp_proof` (2026-10-23), `wp_apply Hru $$ [$Htok]` (an
  Iris hypothesis, the read transaction's `RUnlock` triple from `keyReadLocked`) failed with
  "unsolved goals" reported at the theorem's `:= by`, the goal shown being the call, and the
  tactics after it never ran (a `fail` after it did not fire). The same call is applied this way
  in `storeTxnRead__End.lean`.
- **Workaround here.** `wp_bind` the call, then `iapply Hru $$ [Htok]`, `iexact Htok`, `inext`,
  `iintro`.
- **Proposed change.** Not designed: a minimal reproduction first; the tactic should report
  where and why it fails.

### An `RWMutex`'s reader slots are leaked by readers that hold them for life

- **Missing** (2026-10-26, D22 J0). `RWMutex.RLock` takes a reader token (`ownRLockToken`), of which
  a lock has `actualMaxReaders` (`2^30 - 1`, `ownRWMutex`'s `Hmax`). A goroutine or an object that
  takes a token for its whole life and is then abandoned (not joined) leaks it in the proof, while
  in Go only the readers inside `RLock`..`RUnlock` at one time count. etcd's server repeats this
  once per received snapshot: `applySnapshot`'s `RemoveAllPeers` stops each peer without joining
  its two `Process` goroutines (`peer.go:173-205`, `:314-333`), which hold a slot of the server's
  `lgMu` each (`startPeer.lean`'s `HR7`/`HR8`), and the new `UberApplier` takes a slot of the auth
  store's `enabledMu` that the old one never gives back. So any finite stock runs out after enough
  snapshots, and an unbounded number of snapshots cannot be verified.
- **Needed by.** D22's second-snapshot loop (`notes/snapshot-sj-plan.md`, "J0 decisions", gap 5;
  stages J8b and L3).
- **Workaround here.** None that is free. Until the change lands, J8a states `srvSnapApplied` with
  the slots it can return and the stock threaded from `NewServer` (`NewServer` drops the rest of
  `NewAuthStore`'s `actualMaxReaders` slots and `lgMu`'s today: J1b keeps them), and J8b closes the
  loop only if the stock suffices; the fallback is a named premise bounding the snapshots a member
  applies in a run, for the user's approval.
- **Proposed change.** `RLock` paid by a thread token (`GooseLang/Threads.lean`) when
  `threadBound ≤ actualMaxReaders`: every reader is a live thread, so the readers at one time are
  bounded by the threads, which is the real reason Go's counter does not overflow. A reader token
  then need not be held between critical sections. Not yet designed; general (any program whose
  goroutines read-lock a long-lived `RWMutex`), not shaped by this proof.
- **Landed** (2026-10-26, Perennial `3c64ae292`, branch `rlock-thread-token`): `Perennial/Proof/ThreadPool.lean`
  (`threadPool.isThreadPool N γ R`: at least `threadBound - 1` copies of `R`, a thread token swapped for
  a copy, `borrow`/`borrow_lc`/`giveBack`) and `Perennial/Proof/sync/RWMutexThreads.lean`
  (`init_RWMutex_threadPool`: every reader token in a pool, premise `threadBound GF ≤ 2^30`). Additive,
  no trusted-base change. Limitation: one thread token borrows one copy at a time, so a thread holding
  two thread-paid read locks at once pays the second with a stock token. The pin bump is still to do
  (with J8b).

### `strconv.NumError`'s `Error()` has no spec

- **Missing.** Perennial specifies `strconv.ParseUint`'s errors as fresh `*NumError`s
  (`strconv.numErrorOf`) but not `(*NumError).Error` (`"strconv." + Func + ": parsing " +
  Quote(Num) + ": " + Err.Error()`, through `strconv.Quote`), so a caller that must show the error
  prints (`http.errStrOk`, `zap.Error`'s callers) cannot. Found 2026-10-26 when trying
  `types.IDFromString` (`strconv.ParseUint(s, 16, 64)`): its proof would need a new axiom for
  `NumError.Error` in place of the one it discharges, so it stays an axiom.
- **Workaround here.** None: `types.IDFromString.wp_proof` stays a trust-boundary axiom. Its success
  case is provable over `ParseUint.spec` (a pure lemma that `parseUint (types.idStr x) 16 64 = .ok
  x`, by induction on `types.hexNatF`'s fuel with `parseDigits_append_ok`).
- **Proposed change.** A spec of `(*NumError).Error` (returns some string; or the string, with a
  spec of `Quote`) in Perennial's `Proof/strconv`.

### `errors.Is`/`errors.As` at non-pointer targets and for leaves

- **Missing.** Perennial's `errors.Is.spec` takes a `nil` or pointer target, and its
  `errors.As.spec` allows any result. Four axioms here are specializations it does not cover
  (2026-10-26 survey): `errors.IsDeadlineExceeded` and `errors.IsCtxErr` (the target
  `context.DeadlineExceeded`, an empty struct), `errors.IsStatusErr` (an `EtcdError` value
  target), `errors.AsLeaf` (`As` of an `errors.New` error against a type whose set excludes
  `*errorString` returns `false`).
- **Workaround here.** The four stay trust-boundary axioms (`Proof/errors/`).
- **Proposed change.** `errors.Is.spec` for a comparable non-pointer target (Go's `Is` compares
  with `==` first, which does not panic for a comparable target type), and an `errors.As` spec that
  says `false` for a leaf error not in the target's type set; then the four are proved here.

### `go.NotInterface go.uint64`

- **Missing.** Perennial's `PostLifting.lean` has `go.NotInterface` instances for composite types
  (arrays, pointers, slices, maps, untyped) but none for the basic integer types, so
  `MethodResolve` on a named type over `uint64` (`types.ID`'s `String`) does not step.
- **Workaround here.** Local instances (`InvStart.lean`, `apply/BackendLemmas2.lean`,
  `EtcdServer__sendMergedSnap.lean`, `SnapTakeProof.lean` (D22 J4b)), each `⟨by unfold go.uint64;
  trivial⟩`.
- **Proposed change.** Instances for the basic types (`uint64`, `int64`, `string`, `bool`, ...) in
  `PostLifting.lean`, beside the composite ones.

### `wp_apply` of a hypothesis triple with no binders in its post drops the continuation

- **Found** (2026-10-29, U8 v2 step 4, `newLogWithSize` over the boot bundle,
  `notes/u8v2/step4-boot-newLogWithSize.patch`): `wp_apply H $$ [$HR]`, with `H` a hypothesis
  triple whose postcondition binds nothing (`{{ P }} e {{ RET v; Q }}`), silently loses the
  continuation: the goal after it is not the rest of the program.
- **Workaround here.** `wp_apply_raw H $$ [$HR]; inext; iintro HR`.
- **Proposed change.** `wp_apply` handles a post with no binders like one with binders
  (investigate where the continuation is dropped; a regression test with such a hypothesis).

### `word` on fully concrete goals fails the kernel's check

- **Found** (2026-10-29, same proof): `word` closes a goal with no variables (concrete `w64`
  arithmetic) at elaboration, but the proof term fails the kernel's check.
- **Workaround here.** `rfl` or `simp` on those goals.
- **Proposed change.** Find which `word` step produces the ill-typed term on closed goals (or
  have `word` try `decide`/`rfl` first on them); add a test.

### gokv's `trusted_proph` has a trusted model but no spec, and no translation in Perennial

- **Found** (2026-10-30, kvreconf-final, the atomic `Cluster.Read`): Perennial has the trusted
  model of `github.com/mit-pdos/gokv/trusted_proph`
  (`Perennial/TrustedCode/github_com/mit_pdos/gokv/trusted_proph.lean`: `NewProph`,
  `ResolveBytes := ResolveProph p (Convert []byte→string b)`), but no Goose translation of the
  package and no spec of `ResolveBytes`.
- **Workaround here.** The kvreconf project translates the package (`etc/goose.py`,
  `Code/github_com/mit_pdos/gokv/trusted_proph.toml`, both functions trusted;
  `TrustedCode/github_com/mit_pdos/gokv/trusted_proph.lean` re-exports Perennial's model), and the
  spec is proved here from `wp_bytes_to_string` and `wp_resolve_proph`
  (`Spec/github_com/mit_pdos/gokv/trusted_proph/ResolveBytes.lean`,
  `Proof/.../trusted_proph/ResolveBytes.lean`):
  `{proph p pvs ∗ sl ↦*{dq} s} ResolveBytes(p, sl) {∃ pvs', ⌜pvs = #s :: pvs'⌝ ∗ proph p pvs' ∗ sl ↦*{dq} s}`.
- **Proposed change.** Translate `trusted_proph` in Perennial (as `primitive`, a `.toml` with the
  two trusted functions), and add this spec and its proof (`Perennial/Spec/.../trusted_proph/`,
  `Perennial/Proof/.../trusted_proph/`, with a `Link`), as for `primitive`'s
  `ProphId.ResolveU64`. Then this repository drops its translation and its copy of the spec.

## `WithCancel`'s `Value` delegates to its parent (2026-10-28, M2)

Perennial's `context.WithCancel` spec gives `isContext` of the child, whose `Value` is specified only
for `cancelCtxKey`. etcd's server reads `ctx.Value(TraceKey{})` (`traceutil.EnsureTrace`) on the
auto-compactor's context, `WithCancel(Background())`; proving that it carries no trace needs: for a
key other than `cancelCtxKey`, the child's `Value(k)` is the parent's (Go's `cancelCtx.Value`,
`value(c.Context, key)`). General (every derived context: `WithCancel`, `WithTimeout`,
`WithDeadline`). Meanwhile: a local lemma over Perennial's context, justified in
`notes/m2-plan.md` (the compactor's freeze repair).

## `aupd_post_mono`: an atomic update is antitone in its atomic postcondition (2026-10-29)

`atomic_update Eo Ei α β Φ ⊢ atomic_update Eo Ei α β' Φ` when `β' x y ⊢ β x y`: the committer
supplies more. It is a fact of Iris's atomic updates (the Rocq `atomic_update_mono` family), proved
here by `greatest_fixpoint_coiter` and `aupd_aacc` (`Proof/.../etcdserver/InvRequest.lean`, step 5
of the auth-mode merge). Proposed change: the lemma in Perennial's/Iris's atomic-update library,
next to `aupd_aacc`.

## A bag channel's non-blocking send (2026-10-30, kvreconf-snapshot-thread)

Perennial's bag idiom (`Chan/Idioms/Bag.lean`) has the blocking send's atomic update
(`bag_send_au`) but not the non-blocking one a `select` with a `default` needs. kvreconf's `request`
sends on a capacity-1 bag channel without waiting; the lemma `bag_nb_send_au : £ 1 -∗ isChanBag γ ch
P -∗ P v -∗ ▷ Φ -∗ nonblockingSendAuInner γ v Φ` is proved locally
(`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/BagSend.lean`, generic). Proposed change:
the lemma in `Bag.lean`, next to `bag_send_au`.


## A bag channel's non-blocking receive (2026-10-31, S1)

The receive counterpart of the previous entry: `applyAll`'s `select` on `msgSnapC` (with a
`default`) needs a non-blocking receive's atomic update from a bag. Proved locally as
`chanBag_nbRecv : isChanBag γ ch P ⊢ (∀ v, P v -∗ Φ v true) -∗ nonblockingRecvAuInner γ Loc Φ`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapSendBranch.lean`, generic). Proposed change: the
lemma in `Bag.lean`, next to `bag_send_au` (with `bag_nb_send_au`).

## A typed points-to's fraction validity (2026-10-31, lease-keys Part B)

`typedPointsto l v dq` has value agreement (`typedPointsto_combine_sep_gives`, `⌜v1 = v2⌝`) but
not the fractions' validity that the heap points-to's `CombineSepGives` gives
(`⌜✓ (dq1 • dq2) ∧ v1 = v2⌝`): so a points-to owned whole and a read-only one of the same field
cannot be shown to exclude each other. The lessor's `Grant` needs it: a fresh `*Lease` (its `ID`
owned whole) is not one the item sets' map already has (each with `ID ↦□`). Worked around locally
for a `w64` field (`w64_own_discard_false`, `Proof/.../lease/InvLessor.lean`: through the first
byte's heap points-to). Proposed change: `TypedPointsto` gains (or derives, for the byte and heap
instances) `typedPointstoDef l v1 dq1 ∗ typedPointstoDef l v2 dq2 ⊢ ⌜✓ (dq1 • dq2)⌝` for a
non-empty representation, and `typedPointsto`'s `CombineSepGives` returns it with the agreement.

## Strictly sorted lists with the same members are equal (2026-10-31, lease-revoke)

`go.GoStringLt` (Perennial's order on Go strings, which `sort.StringSlice.Sort`'s model sorts by)
has no law that two lists strictly increasing for it, with the same members, are equal. The
lessor's `Revoke` needs it: the sorted item set it deletes is the lease's keys in key order
(`mvcc.leaseDelKeys_eq`). Worked around locally (`eq_of_lt_sorted_mem`,
`Proof/.../storage/mvcc/LeaseItems.lean`, from irreflexivity and transitivity). Proposed change: a
general `List.eq_of_pairwise_lt_mem` for a strict order (in Perennial's list lemmas, or the
`GoStringLt` instance of one), so that the local copy goes.

## `sort.Sort` for a `Less` that answers anything (2026-10-31, lease-read)

Perennial proves `sort.Sort` (`sort.wp_Sort`, over `sort.isSorter x own R`) only for a `Less` that
agrees with a strict weak order `R`. The lessor's `Leases()` sorts with `leasesByExpiry`, whose
`Less` compares `Remaining()`, read off the clock (and moved by `Renew`): it agrees with no fixed
order, and the caller needs only the permutation. Go's `pdqsort` (`zsortinterface.go`) bounds every
index it passes to `Less` and `Swap` by the slice's bounds, never by `Less`'s answers, so the
permutation holds for any `Less`. Worked around locally by a trust-boundary axiom,
`sort.Sort.wp_anyLess` (`Spec/sort/SortAnyLess.lean`: `sorterAnySpec`, a `Less` triple returning
some boolean; the result a permutation), the user's choice (the lease-read plan's S2). Proposed
change: a spec of `sort.Sort` (and of `pdqsort` and its helpers) for a sorter whose `Less` returns
any boolean, the result a permutation of the whole slice; `wp_Sort` then adds sortedness for a
strict weak order. Not `wp_Sort`'s induction without the order: with any `Less`,
`partialInsertionSort`'s left shift runs down to index 1, not to the segment's start
(`zsortinterface.go:218`, `j >= 1`), so it moves elements below the segment and the per-segment
"outside unchanged" invariant fails; the proof needs a whole-slice invariant (every index in
`[0, n)`, the list a permutation). The local axiom goes when it lands.

## A thread pool's loans are fewer than the live threads (2026-11-01, bounds B2's leasing pilot)

`threadPool` (`Perennial/Proof/ThreadPool.lean`) lends a copy of its resource for a thread token
and holds the token, but says nothing a client can use about the loans outstanding. A goroutine
started on a wait group whose counter is bounded by thread tokens (`Add(1)` deposits the caller's
token) has no token of its own, so it cannot borrow; if instead the wait group's running slots hold
the pool's loan receipts (`ownThreadLoan`), the counter's bound needs "`k` loans are fewer than
`threadBound GF`". Worked around locally (`Proof/go_etcd_io/etcd/client/v3/leasing/PoolLoans.lean`):
`threadPool.loans_lt` (`isThreadPool N γ R ∗ ownToks γ k ⊢ |={E}=> ⌜k < threadBound GF⌝ ∗ ownToks γ k`,
`↑N ⊆ E`: the invariant's `ownTokAuth γ b` bounds `k ≤ b`, its `threadToks b` gives
`b < threadBound GF`) and `threadPool.init_named` (`init` under a name allocated beforehand,
`ownTokAuth γ 0`, so that the name can be among the ghost names the pooled resource is defined
over). Proposed change: both in `ThreadPool.lean` as they are.

## `errors.Is` answers the same twice (2026-11-01, the lease rows at the gRPC level)

`errors.Is.spec` (`Perennial/Proof/errors/Base.lean`, `errorIsTree S M target`) says only `err =
target → true` and `true → some error of the tree is the target or an `Is` method said so`
(`M`); the tree is an over-approximation (`S`, closed under `Unwrap`), and its nodes' `Is` and
`Unwrap` specs return some answer. So two calls with the same error and target may answer
differently, though Go's `errors.Is` is a function of the tree (the errors reachable by `Unwrap`
from `err`, each compared with `target` and asked `Is(target)`), and Go's error methods are
deterministic. etcd's `v3rpc/lease.go` calls `errors.Is(err, lease.ErrLeaseNotFound)` twice
(`LeaseTimeToLive`, `LeaseLeases`): a `true` then a `false` would reach `ls.hdr.fill(resp.Header)`
with `resp == nil`, so the handlers cannot be proved; `watch.go`'s `recvLoop` calls
`errors.Is(err, context.Canceled)` twice too. The errors here are `applyErrIs` errors (any tree),
so a local leaf fact would have to be threaded from the auth store up through about ten frozen
specs (asked, 2026-11-01: the user chose this Perennial change instead). **Workaround here**: none (a `sorry`
in each handler); the lease gRPC stage (`notes/lease-grpc-plan.md`) waits. **The change**
(landed: Perennial `c4a24e323`, 2026-11-01; the pin): the
tree's method specs as relations (`errorWalkTree S I U target`), `errors.Is`'s answer one of Go's
walk over them (`IsWalk`), a function of the tree for exact relations (`isWalk_det`);
`errorIsTree S M` the over-approximating instance (unchanged in meaning), `errors.wp_Is_tree` the old
postcondition, `errorIsTree_of_walk`, `errorWalkTree_leaf`. It generalizes the first proposal: an error tree with
exact node specs (`Unwrap() error` returns a fixed `u ii`, `Unwrap() []error` a fixed list, `Is`
returns a fixed `f ii target`), and a spec of `errors.Is` over it whose answer is
`decide (∃ e ∈ reach u err, e = target ∨ f e target)` (partial correctness: a cyclic chain does not
return); `errorIsTree`'s current form follows from it. Every Go error type whose methods are
deterministic (all of the standard library's and etcd's) has such a tree; `applyErrIs` would then
carry it. Done here: `applyErrIs` with an exact tree (its three leaf constructors), etcd-grove's
`errors.Is.spec` proved by `errors.wp_Is_tree`, the two handlers' `sorry`s closed. **Follow-up**
(small, open): `errorIsTree_of_walk` (and the other `Base.lean` lemmas) take the section's
`errors.Assumptions` though their proofs do not use it; an `omit package_sem in` would drop it.

## `isChanBag` has no law for changing its payload (2026-11-02, the lease-grant review's M1)

`Perennial/Golang/Theory/Chan/Idioms/Bag.lean`'s `isChanBag γ ch P` (irreducible, over an `inv` of
`chanBagInv γ P`) has no law replacing `P` by an equivalent payload, though `inv_iff` makes it
immediate. **Workaround here**: `chanBagInv_mono` and `isChanBag_iff` (`P v ⊢ Q v` and `Q v ⊢ P v`
for every `v`), in `Proof/go_etcd_io/etcd/server/v3/etcdserver/LessorOk.lean`, used to restate the
lessor's `expiredC` as a bag of `False`. **The change** (proposed, not started): the two lemmas in
`Bag.lean` (and the same for the other channel idioms' payloads).


## A cell owned whole is no cell's read-only points-to (2026-11-02, restart plan R2c stage 2)

`typedPointsto l v (own 1) ∗ typedPointsto l w discard ⊢ False`: Perennial has the fractions'
validity at the non-atomic heap (`naHeapPointsto`'s `CombineSepGives`, `naHeapPointstoSt_valid_2`) but
no typed-level form. `idutil`'s `NewGenerator` needs it, for a `uint64` field, to show that a new
generator is no registered key's. Its prefix field is owned whole until it is persisted, and every
registered generator's is persistently readable.

Local: `w64_pointsto_excl` (`Proof/go_etcd_io/etcd/pkg/v3/idutil/Defs.lean`), for `w64`, through the
first byte's heap points-to. The general change: `typedPointsto_valid_2` for any `TypedPointsto` type
whose points-to owns at least one byte, giving `✓ (dq1 • dq2)`.

## Loading a struct field through a fractional points-to (2026-11-02, porcupine PR #46)

`wp_load`/`wp_auto` do not load a field of a struct held by a fractional points-to
(`p ↦{dq} v`, `dq ≠ own 1`), although the generated `AccessStrict` load instances take any `dq`;
applying the instance by hand works. Met proving the oracles of porcupine PR #46 (`RealTime` reads
`a.Call`, `b.Return` through pointers the caller holds fractionally). Local: split the struct with
`iStructNamed` and put it back with `typedPointsto_combine` (`op_split`/`op_join` in
`PorcupineDag/Proof/github_com/anishathalye/porcupine/Oracles.lean`). The general change: the
field-load automation finding the instance at any fraction.

## A slice literal of map literals (2026-11-06, the mvcc tester)

`wp_slice_literal` (`Perennial/Golang/Theory/Slice.lean`) fixes the elements `l` before the array
literal's WP runs, so a literal whose elements are themselves allocated by that WP
(`[]map[string]kvRec{{}, {}}`, `examples/mvccrand`'s `newHistory`: each element a `make1`) cannot
name them: the metavariable `?l` is created outside the scope of the maps' locations, and `rfl`
fails. **Worked around locally** (2026-11-06): `wp_slice_literal_ex` in
`Proof/github_com/mit_pdos/etcd_grove/examples/mvccrand/newHistory.lean`, a copy of
`wp_slice_literal_nonnull`'s proof whose post takes the elements existentially
(`∃ l, ⌜v = #(array.mk n l)⌝ ∗ …`), under `set_option goose.wp.unfoldSliceLiterals true` and
Perennial's section variables (`[GoSemanticsFunctions] [go.PreSemantics]`); `newHistory` is proved
over it. **The general change**: Perennial's `wp_slice_literal`(`_nonnull`) with `∃ l` in the array
literal's post (the current statements are its instances at a fixed `l`), then delete the local copy.

## `isSpsc`'s invariant at `nroot`; no `chan.wp_len` (2026-11-06, the mvcc tester)

Met proving `examples/mvccrand`'s ticks channel (`WriterRun.lean`, `notes/mvcc-migration/mvccrand.md`):
Perennial's single-producer channel `isSpsc` keeps its invariant at `nroot`, so a caller that holds
another invariant open (the tester's, under its own namespace) cannot send on it; and there is no
`chan.wp_len` wrapper beside `chan.wp_cap`. Local: the tester sends outside its invariant. The
general changes: `isSpsc` parameterized by its namespace; a `chan.wp_len` lemma.
## `ownMap` is not `DFractional` (2026-11-04, bbolt batch 34)

Perennial has `ownMap_fractional` (the `Fractional` form at `DFrac.own q`) but no `DFractional`
instance for `ownMap mref dq m`, so a predicate mixing map points-tos with other `DFractional`
parts (bbolt's writer heap, `wtxHeap`) cannot get `Fractional` by instance search. Local: the
private `ownMap_dfractional'` in `Proof/go_etcd_io/bbolt/Inv/WtxHeap.lean` (U5c's proof: through
`ownMap_unseal` and `heapPointsto_dfractional`, persistence by `ownMap_discarded_persist` /
`ownMap_persist`), which is general. The general change: that instance next to `ownMap_fractional`.

## `sync.Once`'s spec is fixed to `HasLC.hasLC` (2026-11-04, bbolt batch 38)

Perennial's `sync.Once` spec (`isOnce`, `Once.Do`) is stated at `HasLC.hasLC` only, so a proof
generic in `hlc` (bbolt's, every internal spec) cannot use it. bbolt's `Open` steps `Do` on an owned
zero `Once`; local: U11d's `Proof/go_etcd_io/bbolt/Open/OnceOwn.lean` (`Once.wp_Do_own`, any
`hlc`). The general change: an `hlc`-generic `Once` spec in Perennial.

## `sync.Pool`'s `New` may assume a caller-lent resource (2026-11-04, bbolt U11h)

- **Limitation.** `isPool p f P` required a persistent `{{ True }} New() {{ P x }}` at the pool's
  creation. A `New` closure reading a variable its creator writes again later has no such spec:
  bbolt's `Open` sets `pagePool.New = func() any { return make([]byte, db.pageSize) }` over its named
  result `db`, which every `return` writes. The Go code is safe (`New` runs only in `Get`, reached
  only while the database is open); the spec is too strict.
- **Needed by.** bbolt's `Open` (`Proof/go_etcd_io/bbolt/Open.lean`, the page pool's `New`).
- **Workaround here.** None (merged from the local branch `bbolt-pool-new-later`, 2026-11-05: no
  `sorry` in `Open`): a `Get` caller lends `New` a
  lease `poolR γbq N P` (U11i), and `New` borrows a fraction of `db`'s cell from `Open`'s protocol
  `Open/PoolNew.dpProt` for its whole read, depositing `P` (saved under a name, the borrow in a
  ghost map) as collateral; `Open`'s last write collects every fraction around one of its own
  steps (`wp_step_fupd`), refuting a borrow still out by its lease and the whole token (U11j).
- **Proposed change.** Perennial branch `pool-new-later` (`/home/ubuntu/perennial`, commit
  `3b91c3ee1`, off the pin `b3e996d84`): `isPool p f R P` with
  `newSpec f R P := ⌜f = nil⌝ ∨ {{ R }} f() {{ x, P x ∗ R }}`; `Get` takes and returns `R`; `Put`
  and `init_Pool` take the parameter; `R := True` is the old spec (`newSpec_of_true`);
  `init_Pool` consumes the pool's points-to, so the spec can be chosen after `Pool{New: f}` is
  stored. No model or trusted change. With `sync.isPool_respec` (`c6d352196`: an `isPool` with
  another `New` spec `R'` for which `newSpec f R' P` holds), so that a pool can serve a family of
  lenders (`∀ Q, isPool p f (R Q) P`; `Open/PoolNew.init_Pool_all`).
- **Status.** Landed (3dd730372, Perennial `lean`'s merge of `pool-new-later`). bbolt-v2 pins
  `c6d352196` (its pin `b3e996d84` plus the two pool commits, in `lean`'s history); the catch-up
  to `lean` (3dd730372 and later) comes with the merge of bbolt-v2 into this repository's `lean`.

## `struct_wp_alloc_pos` in `Golang/Theory` (bbolt maintainer 13, 2026-11-04)

- **Need.** A struct allocated by Go is at a positive address (`GoPrealloc` gives it:
  `wp_GoPrealloc_pos`), which a byte view (`BytesView`) needs; `struct_wp_alloc` keeps only
  `l ≠ null`. bbolt's `Tx.init` allocates the transaction's meta copy, which `writeMeta` views as
  bytes.
- **Where it is now.** `struct_wp_alloc_pos` exists only in Perennial's test example
  (`Proof/github_com/mit_pdos/perennial/goose/testdata/examples/unsafememory/Meta.lean`).
- **Workaround.** A copy in `Proof/go_etcd_io/bbolt/Txn/MetaAlloc.lean` (`bbolt.struct_wp_alloc_pos`,
  `Meta.wp_alloc_pos` for `common.Meta`).
- **Proposed change.** Move `struct_wp_alloc_pos` to `Perennial/Golang/Theory/Auto.lean` (beside
  `struct_alloc_fields'`); ideally have the generated proofs give `T.wp_alloc_pos` per struct. Not
  started.
### Prophecies in Lean only: `withProph` and `goose_adequacy_withProph` (2026-11-02)

- **Missing.** A proof that needs a prophecy variable the Go code does not have (the etcd3 store's
  `Get`, whose read update fires at several states; `notes/k8s-etcd3-plan.md`, phase 7) had to
  instrument the Go code (the etcd fork's `goose-lean-getproph`, `Apply`'s `ResolveU64`s), with
  an informal argument that `primitive.NewProph`/`ResolveU64` are no-ops.
- **Done (Perennial branch `proph-erasure`, pushed, not landed).** `withProph e`
  (`Perennial/GooseLang/ProphInstrument.lean`) runs the program `e` unchanged under a prophecy of
  its result; `goose_adequacy_withProph` gives `goose_adequacy`'s conclusions about the real
  executions of `e` from a WP of `withProph e`, same bounds, proved (standard axioms only), no
  change to the semantics (`etc/trusted-delta.py`: the new modules are tier 2). `wp_withProph`
  (`Golang/Theory/WithProph.lean`) hands the proof of `e` the prophesied list. End-to-end example
  `goose/testdata/examples/prophkv` (`GetAny` reads twice and returns one answer chosen afterwards;
  its logically atomic spec takes a prediction; `prog_safe` is about the program without the
  prophecy).
- **Per-call instrumentation, done (same branch, 2026-11-03).** `goose_adequacy_funcProph`
  (`Perennial/GooseLang/FuncInstrument.lean`, proved, standard axioms only): a WP in a Go model
  patched so that one function `f` (two arguments, no type arguments) resolves to its body under a
  prophecy of its result (`prophFnV impl`) gives `goose_adequacy`'s conclusions about the real
  executions in the real model. Proof: a simulation in the bounded language whose instrumented
  threads are the real ones with the wrapper's frames inserted around running calls of `f`. It
  needs `f`'s resolution `GoInstruction (FuncResolve f [])` to be only applied to its arguments
  (`ok`), so that the two models' different closures never reach a Go instruction: `ok` is checked
  on the program and is an invariant given the same of the model's instruction results
  (`GoodModel`), the extensions (`GoodExts`), prophecy-id values (`IntoValOk.proph`) and the
  initial heap; these are premises of the closed theorem (true of any model of Go, which has no
  instruction producing a reference to `f` and no prophecies, but not derivable from
  `go.Semantics`). `patchSem` (`Perennial/Golang/Theory/FuncProph.lean`) proves the patched model
  satisfies `go.Semantics`: a `transfer` tactic carries the ~480 fields over definitionally; only
  `go_func_resolve_step` and a few `FuncUnfold` facts of named functions (`reservedFuncs`) need
  proofs. In `prophkv`, `wp_GetAny` is now a plain logically atomic spec (no prediction), and
  `prog_safe` takes `ModelOk` and `heapOk` premises.
- **Dropped (2026-11-03, the user's choice).** This approach (prophecies added in Lean, with an
  instrumentation theorem) is no longer followed: proofs that need a prophecy get it from a
  prophecy patch of the Go code (`etc/proph-patches/`, `notes/decisions.md`, "Prophecies as patches
  of the Go code"). The Perennial branch `proph-erasure` is kept, not landed, for reference only;
  do not build on it. (A WP-free erasure theorem would need either the premises below or a new
  `go.Semantics` fact, Go instructions commute with erasure; not pursued.)
- **Remaining limitations.** `f` must take exactly two arguments (the wrapper's shape and the
  call-position count are fixed); one instrumented function per model (patching composes, not
  done); `ModelOk` assumes the program's own function bodies are `ok` rather than checking them
  (they are checked only through `prog`'s own code); generated instances that take the package's
  `Assumptions` (proofgen's struct instances) must be re-declared from the instrumented model's
  `AssumptionsP` (`Main.lean`'s shim).

## A cancelable thread pool (2026-11-04, the restart plan's R2b-3d gap 4)

- **Need.** The server's shutdown closes the backend, which takes every reader's open share back.
  The server lends the shares through `threadPool.isThreadPool`, a plain invariant, which never
  gives them back.
- **Change.** Perennial branch `threadpool-cancel` (`c0a2fdd46`, off `origin/lean` `350766064`,
  worktree `/shared/perennial-tpool-cancel`), in `Perennial/Proof/ThreadPool.lean`:
  `isThreadPoolC N γ γc R` with
  `poolOpen γc q`, `initC`, `borrowC`, `giveBackC`, `cancel` and `reclaim`. It is a proved library
  addition (tier 3) that adds nothing to the trusted base. `land.sh prepare` passed and the trusted
  review recorded OK. **Landed** (the user's push, 2026-11-04: Perennial `lean` `e3ceb1520`); the pin moved to it the same day (branch `r2b3`).

## `fmt.Errorf`'s model can be unfolded to learn facts false of Go (2026-11-06, k8s etcd3 7c-2, branch `k8s-etcd3-7c`)

- **The gap.** Perennial's model of `fmt.Errorf` (`Perennial/TrustedCode/fmt.lean:19-28`) is
  `errors.New(format)`: it ignores the arguments and does not model `%w`. The spec
  (`fmt.wp_Errorf`, `Spec/fmt/Errorf.lean`) deliberately promises only a non-nil error whose
  `Error()` returns some string, with no type. But nothing stops a client proof from unfolding the
  model (`wp_start` on a call of `Errorf`) and learning facts that are false of Go, where a `%w`
  format returns a `*fmt.wrapError`:
  - its type (`*errors.errorString`);
  - that it is a leaf (no `Unwrap`), and so `statusErrOk`;
  - that `errors.Is(err, target)` is false for the wrapped error;
  - that its message is the format string.
- **Where it bit here.** `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Errorf.lean`'s
  `wp_Errorf_errorfIs` (since 2026-10-12, unit 3b; `notes/decisions.md`, "`fmt.Errorf`'s `%w`
  errors: the model's body, not the axiom"). It is used for `rangeKeys`' and `executeTxn`'s `%w`
  errors (`kvstore_txn.go:121`; `txn.go:162, 174, 182`), which then reach `applyErrIs` (a leaf
  with `statusErrOk`, since k8s etcd3 7c-2 part 1) through `applyErrIs_errorf`. False of Go for a
  cancelled context: reported to etcd-grove-82, 2026-11-06; the local fix is k8s etcd3 7c-2's.
- **Proposed (general; record only, nothing changed in Perennial).** When the format contains `%w`,
  `Errorf`'s model returns an opaque error, so that no proof can reason about it beyond the spec;
  or it models `%w`: a `*fmt.wrapError` with `Unwrap`, its message the formatted string, with a
  spec that states the wrapped errors. Without `%w` the present model (`errors.New`) is faithful
  up to the message's formatting.
- **Status.** Recorded only.

## `iframe` over a large `List.replicate` materializes the list (2026-11-06, revoke-open)

- **What happened.** A bare `iframe` in revoke-open's `NewServer.lean` (the goal two `[∗list] _ ∈
  List.replicate srvRevokePoolN ()` conjuncts, `2 ^ 28 - 1` copies each) tried every hypothesis of
  the context against them; on a big-list hypothesis whose element did not match, the unifier
  unfolded `[∗list]` and built `List.replicate (2 ^ 28 - 1) ()` element by element: 80 GB of RSS
  after 36 minutes before it was killed (a normal compile of the file peaks at 5.4–5.8 GB).
- **Local workaround.** Frame explicitly (`isplitl [H]; · iexact H; · iexact H'`); never a bare
  `iframe`, or any search over the whole context, where a `[∗list]` over a large replicate is in
  scope.
- **Proposed (general; record only, nothing changed in Perennial).** `iframe`'s candidate matching
  should not unfold big separating lists: match a `[∗list]` hypothesis against a `[∗list]` goal only
  syntactically (same list term, same element up to reducible unfolding), or with the unifier at
  reducible transparency, so that a mismatch fails fast instead of reducing `List.replicate n` for a
  literal `n`.
- **Status.** Recorded only.

## `wp_apply` of a hypothesis spec can give up silently, leaving a `sorry` (2026-11-06, revoke-open)

- **What happened.** In revoke-open's `EtcdServer__revokeExpiredLeases.lean`, `wp_apply hWR stl
  E.RD (GoInterface.ok ctx)` (a callee spec taken as a hypothesis, `authStore.WithRoot`'s) failed
  without an error: the declaration only got the warning "declaration uses sorry". A proof author
  who reads errors only would take it for done; `etc/tcb-report.py` and the build's sorry warnings
  catch it.
- **Local workaround.** `wp_bind (App (Val _) (Val #(GoInterface.ok ctx)))`, then `iapply hWR …
  $$ [IRD] …`.
- **Proposed (general; record only, nothing changed in Perennial).** When `wp_apply` cannot use the
  term it is given, it should fail with an error naming the mismatch, never close the goal with an
  admitted proof.
- **Status.** Recorded only; not reduced to a minimal example.

## `strings.Cut` has no model (2026-11-08, k8s 7e-3b)

- **What happened.** Perennial's `strings` translates `Cut` names-only (no body, no spec). The k8s
  etcd3 driver's `splitKey` called it.
- **Local workaround.** The driver (our test code) splits the key with a byte loop instead; no spec
  or axiom added.
- **Proposed (general; record only).** A model of `strings.Cut` (a translated body, or a spec:
  `s[:i]`, `s[i+len(sep):]`, `true` at the first occurrence `i`; `s`, `""`, `false` if none) is a
  candidate general addition to Perennial's `strings`.
- **Status.** Recorded only.

## `func.forRange` (range over a function) has no WP rule (2026-11-10, k8s 7e-2, branch `k8s-7e`)

- **Missing.** Perennial defines `func.forRange n` (`Perennial/Golang/Defn/Loop.lean`, Go 1.23's
  `for k, v := range f`) but proves no WP rule for it; `doFor` has `wp_for`.
- **Needed by.** `store.GetList`'s `for chunk, chunkErr := range chunks`
  (`k8s.io/apiserver/pkg/storage/etcd3/store.go:829`).
- **Workaround here.** A local, proved lemma `wp_forRange2` (`n = 2`) in
  `Proof/k8s_io/apiserver/pkg/storage/etcd3/ForRange.lean`: the caller proves the iterator's WP for
  an abstract yield `GoFunc` holding a token `Tok` (forRange's `state` cell at `0` and its `exit`
  cell untouched), with the yield's spec (the body's outcome `executeVal`/`continueVal` gives `Tok`
  back and `true`; `breakVal`/`returnVal r` gives `Done bv` and `false`); after the iterator returns
  with `Tok` or `Done bv`, the loop's outcome follows. Bodies that panic are not covered. Plus
  `wp_app_recV` (a closure argument as a `GoFunc` value). No axiom.
- **Proposed change.** The same rule in `Perennial/Golang/Theory/Loop.lean` for `n = 0, 1, 2`, with
  a sealed postcondition in `wp_for`'s style and a panicking-body case; a `wp_for_range` tactic.
- **Status.** Candidate; not started in Perennial.

## `reflect.Kind` is an axiomatized type: `v.Kind() != reflect.Slice` cannot step (2026-11-10, k8s 7e-2)

- **Missing.** Perennial's `reflect` translation declares `Kind` (Go: `type Kind uint`) as an
  axiomatized type (`axiom Kind : Type`, `Kind.underlying` an axiom), so `GoOp GoEquals reflect.Kind.ty`
  has no semantics; the trusted `reflect.Value.Kind.spec` (this repository) returns `#(W64 23)`.
- **Needed by.** `store.GetList`'s `if err != nil || v.Kind() != reflect.Slice` (`store.go:780`).
- **Workaround here.** `store.GetList.wp_proof` takes the hypothesis `reflect.KindCompare.spec`
  (`Spec/reflect/KindCompare.lean`: `go.IsStrictlyComparable reflect.Kind.underlying w64`), a
  trust-boundary axiom since 2026-11-10 (`Proof/reflect/KindCompare.lean`, decided by etcd-grove-81
  after the review; Go test `TestKindIsUint`, `examples/k8s7e2attack/attack_test.go`). The change
  below would remove it.
- **Proposed change.** Translate `reflect.Kind` as `type Kind uint` (it is a plain named integer
  type), so its comparison is the translated one; or a reflect model fact stating the underlying.
- **Status.** Recorded; not started in Perennial (the axiom here stands in for it).

## An `RWMutex` can be made a lock only unlocked (2026-11-10, mvccfull F1's B3)

- **What happened.** `mvcc.NewStore` locks `s.mu` while the store is still private memory and, in
  compaction mode, `restore()` resumes a compaction (`compactLockfree`) before the deferred
  `s.mu.Unlock()`. That call takes the store (`isStore`), whose `s.mu` must be a lock
  (`isRWMutexGuard`); but `sync.init_RWMutex` takes an unlocked `RWMutex` (`zero_val`) and its
  resource `▷ P 1`, which `NewStore` has only after `restore()` (the index it publishes, the fixed
  registration).
- **Local workaround.** `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/RWMutexWLocked.lean`:
  `init_RWMutex_wlocked P rw : rw ↦ rwW ={E}=∗ ownRWMutexWLocked rw P ∗ [∗list] … ownRWMutex rw P`
  (every slot), from the write-locked memory `plain.wp_Lock` leaves; `P 1` is given at the unlock
  (`RWMutex.wp_Unlock_guard`). Proved over Perennial's sealed RWMutex internals
  (`rwmutex.ownRWMutexInvariant_unseal`, `isRWMutex_unseal`, `isLock_unseal`, `ownLock_unseal`,
  `isMutex_unseal`, `ownMutex_unseal`, the guard's `invSt`), mirroring `rwmutex.init_RWMutex` at the
  protocol's `Locked`/`IsLocked` state, with `init_lock_locked` for the inner `Mutex`. No axiom.
- **Proposed (general).** `sync.init_RWMutex_wlocked` (and `init_Mutex_locked`) in Perennial, next to
  `init_RWMutex`: a lock made by its holder.
- **Status.** Local lemma; to be proposed.

## `Int64.Load` with the fraction chosen inside the update (2026-11-10, mvccfull F1 Prove)

- **Missing.** `sync.atomic.Int64.Load.spec` (and `LoadInt64.spec`) quantify the fraction `dq` before
  the atomic update; a caller whose fraction is known only once it opens its invariant (the update's
  `∃ dq x, ownInt64 u dq x ∗ …`) cannot use them, although their proofs open the update before the
  load and would prove the stronger form unchanged.
- **Needed by.** mvccfull's `inBounds.spec` (frozen): `check(v <= hi.Load())` with the caller's
  accessor picking the fraction.
- **Workaround here.** `Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull/AtomicLoad.lean`:
  `wp_LoadInt64_ex`, `wp_Int64_Load_ex`, Perennial's two proofs re-run with `∃ dq` inside the
  update (`wp_load_bytes_typed`, the struct field). No axiom.
- **Proposed (general).** State `LoadInt64`/`Int64.Load` (and the other atomic loads) with the
  fraction inside the update, the current form a corollary.
- **Status.** Local lemma; to be proposed.

## `GoStringLe` as the negation of the converse `GoStringLt` (2026-11-10, mvccfull F1 Prove)

- **Missing.** `go.GoStringLe a b ↔ ¬ go.GoStringLt b a`, a general fact about Perennial's string
  order.
- **Workaround here.** `goStringLe_iff_not_lt` in
  `Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull/inRange.lean`.
- **Proposed (general).** The lemma next to `GoStringLe`'s definition in Perennial.
- **Status.** Local lemma; to be proposed.

## `fmt.Errorf`'s spec does not admit an error argument (`%w`) or a `Stringer` (2026-11-09, branch `specs-only`)

- **The gap.** Perennial's `fmt.Errorf.spec` requires `ArgsWf` (basic-typed arguments). Three calls the
  specs-only branch specifies fall outside it: mvcc's `rangeKeys` (`fmt.Errorf("…: %w", ctx.Err())`,
  `kvstore_txn.go:121`), raft confchange's `Changer.apply` (a `ConfChangeType`, which has `String`) and
  raftpb's `ConfState.Equivalent` (four `*ConfState`s).
- **Local workaround.** raftpb states a local assumed spec, `RaftPb.fmtErrorf.spec`
  (`SpecPlan/Spec/go_etcd_io/raft/v3/raftpb/FmtErrorf.lean`); mvcc's `rangeKeys` proof will rest on the model at
  that step (`Mvcc.rangeCtxErr`'s laws: non-nil, fresh, none of mvcc's sentinels). Related: the entry
  above (the model can be unfolded to learn false facts).
- **Proposed (general; record only, nothing changed in Perennial).** `fmt.Errorf.spec` for a `%w` argument
  (a fresh wrapping error whose `Unwrap` is the argument) and for arguments with a `String`/`Error`
  method (the method's spec called with the caller's ownership).
- **Status.** Recorded only.

## OsFs: no `rename`, and no crash case reverting an unsynced rename (2026-11-09, branch `specs-only`)

- **The gap.** Perennial's OsFs model has no `rename`, and its crash relation cannot bring back the file a
  rename replaced when the directory was not fsynced afterwards. etcd renames onto live paths: defrag
  (`os.Rename(tdbp, dbp)`, `backend.go:557`) and the snapshot install (`snap.dbFile_rename`), and fsyncs
  the directory only in some paths.
- **Local workaround.** The specs-only branch states `Snap.dbFile_rename` as a trusted triple and gives the
  backend a `beRevert`/`beNoRevert` token with a revert case in `beCrash`
  (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/`); that case's realization is open until OsFs has it.
  The second crash pass (`notes/specs-only/verify/repair5-crash.md`, G-b) adds two more uses of the same
  gap: a file renamed over while still open (`Backend.beDetached`, `applySnapshot`'s old backend, whose
  open handle keeps the unlinked inode until `Close`), and its close or crash folding that inode's image
  into the revert list (`beCloseUpd`'s detached form, `beDetached_crash`): both need OsFs's files to be
  inodes a rename can unlink while open, not paths.
- **Proposed (general; record only, nothing changed in Perennial).** OsFs `rename` with POSIX semantics,
  its crash case (the old directory entry survives unless the directory was fsynced after the rename),
  and a directory fsync.
- **Status.** Recorded only.

## The crash frame cannot take client-owned durable state out of an invariant opened inside atomic updates (2026-11-09, branch `specs-only`)

- **The gap.** Perennial's crash frame (`CrashAdequacy.lean`) is proved at boot and gets only invariants
  and its own closure. A program keeps its durable resources (etcd's `EtcdServer.diskState`; 4a's
  `beHist`, 4c's `boltState`, the WAL's and the snapshotter's) in an invariant that the running code
  opens inside callees' atomic updates (the WAL's `Save`, `SaveDBFrom`, bbolt commits). To apply a crash
  law, the frame must take those resources out of the invariant; an accessor fired inside a callee's
  atomic update cannot rule out that the frame already took them, since that needs the generation's
  `notCrashed`, which only a thread's step owns (through the state interpretation).
- **Local workaround.** The specs-only branch states the crash laws (`disk_crash`, `beCrash`,
  `boltCrash`, ...) over resources held in the invariant and records the extraction as a gap
  (`notes/specs-only/verify/repair2-crash.md`, decision 1; `top.md` K6).
- **Proposed (general; record only, nothing changed in Perennial).** A crash-aware invariant: opened only
  at a thread's step (which refutes `crashed`), and handed whole to the crash frame. Alternative: durable
  extension operations whose atomic updates admit a `crashed` answer, refuted at their own step.
- **Status.** Recorded only.

## No WP step lemma refutes the generation's `crashed` (2026-11-09, branch `specs-only`)

- **The gap.** Every thread step's state interpretation holds the generation's `notCrashed`
  (`Lifting.lean:752`, `goose_bstateInterp_eq`), and `notCrashed_crashed` (`CrashToken.lean:50`)
  refutes `crashed` with it, but no lemma hands a WP step that fact: nothing proves
  `crashed -∗ WP e {{ Φ }}` for an expression that takes a step, or lets an atomic step's proof use
  `notCrashed` (a grep for uses of `notCrashed_crashed`, or for `crashed -∗ WP`, finds none).
- **Who needs it.** The specs-only branch's per-generation tokens are a token **or the generation's
  `crashed`** (raft's `nodeVacant`, 2e's `diskIdle`; `notes/specs-only/verify/repair4-raft-crash.md`,
  open question D28), so that the crossing laws hold at every next generation, the current one
  included; their realizations refute the `crashed` disjunct at the consumer's first step (raft's
  `StartNode`/`RestartNode`, `NewServer`), which needs this lemma (`verify/F2-crash.md`, second tier
  s1). Distinct from the crash-aware invariant entry above, which is about the crash frame taking
  resources out of an invariant; this one is about a running thread ruling out `crashed`.
- **Local workaround.** None needed in the statements: the realizations' text cites the step fact,
  and the laws are stated as obligations.
- **Proposed (general; record only, nothing changed in Perennial).** A lifting lemma
  `wp_crashed_elim : ¬ IsValue e → crashed ⊢ WP e @ s; E {{ Φ }}` (the first step's state
  interpretation gives `notCrashed`, hence `False`), and its atomic-step form for a step proof that
  opens an invariant holding a `token ∨ crashed` disjunction.
- **Status.** Recorded only. 2026-11-13: the atomic-step form is proved locally (`wp_atomic_nc`,
  `wp_notCrashed_acc`; the entry "`notCrashed` before a step" under "Open").

## No specs of `fmt.Fprintf` / `strings.Builder` (2026-11-09, branch `specs-only`)

- **The gap.** raft's `DescribeConfChange` and raftpb's `ConfChangesToString` build strings with a
  `strings.Builder` and `fmt.Fprintf`, which Perennial does not specify.
- **Local workaround.** Both are stated as assumed trust-boundary specs on the specs-only branch
  (`SpecPlan/Spec/go_etcd_io/raft/v3/DescribeConfChange.lean`, `raftpb/ConfChangesToString.lean`).
- **Proposed (general; record only).** Specs of `strings.Builder` (`WriteString`, `WriteByte`, `String`)
  and of `fmt.Fprintf` to an `io.Writer` with basic-typed arguments.
- **Status.** Recorded only.

## 2026-11-13: `fmt.Errorf` with `%w` does not wrap (the WAL decoder)

- **Missing.** Perennial's `fmt.Errorf` model returns a fresh error for `%w` that does not wrap its
  argument, so `errors.Is(fmt.Errorf("...: %w", io.ErrUnexpectedEOF), io.ErrUnexpectedEOF)` is false in
  the model and true in Go; and the spec refuses error arguments (`ArgsWf`). etcd's WAL decoder
  (`decoder.go`: the "too large" and CRC-mismatch errors) and `walpb.Record.Validate` pass errors to `%w`,
  and `ReadAll`'s read-mode branch tests `errors.Is(err, io.ErrUnexpectedEOF)` on them.
- **Workaround here.** The WAL proofs take `fmt.ErrorfErrs.spec` as a hypothesis (branch `wal-dec`,
  `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`), to be discharged when linking.
- **Proposed.** `Errorf`'s model wraps the `%w` arguments (Go's `wrapError`/`wrapErrors`) and its spec
  accepts error arguments, with `errors.Is`/`Unwrap` following the chain.

## 2026-11-14: `errors.Is` on `fmt.Errorf`'s result, and on `proto.Unmarshal`'s error (the WAL decoder)

- **Missing.** A reader looping to `io.EOF` (etcd's `wal.ReadAll`) tests `errors.Is(err, io.EOF)` on the WAL
  decoder's errors, which include `fmt.Errorf("%w: ...", io.ErrUnexpectedEOF)`, `fmt.Errorf("%w: ...",
  Validate's error)` and `proto.Unmarshal`'s error. Perennial's `Errorf` spec gives nothing of its result
  (and refuses error arguments, the 2026-11-13 entry above); this repository's trust-boundary axiom
  `proto.UnmarshalPb.spec` (`LinuxFs/Proof/google_golang_org/protobuf/proto/UnmarshalPb.lean`) says only
  that the error is not `nil`.
- **Workaround here.** Two hypotheses of the decoder's proof (branch `wal-readall15`):
  `fmt.ErrorfErrsNot.spec` (`LinuxFs/Spec/fmt/ErrorfErrsNot.lean`: the result is not `t` and `errors.Is(_, t)`
  answers `false` on it, `t` a package variable's value, when so of every error argument) and
  `proto.UnmarshalWalRecordE.spec` (`LinuxFs/Spec/google_golang_org/protobuf/proto/UnmarshalWalRecordE.lean`:
  the error is not `io.EOF`, the same answer). Both hold in Go (the files' headers say why).
- **Proposed.** With the 2026-11-13 entry's `Errorf` (wrapping `%w`, `*wrapError` results), the first follows
  from `errors.Is`'s walk; Perennial's `errors.newVar` could keep the `*errorString`'s points-to, so that
  freshness proves "not `t`" under today's model too. For `proto`: an extension of `UnmarshalPb.spec`'s error
  (not `io.EOF`, `errors.Is(_, io.EOF)` false) — a trust-base change, for the user.
- **Status.** Recorded; hypotheses in place.

## 2026-11-13: `go.NotInterface` does not unfold `go.int64` (method calls on `time.Duration`)

- **Missing.** `MethodResolve` on a named type over `int64` (`time.Duration`) needs a `go.NotInterface go.int64`
  instance that Perennial's instances do not derive (they do not unfold `go.int64`).
- **Workaround here.** A local instance in the WAL encoder's proofs (branch `wal-enc4`, `LinuxFs/.../wal/EncDefs.lean`).
  The same for `go.uint32` (`io/fs.FileMode.IsDir`, `os.MkdirAll`'s proof, branch `wal-osau4-mkdirall`:
  a `haveI` in the macro `fileStat_isDir` of `LinuxFs/Proof/os/MkdirAll{,Parts}.lean`). Every predeclared
  integer type is a plain `def` (`go.uint32 := go.Named go!"uint32" []`), so no instance of the class sees it.
- **Proposed.** The instance (or the unfolding) in Perennial, for every predeclared type.

## 2026-11-13: `errors.Is` only for pointer targets (`fileutil.TryLockFile`'s `EWOULDBLOCK`)

- **Missing.** Perennial's `errors.Is.spec`/`errors.is.spec` admit only `nil` and pointer targets
  (`IsPointerError`). `fileutil`'s `ofdTryLockFile`/`flockTryLockFile` call `errors.Is(err,
  syscall.EWOULDBLOCK)` with an errno target (a `uintptr`, comparable, so Go's walk returns), and
  `syscall.Errno.Is` has no spec.
- **Workaround here.** `TryLockFile`'s proof takes `errors.IsErrno.spec` (`LinuxFs/Spec/errors/IsErrno.lean`:
  an errno `err` and an errno target give some boolean) as a hypothesis (branch `wal-read4`).
- **Proposed.** `errors.is.spec` for any target whose type's errors in the tree hold comparable values
  (the comparison `err == target` is then defined), and a spec of `syscall.Errno.Is` (a `switch` comparing
  the target with `oserror`'s pointer errors).
- **Also (2026-11-14, `wal.Exist`):** `errors.Is(err, os.ErrNotExist)` of an `os` error (a `*PathError` of
  an `Errno`) has a pointer target, so `errors.Is.spec` applies, but needs the error tree (`*PathError`'s
  `Unwrap`, `Errno.Is`) and `os.ErrNotExist = oserror.ErrNotExist` distinct from `oserror`'s other errors
  in the package facts. Workaround: the hypothesis `errors.IsPathErrnoNotExist.spec`
  (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ExistCallees.lean`).

## 2026-11-14: `errors.newVar` forgets the allocation (the WAL decoder's environment, `wal-readall17`)

- **Limitation.** `errors.newVar X msg` (`Perennial/Proof/errors/NewVar.lean`, what `io`'s fact keeps of
  `io.EOF`, `io.ErrUnexpectedEOF`, ...) holds `globalAddr X ↦□ *errorString(x)` and `Error()`'s spec, but
  not `x`'s field (`wp_New_errorString` persists it and drops it). So two `errors.New` variables cannot be
  shown different (`io.EOF ≠ io.ErrUnexpectedEOF`, `errors.Is(walpb.ErrCRCMismatch, io.EOF) = false`),
  which Go guarantees (distinct allocations). The part's WAL hypothesis `WalDecEnvSupply`
  (`openAtIndex.lean`) is blocked only by this.
- **Proposed (general).** `newVar` keeps `structFieldRef errorString "s" x ↦□ msg` (so variables with
  different messages are different pointers), or a ghost "fresh allocation" token; `wp_New_errorString`
  returns it.
- **Also:** `errors.Is(err, io.EOF)` on the part's `*PathError`s (`errors.IsPathErrnoEof.spec`,
  `LinuxFs/Spec/errors/IsPathErrnoEof.lean`), the same gap as `IsPathErrnoNotExist.spec` above.

## 2026-11-14: The WAL's leaf specs (`wal-leaf1`): `errors.As` first match, `Errno.Is`

- **Missing.** (1) Perennial's `errors.As.spec` (an axiom: `As` is reflection) says nothing of the result
  (`∃ b v'`), even when `err`'s own dynamic type is the target's element type, where Go's `as` stores `err` and
  returns `true` before any `Unwrap`; and it asks for the whole error tree. `renameWAL`'s
  `errors.As(err, &linkErr)` on `os.Rename`'s `*LinkError` needs the first-match case
  (`errors.AsLinkError.spec`, `LinuxFs/Spec/errors/AsLinkError.lean`). (2) `syscall.Errno.Is` and
  `(*fs.PathError).Unwrap` are names-only in the part (`LinuxFs/Code/syscall.toml`, `io/fs.toml`: this repository's
  goose configuration, not Perennial's), so `errors.is` cannot step past an errno (`errors.IsErrno.spec`,
  `errors.IsPathErrnoEof.spec`); with them translated, `IsErrno` still needs the 2026-11-13 entry's `errors.is.spec`
  at a comparable non-pointer target, and both need `oserror`'s errors (and `errors.ErrUnsupported`) distinct from
  the target (the `errors.newVar` entry above).
- **Workaround here.** The three stay hypotheses of their callers' proofs (plan §8, "Leaf specs log").
- **Proposed.** (1) `errors.As.spec` with a first-match case: if `err`'s dynamic type is the target's element type,
  `As` returns `true` and stores `err`, with no tree premise. (2) Translate `Errno.Is` and `PathError.Unwrap` in the
  part (a configuration change here), and Perennial's `errors.is.spec` for comparable targets.
- **Status.** Recorded.
