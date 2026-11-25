# Axiom review: `github_com.go_redis.redis.v8.wp_initialize'` (dsverify quepaxa, rabia)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` at `23a50393f5` (the brief named branch `dsv-fix3`; the worktree's
branch was `dsv-fix2b`); Perennial `fce59af75`; Go: `github.com/go-redis/redis/v8` v8.11.5 (both kits'
`go.mod`), toolchain go1.27.3.

## The axiom

`Perennial.github_com.go_redis.redis.v8.wp_initialize'` (`Dsverify/Proof/github_com/go_redis/redis/v8/Init.lean`;
the class `InitHyp` there states the same triple, still a premise of `rabianet`'s statement at this
revision):

```lean
axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.go_redis.redis.v8 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.github_com.go_redis.redis.v8 }}
```

- **Translation** (names and types only, `translate = ["!*"]`, `imports = ["!*"]`):
  `Dsverify/Code/github_com/go_redis/redis/v8/chunk0.lean:1212-1217`. `PkgInfo.pkgImportedPkgs := []`;
  `initialize'` is `package.init redis (λ_. exceptionDo (X₁.init #(); …; X₅₀.init #()))` over 50
  opaque values: `errClusterNoNodes`, `ErrClosed`, `errRingShardsDown` and 47 `«_».init` (the
  `var _ I = (*T)(nil)` assertions). This matches the Go source exactly: 3 runtime variables
  (`cluster.go:22`, `error.go:14`, `ring.go`) and 47 blank assertions (`command.go`, `commands.go:409-415`,
  `error.go:26`, `pipeline.go`, `script.go`, `universal.go`); no `func init` in a non-test file.
- **Package fact** (`Base.lean`): `define_is_pkg_init iprop(True)`, `build_get_is_pkg_init_wf`, so
  `GetIsPkgInitProp redis g` is `g redis = isPkgInit redis ∧ True` and `isPkgInit redis` is `True`.
- **Users**: `Dsverify/Proof/raxos/replica/src/Init.lean:110` (QuePaxa's replica, the kit's five
  servers) and `Dsverify/Proof/rabia/roles/server/layers/proxy/Init.lean:82` (Rabia's proxy).
  `HYP_IMPORTS` is unset in `etc/dsv/quepaxa.py` and `etc/dsv/rabia.py` (default `'all'`): the
  generator's inventory sees redis's real imports, but redis's own `GetIsPkgInitWf` (from `PkgInfo`,
  imports `[]`) constrains none of them.

So the claim, in plain words: running redis's initialization returns `#()`, **never panics** (in any
run of any program), touches no resource the caller holds (frame), and records redis with fact `True`.

## Verdict: **refuted** (Go side; Lean counterexample not built)

The no-panic claim is false of Go under the `fips140` GODEBUG setting. Importing go-redis pulls
`crypto/tls` (from `options.go`, `cluster.go`, ...) and with it `crypto/internal/fips140`, whose
`init` (go1.27.3 `src/crypto/internal/fips140/fips140.go:20-31`) does

```go
v := godebug.Value("#fips140")
switch v { case "on", "only": ...; case "debug": ...; case "off", "":
default: panic("fips140: unknown GODEBUG setting fips140=" + v) }
```

Go runs it before redis's own variables, as part of initializing redis's imports. The model runs none
of redis's imports (`pkgImportedPkgs := []`), so the axiom's "initializer returns" is the only place
the model accounts for that code, and it says it never panics, with no premise on the environment.

Perennial's own convention says this premise is needed: `Perennial/TrustedCode/crypto/fips140.lean`
makes the setting the opaque `godebugFips140` ("a theorem about a program holds for every value it
could be") and `GodebugFips140Off` the environment premise "under which the packages around
`crypto/fips140` that goose does not translate (their initializers are not run by the model) do not
panic". The redis axiom states that same consequence for every value of the setting. Neither kit's
statement takes `GodebugFips140Off` (`grep`: no occurrence under `Dsverify/`).

**Go evidence** (scratch module `/shared/tmp/redisinit-review`, not committed; go1.27.3): `main`
imports `github.com/go-redis/redis/v8` and checks `redis.ErrClosed`.

```
$ ./rinit                                  # GODEBUG unset (also fips140=, off, on, only, debug)
main ran; ErrClosed = redis: client is closed Nil = redis: nil       exit=0
$ GODEBUG=fips140=bogus ./rinit
panic: fips140: unknown GODEBUG setting fips140=bogus
goroutine 1 [running]:
crypto/internal/fips140.init.0()
	.../go1.27.3.linux-amd64/src/crypto/internal/fips140/fips140.go:27 +0xe5      exit=2
$ GODEBUG=fips140=bogus ./plain            # the same with only fmt imported
plain main ran                                                       exit=0
```

**The counterexample, as it would be built** (not built: the brief allowed no new Goose project,
no edits outside this report and no builds). It is `examples/axiomcx/redisfips` with
`import _ "github.com/go-redis/redis/v8"; func Main() {}`, translated with redis names-only as in
`Dsverify/`. Its theorem is `{{ ownInitializing g }} initialize' #() {{ RET #(); ownInitializing g ∗ isPkgInit pkg }}`:
the generated init walk with one `wp_apply github_com.go_redis.redis.v8.wp_initialize'` and
`is_pkg_init_finish`, plus `Main`'s empty body. Run with `GODEBUG=fips140=bogus`, the program panics
before `Main`. No other axiom is needed: the generated init proofs of the kits already do exactly this
step.

**What rests on it**: `quepaxa_remote_robust` (QuePaxa's replica imports redis; there the grpc
initializer axiom has the same gap, since `google.golang.org/grpc` also reaches
`crypto/internal/fips140`) and `rabianet`'s closed theorem, where redis is the **only**
untranslated package reaching `crypto/internal/fips140` (`go list -deps`: zerolog, gogo `proto`,
`gogoproto`, redis's `internal/proto` and `os/signal` do not reach it). Under
`GODEBUG=fips140=<anything else>` every machine that runs a replica (QuePaxa) or a proxy (Rabia) dies
at start. The statements claim no thread has a top-level panic.

## Attacks tried

1. **Environment-dependent init panic** (above): **succeeds**. Values `""`, `off`, `on`, `only`,
   `debug` run (a normal build, not `purego`, passes `check`'s checksum); any other value panics.
   No other GODEBUG-, environment- or file-dependent panic was found in the closure's initializers
   (all `func init` of the ~170 packages of `go list -deps` were read, excluding `runtime`/`internal`
   ones that cannot fail on a supported platform). `crypto/internal/fips140/check`'s panics need
   `fips140` enabled on a platform it does not support, or a binary without its checksum.
2. **A false package fact.** The fact is `True`; it claims nothing about `ErrClosed`,
   `errClusterNoNodes`, `errRingShardsDown` or any internal variable. There is nothing to read back.
3. **The initializer panics in the default environment.** No. Redis's own initializers are
   `fmt.Errorf`/`errors.New` of constants, a copy of `pool.ErrClosed`, and 47 nil conversions to
   interfaces. Its internal packages' initializers are `log.New(os.Stderr, …)`,
   `rand.New(&source{rand.NewSource(1)})`, a `decoders` slice literal, `newStructMap()` (a
   `sync.Map`), the `crc16tab` literal, `sync.Pool{New: …}`, `time.Time{}` and two `errors.New`.
   xxhash has constant copies and go-rendezvous has nothing. `GODEBUG=inittrace=1` shows each
   initializer once, and `main` runs.
4. **Running twice.** Go runs each package's initialization once. In the model, `package.init`'s
   check (`wp_package_init`, Perennial `Pkg.lean:478`) returns at once when the package is recorded,
   and the post holds either way. The exclusive `ownInitializing` rules out concurrent runs.
5. **Imports missing from the precondition.** `GetIsPkgInitProp` constrains only `g redis`. The model's
   `initialize'` initializes no import, so `ownInitializing`'s map gains only redis and the table needs
   no import's fact. This is consistent, and `HYP_IMPORTS = 'none'` would be equally correct here (the
   README's condition: the initializer runs no import's initializer in the model).
   - In Go the imports run first. Their only cross-package writes are `crypto.RegisterHash` (`crypto/sha1`,
     `sha256`, `sha512`, `sha3`, `md5`), `impl.Register` (internal), `log`'s `internal.DefaultOutput`,
     `syscall`'s `RLIMIT_NOFILE` raise, and runtime and `sync` hooks. None of them is state a Lean
     resource describes: `crypto` is not translated, and Perennial's `crypto/sha1`/`sha256` `init`
     models are no-ops for that reason (`TrustedCode/crypto/sha1.lean`).
   - The order differs: a package the program also imports directly (`log`, `time`, `math/rand`,
     `os`, ...) is initialized later in the model than in Go. This is harmless: none of redis's
     closure writes those packages' variables. Redis's `internal/rand` seeds a private source and
     does not touch `math/rand`'s global, and `internal.Logger` is a new `*log.Logger`, not `log.std`.
6. **Frame / too much ownership.** The real initialization writes only variables of redis, its
   internal packages and the closure above. None is allocated by the names-only translation or owned
   by any Lean proof.
7. **Cross-world entailment.** Not applicable: the fact is `True`, with no cells and no opaque
   function of a pointer.
8. **Inconsistency (`⊢ False`).** The axiom is a WP about opaque `X.init` values that Lean cannot
   reduce. `InitInstancesLinked.lean` derives it from `localOpaqueInitsOk` (each `X.init` returns `#()`
   from `True`), which `λ_. #()` satisfies. So the axiom alone gives no `False`; it is only false of
   Go, in the environment above.

Not tried: the quantification over every `GoGlobalContext`/`go.Semantics` (shared by every interim
initializer axiom, `notes/dsv-instances.md`); building the Lean counterexample (constraints of this
review).

## Proposed restatement (not applied)

Give the axiom (and `InitHyp.wp_init`) the premise `(Hfips : crypto.fips140.GodebugFips140Off)`
(Perennial's `TrustedCode/crypto/fips140.lean`), and say in its docstring that go-redis's imports
reach `crypto/internal/fips140`, whose initializer panics on an unknown `fips140` setting. Then:

- both kits' statements take `GodebugFips140Off` as an environment premise, as Perennial's
  `net/http` model does (`Net/TrustedCode/net/http.lean`);
- QuePaxa's grpc initializer axiom (`google_golang_org.grpc.wp_initialize'`) needs the same premise
  for the same reason;
- `etc/dsv` could check this mechanically: a `HYP_INITS` package whose `go list -deps` contains
  `crypto/internal/fips140` gets the premise.

No Go bug found (the panic on an unknown GODEBUG value is documented Go behaviour).
