## S7 (etcd-grove): crc32 hooks, go/token.IsExported, shared infra

Branch `go-models-rest/2026-11-24` (etcd-grove), my commits: 6bfc699d3f (gomodel `[model]` dir from the pin,
no copy), 97e1b44ff3 (CI Go 1.27.3; token model), b68f8335b8 (netgo, shared), 9dac1834d6 (tcb-report
"Go models", `etc/model-tests.sh`), fd7d0f18b6 (crc32 + token, committed by the lead), the gomodel
Base/Init/LocalChoose part of e251433367, 14aa39bd7f (proof fixes). Head 14aa39bd7f.

### hash/crc32 (`Code/hash/crc32.toml`)
- Already real Go before S7 (etcd-grove#14): `MakeTable`, `update`, `simpleUpdate`, slicing-by-8, the once, the package state.
- **Go model** (`models/hash/crc32/model.go`, `replaces = [archAvailableCastagnoli, archInitCastagnoli, archUpdateCastagnoli]`, `trusted = []`):
  irreducible: `cpu.X86.HasSSE42` (set by the runtime's cpuid assembly, not package init) and the bodyless
  assembly `castagnoliSSE42`/`castagnoliSSE42Triple`.
  - `archAvailableCastagnoli`: `return gomodel.Choose()` (any CPU; called once per process).
  - `archInitCastagnoli`: `{}` (Go's panic needs `!HasSSE42`, excluded by the package's call order; the K1/K2 tables it fills are read only by Go's `archUpdateCastagnoli`).
  - `archUpdateCastagnoli`: `return simpleUpdate(crc, simpleMakeTable(Castagnoli), p)` (trusted claim: the SSE4.2 assembly computes CRC-32C; Go's `TestArchCastagnoli`).
- **Deleted trusted Lean**: `TrustedCode/hash/crc32.lean` (105 lines; 3 `.impl`s, about 40 lines). Its pure table definitions moved to `Spec/hash/crc32/Model.lean` (spec vocabulary, not trusted).
- **Caveat** (mechanism, recorded already): a model can reorder package-variable init; here `IEEETable` vs `castagnoliInitOnce` is unaffected (the hooks run only when the once's function is called).

### go/token (`Net/Code/go/token.toml`, project models-net)
- **Go model** (`models/go/token/model.go`, `replaces = [IsExported]`), decision D1: the real Go translates
  (try1: `IsExported`, `unicode.IsUpper` and its tables), but its proof needs `isPkgInit unicode`/`utf8` in
  `IsExported.spec`, a new premise. Model: `""` → false; first byte `< utf8.RuneSelf` → `'A'<=c && c<='Z'`
  (exact: unicode/letter.go's Latin-1 fast path); otherwise `gomodel.Choose()` (Go's result depends on the case tables).
- **Deleted trusted Lean**: `Net/TrustedCode/go/token.lean` (54 lines, 1 `.impl`; its non-ASCII branch was `ArbitraryInt`'s low bit, now `Choose`).

### Shared infra
- `Code/internal/gomodel.toml`, `Net/Code/internal/gomodel.toml`: `dir = .lake/gomodel/internal/gomodel`, materialized by `etc/gomodels.py` from the Lean pin (no copy). Lean: Perennial's `GeneratedProof.internal.gomodel`.
- LOCAL until the integration pin bump (delete then): `Proof/internal/gomodel/{Base,Init}.lean` (its `IsPkgInit`, fact `True`, gen-init's `PERENNIAL_HERE`) and `LocalChoose.lean` (`Choose`'s spec from its `.impl`).
- `etc/tcb-report.py` "Go models" table; `etc/model-tests.sh` (`etc/gomodels.py test`); CI `setup-go 1.27.3`; `etc/goose.py`'s `BUILD_TAGS = ["netgo"]`.

### Not retired (decisions)
- `idutil.Generator.Next`: left as is (#30, status quo trust).
- J3 `JSONModel*`: stays on per-project `-overlay` (option A). Go refuses an overlay beneath GOMODCACHE, and most projects load etcd's server from there. One mechanism follow-up, recorded with primitive.Mutex's.
- #24 `grpc.Server.Serve` and #37 `PbModel*`: left to their claims. `std_models`: deferred.

### New primitives
None. The models use Perennial's `gomodel.Choose`.

### Premise and statement changes
None. No spec statement changed, and no premise or binder was added.

### `#print axioms` (VM, 14aa39bd7f)
`archAvailableCastagnoli.wp_proof`, `archInitCastagnoli.wp_proof`, `archUpdateCastagnoli.wp_proof`,
`hash.crc32.wp_initialize'`, `go.token.IsExported.wp_proof`: each `[propext, Classical.choice, Quot.sound]`.
The top-level results (`mvccfull_robust`, `etcd_robust_single_process`, net/rpc `Server.register.wp`)
are not built yet: they sit behind egos's os/syscall failures (below).

### Evidence
- `etc/model-tests.sh crc32 token token-diff` passes. It runs Go's `hash/crc32` tests (all; `TestArchCastagnoli` SKIPs under the overlay, since `Choose`'s Go body is false: the model's update is exercised by the adversarial review's run with `Choose` forced true, where all crc32 tests pass, and by real Go's `TestArchCastagnoli`), `go/token`'s tests, and `rpcdifftest.TestIsExportedASCII` (every ASCII first byte), all under the overlay. Left out: non-ASCII IsExported cases (the choice point; its Go body returns false).
- `goose.py --check` (goose 78d6ef937), all projects: 70 up to date, including every project that reaches crc32 or go/token. The only differences are `Code/os.lean` (egos) and `{Net,KvNet}/{Code,GeneratedProof}/net.lean` (egnet).
- `gen-specs-pkginit --check`: crc32 fixed. `os` and `syscall` still differ (egos).
- gen-init: my outputs are consistent (with egos's line below, the only differences are os/syscall/filepathlite files and the PkgTables over them).
- `tier-check --check` ok.
- VM build of every importer (939 leaves, about 8.4k modules): everything not behind `Proof.syscall.*`/`Proof.os.Base` builds. Those two fail on egos's os/syscall WIP, so the rest of the cone has not been built yet.
- review-trusted (R12, by hand: `trusted-delta.py` is Perennial-only): each model checked line by line against Go 1.27.3 (`crc32_amd64.go:54-93`, `token.go:316-319`). Every `Choose` has its reason. The `[model]` tables replace only, with no `added_methods`.
  - NOTE R1/R2: `IsExported` sits on rung 4 although rung 2 (real Go) translates. Kept by decision D1, because the real Go needs a premise.
  - No adversarial subagent (the takeover forbids sub-agents).

<details><summary>Model next to the real Go (Go 1.27.3)</summary>

```go
// real crc32_amd64.go                         // model models/hash/crc32/model.go
func archAvailableCastagnoli() bool {          func archAvailableCastagnoli() bool {
	return cpu.X86.HasSSE42                    	return gomodel.Choose()
}                                              }
func archInitCastagnoli() {                    func archInitCastagnoli() {}
	if !cpu.X86.HasSSE42 { panic(...) }
	castagnoliSSE42TableK1 = new(sse42Table)
	castagnoliSSE42TableK2 = new(sse42Table)
	... castagnoliSSE42(val, tmp[:...]) (asm)
}
func archUpdateCastagnoli(crc uint32,          func archUpdateCastagnoli(crc uint32, p []byte) uint32 {
    p []byte) uint32 {                         	return simpleUpdate(crc, simpleMakeTable(Castagnoli), p)
	if !cpu.X86.HasSSE42 { panic(...) }        }
	... castagnoliSSE42Triple / castagnoliShift (asm, K1/K2)

// real go/token/token.go                      // model models/go/token/model.go
func IsExported(name string) bool {            func IsExported(name string) bool {
	ch, _ := utf8.DecodeRuneInString(name)     	if len(name) == 0 { return false }
	return unicode.IsUpper(ch)                 	c := name[0]
}                                              	if c < utf8.RuneSelf { return 'A' <= c && c <= 'Z' }
                                               	return gomodel.Choose()
                                               }
```
</details>

### Open items
1. **egos**: `etc/gen-init.py`'s `NET_MAIN` needs `'internal.filepathlite'`. Without it gen-init dies with `KeyError: 'internal.filepathlite'`, because os now imports it. Then regenerate: os/syscall Init in every part, `Net/Proof/internal/filepathlite/Init.lean`, about 100 PkgTables, and SpecPlan's os/syscall PkgInit. `Proof.syscall.*` and `Proof.os.Base` fail to build. I left all of it uncommitted and untouched.
2. Once (1) is done: rebuild the cone (`gmr-egrest/leaves.txt` without `notes.*`). Then run `tcb-report.py` before and after, and `--check`. I expect no axiom or sorry delta from S7: S7 deletes TrustedCode and adds models only.
3. Integration bump: delete `Proof/internal/gomodel/{Base,Init,LocalChoose}.lean` if Perennial provides them, and drop `PERENNIAL_HERE`'s `internal.gomodel`.
