# bbolt v2: the translation with bodies (infrastructure, 2026-11-03)

Branch `worktree-bbolt-v2`, from `lean` `5eea04e0d6`. The setup for re-verifying bbolt (v1.5.0,
etcd's dependency) on the current tree: bbolt translated by Goose with bodies, building with the
rest. No bbolt proof is started here. The old attempt is `old/bbolt/` (`old/bbolt/README.md`);
section 3 says what of it carries over.

## 1. What is translated

**Project `bbolt`** (`etc/goose.py`): the fork `upamanyus/bbolt`, branch `goose-lean`
(`3207bacf`). That is v1.5.0 (`e7a8b2d`) plus:
- the `goose` branch (`e353cbe`), whose forms Perennial's byte memory follows. Its `unsafe` helpers
  are `unsafe.Add`/`unsafe.Slice` with no `uintptr`, and its six whole-struct copies go through a
  local (Perennial `docs/design/unsafe-memory.md`, section 6);
- the fix of etcd-io/bbolt#1311 (`issues/bbolt-commit-meta-error-frees-reader-pages.md`);
- a crash-safe `init`, and `Open` re-initializing after an interrupted one
  (`nonissues/bbolt-init-not-crash-safe.md`);
- a named type for `DB.ops` and no `retry:` label (the two goose blockers).

Packages `go.etcd.io/bbolt`, `errors`, `internal/common` and `internal/freelist` are all
translated with bodies (`translate = ["*"]`, `Code/go_etcd_io/bbolt{,/errors,/internal/*}.toml`),
with two exceptions in the root package: the type `Options` stays axiomatized, and so does
`DefaultOptions`' initializer (`translate = ["*", "!Options", "!DefaultOptions"]`). The backend's
constructor and every example's `newBackend` go through `Options` by trust-boundary axioms over an
abstract value (`storage/backend/BboltOptions.lean`: `optsAt`, `wp_optsLit`, ...). A translated
struct makes `wp_auto` run the literal itself, which bypasses those axioms. Translating `Options`
belongs with `Open`'s proof, when those axioms become lemmas.
The etcd project no longer translates bbolt. Its lean root `go.etcd.io/bbolt=` stays, so that the
backend names the same modules.

**Since 2026-11-03 (second step) the fork is at branch `goose-lean-v2` (`b30879b2`)**, which adds
two commits on `goose-lean`:
- `7c837ad` (D18): `getPageSize` returns a meta page's read error. Before, it went on probing
  page 1's offsets, which could take the page size from user data that happens to hold a valid
  meta. Adapted from the spec work's `getpagesize.diff`; it applied as is.
- `b30879b` (D17): `splitTwo`'s float threshold is factored out, unchanged, as
  `splitThreshold(pageSize uintptr, fillPercent float64) int`. It is listed `trusted`, and its
  model in `TrustedCode/go_etcd_io/bbolt.lean` returns an arbitrary `int`, continuing only if
  `splitThresholdOk` holds (a NaN fill, or `pageSize ≥ 2^53`, or else `0 ≤ t ≤ pageSize`) and
  diverging otherwise. The model's docstring argues faithfulness.
- `rebalance`'s own float threshold is left translated, so it is arbitrary. This is harmless:
  its early return also needs `len(n.inodes) > n.minKeys()`, so empty nodes and one-child
  branches are always rebalanced, and a different threshold only changes how much is merged,
  which `spill` re-splits.

Three more commits followed (head `b3e06648`):
- `e1fae5c`: `Tx.WriteTo` writes the current meta at page `txid%2`. This is a real bug: after
  restoring a copy whose txid is odd, two torn meta writes leave no valid meta, and the rollback
  panics. The fork adds the regression test `TestWriteTo_OddTxid_TornMetaWrites`, which fails
  before the fix.
- `27b1412`: logger calls format errors with `%v`, not `%w` (upstream main's change).
- `b3e06648`: the default logger is a no-op `nopLogger`. `discardLogger`'s initializer is now a
  literal, so bbolt's package initialization no longer needs `log.NewModel`.

bbolt's tests (`go test -short`) pass on the fork. `examples/go.mod` replaces `go.etcd.io/bbolt`
by the fork at the pin, and `GO_MOD_PINS` checks it. `internal/common`'s package fact is now
`bboltCommonInit`: `DefaultPageSize ↦□ 4096`. The package's other names are constants that the
translation unfolds; `IgnoreNoSync` folds to `false`. The root package still reads
`runtime.GOOS`, an opaque value, in 13 places: those branches need a `GOOS = "linux"` premise
when proved.

**Goose reports nothing it cannot translate**, with Perennial `b3e996d84`. Nothing of bbolt is
`trusted`, and there is no `TrustedCode/go_etcd_io/bbolt`. The only axioms are goose's, for the two
names left out (`Options`' generated instances are `sorry -- axiomatized type`, as before; no
result used them then. Since the proof was linked (2026-11-05) the public results reach
`Options_typed_pointsto`/`Options_into_val_typed`: the D13 option axioms of
`Proof/go_etcd_io/bbolt/Options.lean` speak of `Options` values, as `reflect.Type'`'s instance is
reached elsewhere; recorded in `etc/tcb-baseline.txt`).

**The pin bump to Perennial `b3e996d84`** (origin/lean; it was `c4a24e323`) was necessary.
`c4a24e323`'s goose crashes on bbolt: it emits a nil `BinaryExpr` for `x++` on a `uint16`.
`c3c7ea790` fixes that. The byte-level unsafe model was already in `c4a24e323`. The bump also
brings:
- the monotone package-initialization map (`wp_PackageInitStart` needs the package uninitialized);
- `context`'s `isCtxErr`;
- `os`'s translated initializers, which this repository no longer uses (see below).

**The OS layer: every project now uses this repository's `os`** (`os=`, `io/fs=` in the lean
roots of raft, etcd, bbolt, raft-witness, k8s-apiserver and k8s-daemonset). Those are the
translations of project bboltfs: `Code/os.lean` and `Code/io/fs.lean`, whose trusted functions are
modeled by the Linux file extension osFsExt (`notes/osfs-ext-plan.md`). The reason is that
Perennial's `os` is names-only and declares `FileMode` and `FileInfo` as opaque `axiom … :
go.GoType`, with no `io/fs`. bbolt's `DB` struct has a field `openFile func(string, int,
os.FileMode)`, and `Open`, `fileSize`, `getPageSizeFromSecondMeta`, `WriteTo`, `CopyFile`,
`sameFile` and `Options` name `os.FileMode.ty`, `os.FileInfo.ty` or `io.fs.FileInfo.ty`. None of
these exist under Perennial's `os`, and no partial `translate` list can avoid `DB`.
`osfs-ext-plan.md` had this migration as "the step after". The translations of the other projects
change only in their `os` import (`Perennial.Code.os` becomes `Code.os`). Lean refuses a closure
holding both modules, which is why it had to be every project at once.

**`syscall`, `golang.org/x/sys/unix`** are bboltfs's too, with `Fdatasync`, `Flock`, `Mmap`,
`Munmap` and `Madvise` modeled. `hash`, `hash/fnv` and `encoding/hex` are the etcd project's
names-only translations.

### Package initialization (`etc/gen-init.py`)

bbolt's initializers now run translated code, so its `Init.lean` files are generated with
`SPECIAL` entries:
- `errors`: twenty `errors.New` calls, through Perennial's `context.wp_New_errorString`. This
  replaces the trust-boundary axiom `errorsNewVarsInit`.
- `internal/common`: `DefaultPageSize = os.Getpagesize()`. A new trust-boundary axiom
  `os.Getpagesize.wp_proof` (`Spec/os/Getpagesize.lean`) says it returns 4096, linux/amd64.
- the root package:
  - `trySolo` (an `errors.New` call);
  - `DefaultOptions`;
  - the deprecated aliases, which load `errors`' variables, so `errors`' fact now holds them all
    (`bboltErrorsVars`);
  - `discardLogger` (since the fork's `b3e06648`, a `nopLogger` literal; before, `log.New`,
    through the class `log.NewModel`, now in `Proof/log/NewModel.lean` for raft).
- `os`: its `wp_initialize'` is now generated (`Proof/os/Init.lean`) with the same three kinds of
  trust-boundary axioms raft's `Init.lean` had (`opaqueInitsOk`, `Stderr_init`, `initFuncsOk`),
  over bboltfs's `os`. `syscall`, `io/fs` and `golang.org/x/sys/unix` get generated `Init.lean`s
  (opaque initializers).

**Moved instances.** `IsPkgInit` must have one instance per package, and bbolt must not import
raft, mvcc, k8s or the backend for one:
- `Proof/os/PkgInit.lean`: `os`'s (from raft's `Base.lean`) and `io/fs`'s;
- `Proof/reflect/PkgInit.lean`: `reflect`'s (from raft's and txn's `Base.lean`);
- `Proof/hash/PkgInit.lean`: `hash`'s and `hash/fnv`'s (from mvcc's and kubernetes' `Base.lean`);
- `Proof/syscall/PkgInit.lean`, `Proof/golang_org/x/sys/unix/PkgInit.lean`: new;
- `Proof/go_etcd_io/bbolt/PkgInit.lean`: every bbolt package's, with `bboltErrorsInit`, and
  `encoding/hex`'s (from the backend's `Base.lean` and `internal/common/Init.lean`).

`gen-init.py` prefers this repository's translation of a package over Perennial's (`inventory`).

### The backend

The 20 bbolt axioms (`Spec/go_etcd_io/bbolt/*_kv.lean`) and the `BboltOptions.lean` axioms are
unchanged (`Options` is kept axiomatized for them, above). `batchTx.UnsafeDeleteBucket`'s proof
takes one more component of `bboltErrorsInit`.

### Repairs the bump and the `os` move needed

- **Context's `Err()`** now also gives `isCtxErr err` (Go's contract: `Canceled` or
  `DeadlineExceeded`). About 40 call sites of `HErr`/`HErrDone` take one more `-` in their
  `wp_apply … as` pattern (cache, client, leasing, v3rpc, mvcc, rafthttp, porcupine, kvdurable,
  kvreconf). `schedule.WithCancel` passes `isCtxErr_of_Canceled` to `cancel`.
- **`context.wp_New_errorString`** now persists the `s` cell, so its post changed. The generated
  initializers, and raft's `Init.lean`, use `errors.wp_New_errorString` instead, which has the old
  post and needs only `errors.Assumptions`.
- **`runtime`** (`GOOS`/`GOARCH`, which bbolt imports) and `internal/runtime/{atomic,sys}` get
  their `wp_initialize'` here (`PERENNIAL_HERE`), with opaque-initializer axioms, since Perennial
  proves none of them.
- `unsafe` is a Lean keyword: `ExternalInit.unsafe_`, module `Perennial.Code.«unsafe»`.
- `osFsExt`'s `inRange` is now in scope everywhere: authkv's `Model.lean` writes `auth.inRange`.
- kvwitness's hand-written package table gains `io/fs` and `syscall`, which are now `os`'s imports.
- `RaftWitness/` gets its copies of `os`'s, `syscall`'s and `io/fs`'s `Init.lean` (`PART_INITS`).

### Trust base (`etc/tcb-report.py --check`, baseline updated)

New:
- `os.Getpagesize.wp_proof` (4096);
- the opaque-initializer axioms of the packages whose `wp_initialize'` is now generated:
  `syscall`, `golang.org/x/sys/unix`, `io/fs`, `runtime`, `internal/runtime/sys`
  (`opaqueInitsOk`, `initFuncsOk`).

Gone:
- `bbolt.errors.errorsNewVarsInit` (its `errors.New`s are translated and proved);
- `bbolt.internal.common.opaqueInitsOk`.

`os`'s three axioms keep their names, now in the generated `Proof/os/Init.lean`.

## 2. What bbolt calls, and what models it

| Callee | Model | Spec |
|---|---|---|
| `unsafe.Pointer` casts, `Add`, `Slice` | Perennial semantics (byte memory: R1–R3 of `unsafe-memory.md`; `Add`/`Slice` pure arithmetic, out-of-allocation pointers not checked, `KNOWN_LIMITATIONS.md`) | `Perennial/Golang/Theory/Unsafe.lean` (`ByteEncoding`, `BytesView`, views of byte slices); worked proofs of bbolt-shaped code in Perennial's `Proof/.../unsafememory/` |
| `unsafe.Sizeof`/`Offsetof`/`Alignof` | constants folded by goose (amd64) | — |
| `os.OpenFile`, `File.{ReadAt,WriteAt,Stat,Truncate,Sync,Close,Fd}` | this repository's `TrustedCode/os.lean` over osFsExt | `Spec/os/*` (proved; crash-aware variants in `Proof/os/Crash*.lean`) |
| `File.Name`, `fileStat.Size` | translated (bboltfs) | `Spec/os/File__Name.lean`, `fileStat__Size.lean` |
| `os.Getenv` | names only | axiom `Spec/os/Getenv.lean` |
| `os.Getpagesize` | names only | axiom `Spec/os/Getpagesize.lean` (new: 4096) |
| `os.Setenv`, `Unsetenv`, `Exit`, `Create`, `Open`, `Stat`, `IsNotExist`, `SameFile`, `Stderr` | names only | none (`Stderr`: the package fact) |
| `syscall.Flock`, `Fdatasync` | `TrustedCode/syscall.lean` (osFsExt) | `Spec/syscall/*` (proved) |
| `unix.Mmap`, `Munmap`, `Madvise` | `TrustedCode/golang_org/x/sys/unix.lean` (osFsExt; read-only shared maps) | `Spec/golang_org/x/sys/unix/*` (proved) |
| `unix.Mlock`, `Munlock` | names only | none |
| `sync.Mutex`, `RWMutex`, `Once` | Perennial (trusted / translated) | Perennial `Spec/sync/*` (proved) |
| `sync.Pool` `Get`/`Put` | Perennial trusted | Perennial `Spec/sync/Pool__{Get,Put}.lean` (proved) |
| `atomic.AddInt64`, `LoadInt64` | Perennial trusted | Perennial `Spec/sync/atomic/*` (proved) |
| `sort.Search`, `sort.Sort` | Perennial translated | Perennial `Spec/sort/{Search,Sort}.lean` (proved) |
| `sort.SliceIsSorted` | names only | none |
| `bytes.Compare`, `Equal` | Perennial | Perennial `Spec/bytes/*` (proved) |
| `fnv.New64a`, `Hash64.Write`/`Sum64` | names only (etcd project) | none (the unsafememory example's `Meta.lean` models FNV-64a in Lean) |
| `hex.EncodeToString` | names only | none |
| `time.Now`, `Since`, `Sleep`, `AfterFunc`, `Timer.Stop` | Perennial | `Now`, `Timer.Stop` axioms; `Since`, `Sleep`, `AfterFunc` proved |
| `log.New` | names only | the class `log.NewModel` (`Proof/log/NewModel.lean`) |
| `log.Logger` methods | names only, but `Printf`, `Println` trusted | `Printf` proved; no others |
| `fmt.Sprintf`, `Errorf` | Perennial trusted | proved |
| `fmt.Fprintf`, `Sprint` | names only | none |
| `errors.New`, `Is` | Perennial | proved |
| `strings.Join` | trusted | proved |
| `strings.ToLower` | names only | none |
| `io.Copy`, `CopyN`, `NewSectionReader` (`WriteTo`, `CopyFile`) | names only | none |
| `reflect.DeepEqual` (freelist checks) | names only | none |
| `runtime.GOOS`/`GOARCH` | constants (goose) | — |

## 3. Reuse of `old/bbolt/`

`old/bbolt/` holds 982 files and 114k lines: 382 Spec files and 600 Proof files. "Template" below
means that the unsafememory example (Perennial's
`Proof/github_com/mit_pdos/perennial/goose/testdata/examples/unsafememory/`, `UM/`) proves the
same shape over a bbolt-like copy of the code: the proof against the fork is modelled on it, not
taken from it. `MB/` is minibolt's proofs (`Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/`).

| Group | Files | Class | Replacement / note |
|---|---|---|---|
| Pgids/Pages sort and merge | `internal/common/{Pgids,Pages}__*` (14) | portable | partly already here: `Proof/go_etcd_io/bbolt/internal/common/{Mergepgids,Model,SliceLemmas}` |
| verification flags | `internal/common/{Assert,*Verification*,Verify,getEnvVerify}` (14) | portable | needs `os.Setenv`/`Unsetenv` axioms |
| unsafe primitives, byte view, page loads | `internal/common/{Bytes,UnsafeAdd,UnsafeIndex,UnsafeByteSlice,Load*,New*}` (19) | superseded (Perennial) | `Theory/Unsafe.lean`; `UM/{Layout,unsafeAdd,unsafeIndex,unsafeByteSlice,pageAt}` |
| offset accessors, meta checksum/validate/write/copy | `Page__{Meta,…Element(s),FreelistPage*,…}`, `*Element__{Key,Value}`, `Meta__{Sum64,Validate,Write,Copy}` (36) | superseded (template) | `UM/{Page__*,leafPageElement__*,branchPageElement__key,Meta__*,openInlineBucket}` |
| plain field accessors | the other `internal/common/{Page,Meta,InBucket,*PageElement}__*` (114) | portable | statements hold over `BytesView`; proofs redone |
| inodes ↔ page | `Inode__*`, `ReadInodeFromPage`, `WriteInodeToPage`, `UsedSpaceInPage` (25) | split | getters portable; read/write: template `UM/{readInodeFromPage,writeInodeToPage,leafInodes,writeLeaf}` |
| freelist model, interface, array, shared | `internal/freelist/{Model,Iface,ArrayIface,Array*,Lemmas,…,shared__*}` (54) | portable | — |
| hashMap freelist | `hashMap__*`, `Hash*` (32) | portable | — |
| freelist page I/O | `shared__{Read,Write,Reload,NoSyncReload,EstimatedWritePageSize}` (10) | split | page part: template `UM/Freelist`, `testFreelist{Overflow,RoundTrip}` |
| link/results files | `{Init,Link,Results}` of each package (8) | obsolete | regenerate |
| lemma libraries | `Words`, `SliceWithin`, `StructSplit`, `Records`, `ErrShape` (5) | portable | — |
| float conversions | `FloatConv` | superseded (Perennial) | `Golang/Defn/Predeclared.lean` `Float64Semantics` |
| page model | `PageModel`, `PageView` | split | well-formedness portable; decoding: `Theory/Unsafe.lean`, `UM/{Layout,Pages,pageBytes}` |
| stats, accessors, logger | `TxStats__*`, `DB__{Path,Info,Stats,…}`, `Tx__{DB,ID,Size,…}`, `DefaultLogger__*`, … (137) | portable | the atomics: `UM/testStatsConcurrent` |
| cursor (read path) | `Cursor__*`, `elemRef__*`, `Cursor*`, `KeyOrder`, `PathFlags` (73) | portable | re-base the page view on the new ownership |
| bucket read API | `Bucket__{Get,ForEach*,Bucket,openBucket,…}`, `Bucket*`, `Tx__{Bucket,ForEach,Cursor}` (37) | portable | inline-bucket copy: template `UM/openInlineBucket` |
| writer bucket ops, tx shape | `Bucket__{Put,Delete,CreateBucket*,…}`, `Write*`, `Shape*` (71) | portable | — |
| node | `node__*`, `nodes__*`, `Node*` (51) | portable | `sort.Sort`: Perennial's spec |
| rebalance | `Rebalance*`, `*__rebalance_s` (17) | portable | — |
| spill, split, free | `Spill*`, `node__{spill,split*,free*}`, … (58, 25k lines) | portable | never built (saved WIP of 2026-10-19) |
| allocation | `Tx__allocate*`, `DB__allocate`, `*Alloc*` (9) | portable | the pool: Perennial `Spec/sync/Pool__*` |
| commit, file side | `Tx__{write,writeMeta,commitFreelist}`, `CommitFL`, `WrittenPage`, `DBWrite` (10) | obsolete (ownership) | osFs `Spec/os/File__WriteAt`, `Spec/syscall/Fdatasync`; template `MB/{DB__commit,DB__commitCrash}` |
| database predicate, tx lifecycle | `DBPred`, `DBModel`, `TxModel`, `DB*`, `Tree*`, `FilePages`, `SlotsCarve`, `DB__{Begin,…}`, `Tx__{Rollback*,…}` (55) | split | tree/MVCC logic portable; the slot-fraction layer obsolete: mapping ownership as `MB/{MapInv,MapLoan,MapCells,DB}` over osFs |
| open, mmap, file | `Open`, `DB__{Close,init,mmap,munmap,grow,…}`, `flock`, `DBOpen*`, `DBRemap`, `DBClose` (40) | superseded (osFs) | `MB/{Open,DB__init,DB__mmap,DB__munmap,DB__close,flock,…}`; `Spec/os/OpenFile`, `Spec/syscall/Flock`, `Spec/golang_org/x/sys/unix/Mmap` |
| page size, mmap size, meta bytes | `DB__{getPageSize*,mmapSize,growSize}`, `MetaInj`, `MetaBuf`, `U64Bytes`, `FLPage` (15) | portable | re-base `U64Bytes`/`FLPage` on `ByteEncoding`; related: `MB/{readPageSize,mmapSize,pickMeta}` |
| old file model | `Proof/os/{FileModel,FileLemmas,ErrWF,FileInfoAlias}` | obsolete | osFsExt (`GooseLang/Ext/OsFs/`), `Proof/os/Base.lean` |
| old os/syscall/unix axioms | `{Spec,Proof}/{os,syscall,golang_org/x/sys/unix,io/fs}/*` (32) | superseded (osFs) | `Spec/os/File__*`, `OpenFile`, `Getenv`, `fileStat__Size`, `Spec/syscall/*`, `Spec/golang_org/x/sys/unix/*` (proved) |
| os env/exit axioms | `os/{Setenv,Unsetenv,Exit}` | portable as axioms | nothing yet |
| sort | `sort/{Sort,Sort_w,SliceIsSorted}` | `Sort` superseded; `SliceIsSorted` portable as an axiom | Perennial `Spec/sort/Sort.lean` |
| sync | `sync/{Pool__Get,Pool__Put,PoolModel,OnceFresh}` | superseded (Perennial) | Perennial `Spec/sync/{Pool__*,Once__Do}`, `Proof/sync/{PoolDefs,OnceDefs}` |
| log, fmt.Sprint, strings.ToLower, reflect.DeepEqual, fnv, runtime.GOOS | axioms and assumption classes | portable as axioms | nothing yet in Perennial |

The old model axioms (`bbolt.fsFile`, `osFile`, `fileBytes`, `fileMap`, `filePath`, `fileInfo`)
and the old per-call axioms (`bbolt.os.File.*`, `bbolt.syscall.*`, `bbolt.unix.{Mmap,Munmap,Madvise}`)
are replaced by osFsExt and its proved specs, and `isPool` is replaced by Perennial's
`sync.Pool`. These have no replacement yet: `fnvHash` with the `fnv` calls, `isLog` with
`log.Logger.Output`, `strings.ToLower`, `os.Setenv`/`Unsetenv`/`Exit`, `sort.SliceIsSorted`,
`reflect.DeepEqual`, `fmt.Sprint`, `GOOSLinux`.

## 4. Open

- **Which calls the first proofs need.** The `os` migration puts every OS call bbolt makes on
  osFsExt's models: `OpenFile`, `ReadAt`, `WriteAt`, `Stat`, `Truncate`, `Sync`, `Fdatasync`,
  `Flock`, `Mmap`, `Munmap` and `Madvise`. Each already has a proved spec, as minibolt uses them.
- **The `examples/` Go module still builds against bbolt v1.5.0,** not the fork. A `replace`
  with a `GO_MOD_PINS` entry, as for raft, would align the examples with the verified code.
- **A Perennial change to propose,** independent of this one: translate `io/fs`'s types and `os`'s
  aliases of them, so that Perennial's own `os` can name `FileMode`/`FileInfo`.

## 5. The proof's infrastructure items (2026-11-04)

Done on this branch, one commit each (the coordinator's list; `notes/bbolt-proof-plan.md` §5):

- **`runtime.GOOS`/`GOARCH`** (items 1, 1b): trust-boundary axioms `runtime.GOOS_linux` and
  `runtime.GOARCH_amd64` in the generated `Proof/runtime/Init.lean` (`etc/gen-init.py`
  `SPECIAL['runtime']`). `runtime`'s `IsPkgInit` instance is Perennial's (fact `True`), so the facts
  surface through bbolt's root package fact `bboltRootInit` (`PkgInit.lean`;
  `bboltRootInit_goos`/`_goarch`; `Mmap/Infra`'s `goosLinux_of_pkgInit`/`goarchAmd64_of_pkgInit`).
- **Errors `fmt` formats** (item 2): `syscall.Errno.Error` trusted (some string),
  `io/fs.PathError.Error` translated; `errnoErr_fmtErrorOk`, `pathError_fmtErrorOk`,
  `wp_wrapErrno_ok`; the `os.File.{Stat,Truncate,Sync,ReadAt,WriteAt}` posts end with
  `fmtErrorOkOrNil err`; `fmt.Errorf.spec`'s post (an axiom) has the method-set fact
  (`fmtErrorOk_of_errorf`). `Mmap/Infra`'s `errnoErrOk` is proved (`errnoErrOk_holds`).
- **`os.Getenv`** (item 4): its axiom for any `hlc`. `common.Verify` still a stub:
  `strings.ToLower` has no spec (`notes/perennial-changes.md`).
- **FNV-1a 64** (items 5a, 5b): `hash/fnv`'s `New64a`/`Write`/`Sum64` with bodies and proved specs;
  `Model/Meta`'s `fnv64a` is the real hash; `Meta.Sum64` proved.
- **`os.File.WriteAt` at any length** (item 3): the premise is `off + len < 2^63` (was 1 GiB), proved over the model's chunk loop (`Proof/os/WriteChunks.lean`, `pwBytes_chunk`); `Spec/os/Crash*` keep the old bound.
- **The fork's `Open` commit** (item 6): `743299d8` on `goose-lean-v2`, the pin moved.
- **`delete` on `pidSet`** (item 7): Perennial branch `delete-map-named`, not landed (a trusted
  semantics change needs the user's sign-off); `PidSetDeleteUnfold` stays.
