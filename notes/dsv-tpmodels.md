# dsv-tpmodels: models of the third-party Go modules the dsverify kits use (#24)

Branch `dsv-tpmodels` (2026-11-23, off `origin/lean` `2dce8dc601`), worktree `/shared/etcd-grove-dsvtp`,
agent of the dsverify-lab session (account kaashoek). Agreed on mit-pdos/etcd-grove#24 (Upamanyu,
owner of `models/`): gods treemap, google/uuid, orcaman/concurrent-map in `models/` under
`models/README.md`'s rules; he reviews each before it lands. **Not landed; pushed for review.**

## What is here

| model | module (version) | API kept | kits |
|---|---|---|---|
| `models/gods/` | `github.com/emirpasic/gods` v1.18.1: `maps/treemap`, `utils` | `utils.Comparator`; `treemap.NewWith`, `Map.{Put,Get,Select,Iterator}`, `Iterator.{Next,Value}` | swiftpaxos, epaxos (SwiftPaxos's `state`) |
| `models/uuid/` | `github.com/google/uuid` v1.3.1 | `UUID`, `Time`, `New`, `NewRandom`, `Must`, `UUID.{ID,Time}` | swiftpaxos (`client`) |
| `models/concurrent-map/` | `github.com/orcaman/concurrent-map` v1.0.0 | `SHARD_COUNT`, `ConcurrentMap(Shared)`, `New`, `GetShard`, `Set`, `Upsert`/`UpsertCb`, `Get`, `Has`, `Remove`, `IterCb`/`IterCb`, `Count`, `IsEmpty` (tests) | swiftpaxos (`swift`) |
| `models/log/slog/` (std model, `goroot.py`) | Go 1.27.3 `log/slog` | `Level` + 4 constants, `Handler`, `Record`/`Attr` (opaque), `DiscardHandler`, `Logger`, `New`, `Logger.{Debug,Info,Warn,Error,Handler}`, `Debug` | vr (go-vsr `replica`, `client`, `network`, `examples/vsrnet`); no other kit uses slog (rabia uses zerolog) |

log/slog was added at the coordinator's request (Upamanyu's approval on #24, comment 7089888907):
claim "no effect the program observes", only for DiscardHandler and the default handler (stderr);
a program-supplied Handler and the use of `Logger.Handler()`'s result panic `NotModelled`. Evidence
`models/internal/slogdifftest/run.sh` (overlay; transcripts of returns/panics incl. a nil Logger and
`New(nil)`; no argument method called; a child process writes nothing). go-vsr's tests
(`/shared/etcd-grove-dsvvr/examples/dsverify/vr`) pass against it; goose translates it (farm) with
its bodies.

- Each is a module model as `models/grpc` is: the module's path and layout, its source at the pinned
  version, cut to the kits' API, changes marked `MODEL:`, the trusted claim in the package doc;
  `models/diff.py gods|uuid|concurrent-map` (MODULE_MODELS entries added) computes the difference.
- Evidence: `models/internal/tpdifftest/run.sh` (added to `etc/gates.sh`'s models section): one test
  module built against the real modules and against the models (-modfile, tag `tpmodel`), each
  build checked against the tests' references, the two builds' transcripts equal byte for byte.
  Mutations tried by hand (Put not replacing an equal key's key; Put on an empty map not calling
  `comparator(k, k)`) are caught.
- epaxos (coordinator's note: gods' red-black iterator uses `goto`, which goose refuses): the
  model has no `goto`, covers epaxos's `state` API (the same as swiftpaxos's: `NewWith`, `Put`,
  `Get`, `Select`, `Iterator`, `Next`, `Value`; the restored `epaxos` package does not use gods),
  and epaxos's tests (`/shared/etcd-grove-dsvepaxos/examples/dsverify/epaxos`: `epaxos`,
  `examples/epaxosnet`, `master`, `replica`, `state`) pass against it.
- SwiftPaxos's own tests (`state`, `swift`, `client` in `/shared/etcd-grove-dsvswiftpaxos/examples/dsverify/swiftpaxos`)
  pass built against the models (a -modfile with the three replaces).
- Goose (Perennial `9c3b81f304`, the pin, goose built in a scratch dir) translates all three packages
  (and proofgen) with no error and no untranslated body. No goose project is added (that would
  write into a part's `Code/`; out of this branch's scope).

## Inventory: the kits' third-party modules (lab `915f964`, `examples/*/fork`)

| module | kits | lab's treatment | here |
|---|---|---|---|
| `github.com/emirpasic/gods` v1.18.1 | swiftpaxos, epaxos | `harness/rpcmodel/gods` (sorted-slice model) | `models/gods` |
| `github.com/google/uuid` v1.3.1 | swiftpaxos | `harness/rpcmodel/uuid` | `models/uuid` |
| `github.com/orcaman/concurrent-map` v1.0.0 | swiftpaxos | `harness/rpcmodel/cmap` | `models/concurrent-map` |
| `github.com/rs/zerolog` v1.23.0 | rabia | `harness/rpcmodel/zerolog` (model, translated) | not done (not in #24's agreement) |
| `github.com/gogo/protobuf` v1.3.2 (`proto`, `gogoproto`) | rabia | `harness/rpcmodel/gogoprotobuf` (names for the generated message.pb.go) | not done; maybe pbgen's territory |
| `github.com/go-redis/redis/v8` | rabia (v8.8.2), quepaxa (v8.11.5) | `harness/rpcmodel/goredis` (stub: Redis modes not configured) | not done |
| `github.com/montanaflynn/stats` v0.6.6 | quepaxa (benchmark client only) | `harness/rpcmodel/stats` (stub, build only) | not needed by a kit |
| `gopkg.in/yaml.v2` v2.3.0 | quepaxa (`configuration`) | translated by the lab (names) | not done |
| `google.golang.org/grpc`, `google.golang.org/protobuf` | quepaxa, rabia (protobuf) | lab models | `models/grpc`, pbgen |
| `github.com/google/go-cmp`, `go.etcd.io/bbolt`, `go.mongodb.org/mongo-driver` | craq (tests / other stores only) | not in the kit | none needed |
| `github.com/goose-lang/primitive`, `github.com/anishathalye/porcupine` | gryff, swiftpaxos / all | Perennial / main tree | as is |
| vr, craq, gryff, paxos | none beyond the above | | |

## What a kit needs to use them (dsv-swiftpaxos, dsv-epaxos)

1. Go builds: the kit's go.mod keeps the real modules (its tests run on them, as now); a model build
   uses a -modfile with `replace github.com/emirpasic/gods => <repo>/models/gods` (and uuid,
   concurrent-map), as `models/grpc/gomodel.py` does for grpc. The uuid model requires
   `github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65` (the kit's go.sum needs its lines;
   `models/uuid/go.sum`).
2. Translation: in the kit's goose project, `module_models={"github.com/emirpasic/gods": "models/gods",
   "github.com/google/uuid": "models/uuid", "github.com/orcaman/concurrent-map": "models/concurrent-map"}`
   and the packages `github.com/emirpasic/gods/utils`, `.../maps/treemap`, `github.com/google/uuid`,
   `github.com/orcaman/concurrent-map` with their lean roots. dsv-swiftpaxos's goose project
   (`3263977fb4`) already translates the real modules "names and types only" into `Dsverify/`; it
   switches to the models by adding `module_models` (and translating with bodies).
   Open: who owns the translation, since swiftpaxos and epaxos both reach gods and `Dsverify/` is one
   part: one kit's project, or a shared project (e.g. into `Net/` beside the other models).
3. Proofs: no spec is proved for any of the three. uuid's `Time` calls `encoding/binary`'s
   `bigEndian.Uint16`, which Perennial translates but has no spec of (it has `Uint32`, `Uint64`,
   `PutUint32`, `PutUint64`); `NewRandom` uses `PutUint64` and `primitive.RandomUint64` (Perennial:
   `ArbitraryInt`).

## Open questions for Upamanyu's review

0. log/slog: the default handler's claim needs the program not to call `log.SetOutput`/`SetFlags`
   (stderr is the unreadable sink); a premise or a doc note? And for records the default handler
   would write (Info and above through a default Logger: not in the model's API), slog would call
   argument methods; the model's API keeps only `Debug` at package level, so this does not arise.

1. Directory names: `models/gods`, `models/uuid`, `models/concurrent-map` (the module's last element,
   as `models/grpc`); or something else?
2. (answered by the review, below: interface-reached methods are kept.)
3. gods: the claim is conditional on the comparator being a total preorder that does not panic on
   two keys of the key type; which comparator calls happen is not claimed (Put on an empty map does
   call `comparator(k, k)`, as gods does). SwiftPaxos's `KeyComparator` (int64 keys) satisfies it.
   Should the condition be a checked premise somewhere (the kit's proof), or is the doc enough?
4. uuid: randomness from `primitive.RandomUint64` instead of crypto/rand (the lab's choice); `ID`/`Time`
   keep the real `encoding/binary` calls (the lab wrote them out). The process's fatal error when
   the kernel's random source fails (crypto/rand since Go 1.24) is excluded from the claim.
5. The evidence compares transcripts across two builds (no golden files stored); the tests also
   check a reference in each build. Is that the form wanted, or golden transcripts as
   `internal/jsonstreamtest`?
6. Translation ownership (above, "What a kit needs", 2).

`notes/STATUS.md` is not updated on this branch (nothing landed); the landing adds the entry.

## Review round 1 (Upamanyu, #24 comment 7090130923) and what changed

The reviewer's reproducers (`/tmp/dsvtp-probe`, `/tmp/dsvtp/models/internal/slogprobe`) are not
visible from this session's machine; each finding is reproduced instead in the difftests below.

1. **Interface-reached methods kept** (the "does not build" argument dropped from README and here):
   uuid `String`, `MarshalText`/`UnmarshalText`, `MarshalBinary`/`UnmarshalBinary`, `Value`/`Scan`
   with `Parse`/`ParseBytes` (v1.3.1's code); treemap `*Map.String` (gods' code),
   `MarshalJSON`/`UnmarshalJSON` (`NotModelled`); `ConcurrentMap.MarshalJSON` (`NotModelled`);
   slog `Level`'s `String`, `MarshalJSON`, `UnmarshalJSON`, `AppendText`, `MarshalText`,
   `UnmarshalText`, `Level` (Go's code).
2. **gods**: `Map{state *sorted}`, `NewWith` allocating (zero/new/nil Map panic with gods' nil
   dereference, copies share the state); comparator premise over every pair incl. a key with itself,
   sign-consistent, transitive; a change counter: Next/Value after a Put on the map (Select's
   predicate included) panic `NotModelled`; no current entry: a nil dereference, gods' text (tested
   exactly: transcripts now record panic texts).
3. **uuid**: premises "never assigns `crypto/rand.Reader`", "not built with boringcrypto"; v4
   coverage stated as structural (`ArbitraryInt`). `testdata/randprobe` (run by run.sh) shows the
   early-init case: v1.3.1's `New` panics, the model's does not (outside the premise).
4. **concurrent-map**: `MarshalJSON` only.
5. **slog**: `Logger.Handler()` is Go's `return l.handler` (notModelledHandler removed); the
   `log.SetOutput/SetFlags` premise replaced by "no record is ever enabled through the model's
   API"; premise: the program makes no `Record`/`Attr` values (opaque in the model).
6. **Evidence**: tpdifftest covers zero, new, nil, copied maps, fmt and JSON of all three types
   (cmap JSON: `NotModelled` in the model, `{"a":1,"b":"x"}` in v1.0.0), uuid text/binary/JSON/gob/
   SQL and parsing of 381 texts, a replaced `crypto/rand.Reader`; slogdifftest covers `Handler()`'s
   identity and type, a zero Logger, `Level` formatting and parsing, a wrapped DiscardHandler
   (`NotModelled`). `tpdifftest/run.sh` fetches the pinned modules when the cache lacks them
   (tried with an empty GOMODCACHE: passes).

Goose (pinned Perennial) still translates all four with bodies, no error. The new methods reference
names a kit's Lean build must have: `database/sql/driver.Value` (no translation in Perennial or the
main tree yet: names only would do, as the kits never call Value/Scan), `encoding/hex.Encode` (main
tree), `bytes.EqualFold`, `fmt.Errorf`/`Sprintf` (Perennial: trusted), `strings.TrimRight`,
`strconv` (slog's Level parsing).
