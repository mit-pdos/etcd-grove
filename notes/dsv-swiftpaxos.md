# dsv-swiftpaxos: dsverify-lab's swiftpaxos kit on the net extension (phase 6)

Branch `dsv-swiftpaxos` (2026-11-23, off `origin/dsv-paxos` `e3eaf5cd0d`), worktree
`/shared/etcd-grove-dsvswiftpaxos`. Plan: `notes/dsverify-net-port-plan.md`, phase 6; pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/swiftpaxos/` (read only):
run **`swift-n2nofast-1`**, proof `2cbd46c` (tag `final`), fork `66dfc21`, Perennial `3afd77e35`;
the lab's statement `dsv_goal_check : SafeDistSha (orchNode :: clientNodes ++ serverNodes)
swiftNetCfg`, axioms Lean's three and porcupine's `CheckOperations.wp_proof`.

**State: BLOCKED** on model pieces this branch may not add (`Net/`, `models/`, the main tree's
standard-library translations are out of scope for a kit port; below). Nothing is translated or
proved yet. What is here is the Go half's first step.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/swiftpaxos/` (module `github.com/imdea-software/swiftpaxos`, the fork's path): the fork's system packages at `66dfc21` unchanged (`client`, `config`, `dlog`, `hook`, `master`, `replica`, `replica/defs`, `rpc`, `state`, `swift`), over the **real** `gods` v1.18.1, `uuid` v1.3.1, `concurrent-map` v1.0.0 (the lab replaced these by its own models, `harness/rpcmodel/{gods,uuid,cmap}`). `go build`, `go vet` (one unkeyed-literal warning, upstream's), `go test ./...` pass (2026-11-23). Not copied: the kit `examples/swiftnet` and `cmd/dsrig` (they import the lab harness: `remote`, `rigenv`, `models`; to be ported onto `examples/lib/remote`), and the fork's other protocols (`curp`, `fastpaxos`, `n2paxos`, `paxos`, the top-level `main`/`run`) |
| translation | none yet (no `etc/goose.py` project) |
| proofs, statement, TCB collection | none yet |

## What blocks (the pieces the lab's proof uses that this repository does not have)

The lab's proof (486 files, 143k lines under `proof/{Spec,Proof}`) rests on its own `Harness/`
translations and proofs of these; the port must put each onto this repository's model, and these
models are missing or unproved here (checked against `origin/lean` `2dce8dc601`):

1. **net/rpc, the server side and the HTTP path** (`models/net/rpc`, `Net/Spec/net/rpc/`): the kit's
   master and every replica serve RPC (`rpc.Register`, `rpc.HandleHTTP`, `http.Serve(l, nil)`:
   `kit.go:476-480`, `master/master.go:62-82`) and dial it (`rpc.DialHTTP`: `kit.go:302,434`,
   `master.go:99`, `client/client.go:325`), then `Client.Call`. `origin/lean` proves the client only
   (`Client.{Call,Go,Close,send,input}`, `NewClient(WithCodec)`, `Dial`). Not stated: `DialHTTP`/
   `DialHTTPPath`, `Server.Register(Name)`/`Register`, the server codec's methods, `ServeConn`/
   `ServeCodec`/`ServeRequest`, `ServeHTTP`, `HandleHTTP`, the generated `Codec`'s `Receiver` laws,
   and `net/rpc`'s `isPkgInit` (plan, phase 5.2 "What remains", items 1, 2 (`Receiver`), 4, 5, 6).
   The lab used: `net.rpc.{Register,HandleHTTP,SetCodec,DialHTTP,Client.Call,Client.Close}`.
2. **net/http's server** (`Net/Code/net/http.lean`, no spec): `http.Serve` / `Server.Serve` /
   `conn.serve` up to the hijack, `ServeMux` exact-path dispatch, `ReadResponse` on the CONNECT
   answer (plan, phase 5.2 item 7; the largest item). The lab used `net.http.Serve.wp_proof`.
3. **encoding/gob, used directly** (no model at all in `models/`; the plan's phase 5 says "gob:
   names-only plus the generated codec, net/rpc's only user", which is not so for swiftpaxos):
   `swift/defs.go:417-428`, `MSync.Marshal`/`Unmarshal` (`gob.NewEncoder(w).Encode(m)`,
   `gob.NewDecoder(r).Decode(m)`) on the replicas' wire (sync/recovery). The lab had a gob model
   (`harness/rpcmodel/src/encoding/gob`, the copy kept at `old/dsverify/harness/rpcmodel/src/encoding/gob/gob.go`)
   registered by the kit (`gob.SetCodec`, `rpc_model_gen.go`), with specs `encoding.gob.{NewEncoder,
   NewDecoder,Encoder.Encode,Encoder.EncodeW,Decoder.Decode,SetCodec,getCodec}` (lab
   `proof/Proof/gob/`). Needed: a model `models/encoding/gob` (a standard-library model at its
   import path, as `encoding/json`), its generator input (rpcgen's encoding of `MSync`), its
   difftest, and specs over a `bufio`/`io.Writer`/`io.Reader` stream. (Alternative, the user's/
   coordinator's call: change the fork so `MSync` uses the fastrpc marshalling of every other
   message; that changes verified Go code.)
4. **bufio with bodies and specs** (main tree `Code/bufio.lean`: names only but `NewReader`,
   `NewReaderSize`, `Reader.Read` and helpers, for the WAL): the replicas' transport and the client
   use `bufio.NewReader`/`NewWriter`/`NewWriterSize`, `Reader.ReadByte`, `Reader.ReadString`,
   `io.ReadFull`/`ReadAtLeast` over a `*bufio.Reader`, `Writer.{Write,WriteByte,WriteString,Flush}`,
   over a `net.Conn`. The lab had its own bufio translation and proofs (`proof/Harness/Proof/bufio/`:
   `Reader`, `Writer`, `ReadFull`, `Net`: the reader/writer over the network connection). The main
   tree's `Code/bufio.toml` is shared (rabia, epaxos and gryff, siblings of this port, need the same):
   widening it and proving `Writer`/`ReadByte` over `Net/`'s `Conn` is one shared change, not a kit's.
5. **Models of third-party modules the lab replaced** (`harness/rpcmodel/{gods,uuid,cmap}`: subsets of
   `github.com/emirpasic/gods` v1.18.1 `maps/treemap`+`utils`, `github.com/google/uuid` v1.3.1,
   `github.com/orcaman/concurrent-map` v1.0.0, each the library's code cut to what swiftpaxos calls):
   the translation needs translatable code for these; in this repository a model of a library goes
   to `models/` (trusted, with differential tests), which a kit port does not change. (gods and
   concurrent-map might instead translate from the real modules with a goose configuration listing
   the functions swiftpaxos calls, in the part, if goose takes them; not tried.)

Probably available, to check when unblocked: `log.Logger.{Printf,Println,Fatal}` (Perennial's `log`;
the lab's specs are `log.Logger.*.spec`, and `dlog`'s `HashLog`), `math/rand.{New,NewSource,Intn}`
(Perennial's `math/rand`; main tree specs only `Float64`/`Int63n`), `crypto/sha256` (Perennial's
extension, as in the lab since stage 3), `sync.Pool`, `sync.Cond`, `os/signal.Notify`
(`client`), `slices.SortFunc` (the lab proved pdqsort: `proof/Proof/slices/SortFuncOn/`).

## Next steps (once 1-5 are decided)

1. Port the kit (`examples/swiftnet`, `cmd/dsrig`) onto `examples/lib/remote` as `dsv-paxos` did:
   orchestrator + each client a machine of its own (the lab's run already has clients on nodes of their
   own, through its own `Remote`), `remote.Check` with the kit's porcupine model (the lab's KV model,
   `harness/models` `KvIn`/`KvOut`) in place of the lab's recorder/checker; regenerate `rpc_gen.go`
   with this repository's `models/net/rpc/rpcgen.py` (the lab's codec has `Methods`/`Call`/`Name`;
   ours has the `Receiver`).
2. `etc/goose.py` project `dsv-swiftpaxos` into `Dsverify/` (`std_models` for `net/rpc`, `net/http`
   and gob), `etc/gen-init.py` `dsv_inits` entries.
3. Port the proof by editing (`proof/{Spec,Proof}`, 143k lines): the transport onto `Net/Spec/net/*` and
   `Proto.lean`'s laws, the RPC control plane onto `Net/Spec/net/rpc/*`, the statement
   `swiftpaxos_remote_robust` (`DistDeploy … → Robust [] …`), `etc/tcb-collections/dsv-swiftpaxos.txt`.
