# The part `KvNet/`: where kvnet's proof lives

Started 2026-11-21 (claim issue #22; `notes/kvnet-proof-plan.md`, decision D2). kvnet
(`examples/raft/kvnet`, a Go module of its own whose `go.mod` replaces raft by `RAFT_NOAX_REV`) needs,
in one import closure:

1. raft-noax's translation, specs and proofs (the part `RaftNoAx/`, itself copied from the main tree);
2. the net extension's bodied `net` (the part `Net/`);
3. the bodied `durable` over the Linux file extension fsExt (the part `WalTester/`);
4. kvnet's and kvcheck's own translations.

Each of 1-3 declares main-tree names (raft's, `net`'s, `durable`'s), so none of them can be imported
beside the main tree's versions or beside each other's copies of shared modules (`os`'s
initializers, `PkgInitExt`). `KvNet/` is a fifth tree holding all of them, made by generators as
`RaftNoAx/` is (`notes/raft-noax-part.md`); nothing outside it imports it.

## How the part is made

1. **Translations** (`etc/goose.py`): project `kvnet` (root `KvNet`, packages `.` and `./kvcheck` of
   `examples/raft/kvnet`, no Goose configuration), and a `Part` into `KvNet` of each project whose
   package it needs: raft-noax (raft's five packages, configured by `KvNet/Code/go_etcd_io/raft/**.toml`),
   net (`net` alone, `KvNet/Code/net.toml`), durable (the bodied translation, as `WalTester/`'s: no
   configuration) and etcd (`walpb`, which raft's `PbSchema` names). kvnet's lean roots send raft,
   `net` and `durable` to `KvNet`, lintest and porcupine to the main tree (`github.com/mit-pdos/etcd-grove=`,
   `github.com/anishathalye/porcupine=`), the file layer (`os`, `path/filepath`, ...) to the main
   tree's, as every project's. Each part translation is its source part's up to the prefix (checked
   2026-11-21: `RaftNoAx.`/`Net.`/`WalTester.` replaced by `KvNet.`, identical).
2. **Copies** (`etc/copy-part.py`, generalized to parts with several source trees): the part's
   sources are `Net/`, `WalTester/`, `RaftNoAx/` and the main tree, in that order; a module path
   means the part's own file if it has one, else the first source tree's. Its roots are its own
   hand-written modules under `KvNet/Spec` and `KvNet/Proof` and gen-init's modules for it. Every module
   of their closure that reaches a seed (a translation of the part, a module of a source part, a
   gen-init module of the part) is copied, imports re-prefixed to `KvNet.`, the source part's own
   copy line replaced by one naming it (`-- The copy for the part `KvNet/` of `RaftNoAx/Spec/...``).
   The trusted code, manual proofs and Goose configuration of a translated package come from the
   source tree whose goose piece translates the same package (`net`: `Net/`; raft and walpb:
   `RaftNoAx/`; `durable`: `WalTester/`, none). A module two source parts both have is a clash: the
   script stops unless gen-init writes it for the part (now: `os`'s initializers and `PkgInitExt`,
   `Net/` and `RaftNoAx/`; `durable`'s initializer, `RaftNoAx/` and `WalTester/`).
3. **Package initializers** (`etc/gen-init.py`, `KVNET_INITS`, `kvnet_inits`): the initializers of
   RaftWitness's list (porcupine, lintest, the protobuf runtime, `os` and its imports), `net`'s
   (`Net/`'s configuration, `NET_SPECIAL`), `durable`'s (the bodied one's, `WT_SPECIAL`) and its
   imports' (`internal/filepathlite`, `path/filepath`), generated from the part's translation and
   copies over the main tree's, and a `PkgInitExt` that is the main tree's with the part's raft.
4. **Links**: none yet (no proof of the part links anything); kvnet's will be `etc/gen-link.py` modes
   as RaftNoAx's.

Also: `lakefile.toml` (lean_lib `KvNet`, a default target), `etc/gates.sh` and CI
(`etc/copy-part.py --check` checks both parts; `etc/goose.py --check` and `etc/gen-init.py --check`
cover the new project, parts and initializers).

To regenerate after a source moves (the order matters on the first run: gen-init reads the copies'
instances, copy-part reads gen-init's imports; a second round is a no-op):

    etc/goose.py --project raft-noax --project net --project durable --project etcd --project kvnet
    etc/copy-part.py --part KvNet
    etc/gen-init.py
    etc/copy-part.py --part KvNet    # (and gen-init again if it changed anything)

A change to a raft file the part copies is made in the main tree (or in `RaftNoAx/`'s own file),
then `etc/copy-part.py` (both parts) carries it here. A part file without the copy line is the
part's own (as in `RaftNoAx/`).

## Decisions taken

- **Reconciling the two `os` initializers.** `Net/Proof/os/Init.lean` and `Proof/os/Init.lean` (and
  `RaftNoAx/`'s copy) prove the same thing; they differ only in which `PkgInitExt` they import
  (`Net/`'s has no raft). The part has one of each, generated, over its own `PkgInitExt` (raft
  included: raft's initializer is an `ExternalInit`). The same for `syscall`, `io/fs`,
  `internal/poll`, `internal/syscall/unix`. `durable`'s is the bodied one's (`WalTester/`'s
  configuration), not `RaftNoAx/`'s (the trusted `durable` over `durableExt`, which kvdurable uses).
- **The protobuf runtime's `IsPkgInit` instances** (`pragma`, `impl`, `protoimpl`, `protoreflect`,
  facts `True`) are in the main tree in etcd cache's `Base.lean`, whose imports reach etcd's
  translation and, through grpc's, the main tree's names-only `net`: a clash with the part's `net`.
  The part declares them itself (`KvNet/Proof/google_golang_org/protobuf/PkgInit.lean`, its own
  file), and gen-init's initializers of those packages name it (the first instance in the part's
  proofs wins). The general fix is to move them in the main tree into a protobuf module that cache's
  `Base` imports; that rebuilds the 7635 modules importing `Base` (`etc/importers.py --count`), so it
  waits for a change that rebuilds them anyway; the part's file then goes. **Follow-up** (accepted
  2026-11-21 by the coordinator, issue #22): move the four instances to a main-tree protobuf module
  when a rebuild of `Base`'s importers is acceptable, then delete the part's file.
- **kvnet's and kvcheck's own initializers and `PkgTable`** are not generated yet: gen-init needs their
  `IsPkgInit` instances (their facts: `StatNames`' array literal), which belong to kvnet's proof. Add
  the packages to `KVNET_INITS` (and the program to a `PkgTable`) when the instances exist.

## What the part holds (2026-11-21)

The closure of the smoke test `KvNet/Proof/.../examples/raft/kvnet/Imports.lean` (kvnet's and
kvcheck's translations, raft-noax's `Spec.go_etcd_io.raft.v3.Api` and `RestartNode` specs, `net.Listen`'s
spec, `durable.Write`'s spec):

| written by | files | lines | what |
|---|---|---|---|
| etc/goose.py | 10 + 14 | 52.6k | `Code/`, `GeneratedProof/`: raft-noax's raft, walpb, `net`, the bodied `durable`, kvnet, kvcheck |
| etc/copy-part.py | 179 (+ 6 `.toml`) | 94.7k | from `RaftNoAx/` 171 (raft's node API and what it stands on: `InvNode*`, `InvApi`, `Protocol/`, the trusted code and manual proofs of raftpb and walpb, ...), from `Net/` 4 (`net`'s trusted code, manual proof, `Base`, `Listen`'s spec), from `WalTester/` 3 (`durable`'s `Defs`, `PkgInit`, `Write`'s spec); none from the main tree |
| etc/gen-init.py | 16 | 1.6k | the initializers listed above and `PkgInitExt` |
| own | 2 | 0.1k | the smoke test `Imports.lean`; `Proof/google_golang_org/protobuf/PkgInit.lean` (above) |

220 modules, 149k lines. **Built** 2026-11-21: `lake build KvNet`, 2627 jobs (the 220 of the part, the
rest the main tree's and Perennial's it imports, up to date), 6m09s wall from a build where only the
part was missing (16 min of CPU; the critical path is raft's invariant chain, 45 compiles, 6m00s:
more cores do not help), peak 2.1 GB per process (`TracedCap`); `.lake/build` grows by 538 MB (379 MB
`lib/lean/KvNet`, 159 MB `ir/KvNet`). No axiom or `sorry` of its own; its copies' axioms are the
generated `opaqueInitsOk` of `path/filepath`'s initializer (as the main tree's) and none other; the part
has no `Link` or `Results`, so `etc/tcb-report.py` has no root in it.

As kvnet's proof grows, its modules become roots (they are the part's own files) and the copies
follow their imports.

## kvnet's network glue (2026-11-21)

Proved in the part, no axiom or `sorry` (`lake build KvNet`: 2717 jobs; `KvNet/{Spec,Proof}/.../kvnet/`):

- **Reused from kvdurablenoax** (the same Go text; `etc/copy-part.py`'s `RENAME_KVNET` copies the
  specs and proofs with the package path and the namespace `raft_kvdurable` renamed, `KVNET_REUSED`
  roots them until kvnet's `Link.lean`): `putUint64`/`getUint64`, `putBytes`/`getBytes`,
  `putIDs`/`getIDs`, `putEntry`/`getEntry`, `putSnapshot`/`getSnapshot`, `withTimeout`; the pure codec
  `Codec.lean`. kvnet's `Base.lean` is the part's own (`IsPkgInit`, fact `True` until kvnet's
  initializer).
- **Frames** (byte level, a reader/writer predicate and a persistent accessor over `netEnd`/`netDir`,
  as Net's `wire.ReadFull`): `writeAll`, `readFull`, `writeFrame` (writes `putB body`), `readFrame`
  (on success the bytes read are `putB l`, `l.length ≤ 2^26`, the slice holds `l`).
- **`closeAfter`**: the caller hands over `R`, its right to close (with an accessor to `Conn.Close`'s
  update); the timer and the returned `disarm` race for it under the mutex: `disarm` returns `true`
  and `R` back if it won.
- **Message codec** (`Wire.lean`: `encMsg`, `MsgWf`): `putMsg` (`msgPtsC … st` gives
  `B ++ encMsg st`), `getMsg` (from `encMsg st`, a fresh message holding `{ st with resps := [] }`),
  `putConfState`/`getConfState` (`encConf`).
- **Addresses** (`Addrs.lean`): `SplitAddrs` (`splitBy 44`), `JoinAddrs` (`intercalate ","`, round
  trip `splitAddrs_joinAddrs` for a nonempty list of comma-free addresses), `decimal`, `AddrOk`
  (returns exactly `Net.addrOk a`: `goAddrOk_eq`, a pure equivalence of the Go scan with the
  extension's parser), `ValidAddrs`, `ValidCluster`.

Decided (the coordinator, issue #22, 2026-11-21):
- `getMsg`'s premise `st.ents = [] ∨ st.snap = none` is gone: kvdurable's `getEntry` spec (main tree)
  now reads its bytes at any fraction (`↦*{dq}`, the entry's data persisted inside its proof; ledger
  entry of 2026-11-21), its copies regenerated, `openStorage` passing `DFrac.discard`.
- **The Go test checks more than the proof needs**: `TestMsgRoundTrip` also checks that `getMsg`
  rejects every proper prefix of an encoding. The proof does not: `readFrame` hands `getMsg` only a
  whole frame, and the protocol layer will give that a frame is exactly what a peer's `writeFrame`
  wrote (a cut stream fails `readFrame`, not `getMsg`).
- `AddrOk`'s premise `a.length + 1 < 2^63` stays: a canonical address is at most 21 bytes, and the
  top-level premises (`addrOk` of every replica address, fewer than 2^32 replicas) discharge it.

## kvnet's client side and kvcheck's pure parts (2026-11-21)

Proved, no axiom or `sorry` (`lake build KvNet`: 2749 jobs):

- **Request path** (`client.go`; `Client.lean`: `reqBytes`, the caller's persistent accessors
  `wAcc`/`rAcc`/`cAcc` and `connRes`): `DialTCP` (`net.DialTimeout` at `"tcp"`), `RequestVia` (on
  `(b', true)` the call wrote `helloClient :: putB (reqBytes kind timeout payload)` and read
  `putB (1 :: b')` on the connection; `false`: the dial failed, or some bytes were written and read),
  `RequestWithin`, `Request`, `EncodeRead`, `EncodeDisrupt`. The predicates track the whole stream a
  call wrote (not the Write errors); the Close accessor is persistent (the deferred `Close` and
  `closeAfter`'s timer may both close); the dialer is a one-shot wand (DialTCP discharges it from
  `DialTimeout`'s exclusive update). `EncodeOp` waits: kvdurablenoax's `encode` spec names
  kvreconf's `encodeOp`, defined in kvreconf's `Base` (which names kvreconf's translation); moving
  it to a pure codec module would let the part reuse `encode`.
- **kvcheck** (its own `Base`, `Defs`: `isChecker`, `checkerInv` under the mutex, `issued`): `oneIn`,
  `below`, `sleep`, `checker.randomID`, `checker.changeID`, `checker.randomChange` (kvdurablenoax's,
  ported; kvreconf's `ccTransOk` restated in `kvcheck/Defs.lean`, its module naming kvreconf's
  translation), `checker.fresh` (each number issued once: `issued γ w n` exclusive).

## The replica layer: plan (2026-11-21, after the crash law; not started)

Go text, kvnet's `replica.go`/`storage.go`/`codec.go` against kvdurablenoax's `kv.go`/`storage.go`
(function by function, the bodies compared with the package name normalized):

- **The same text** (copy+rename by `RENAME_KVNET`, as the codecs): `newStorage`, `image.{applySnapshot,
  append,createSnapshot,compact}` (only the panic strings differ: unreached), `Storage.{ApplySnapshot,
  SetHardState,Append,CreateSnapshot,Compact,snapIndex,InitialState,Snapshot,encode}`, `openStorage`,
  `encodeState`/`decodeState`, `putMap`/`getMap`, `less`/`sortStrings`, `readCtx`/`decodeReadCtx`,
  `validConf` (a comment differs), `fits`, `oneIn`/`below`; `Replica.{request,applyOp,answer,propose}`.
- **Small edits**: `Replica.{snapshot,install,applyEntry,applyConf}` and `run` (the counters are
  `r.stats.add(StX)` indices, not `&r.stats.X` fields: `Stats.add`'s spec, proved); `contents` (also
  returns `r.cs`).
- **Differs**: `newReplica` (no `stopc`/`runDone`/`tickDone`/`snapDone`/`seqs`); `ticker` and
  `snapshotter` (`for range` over the ticker's and `snapc`'s channels, no stop clause); `run` (the
  `Ready` received without the stop select; `send` is `Transport.Send`, which takes each message's
  `F.msgOk`: the seam of the server side); `persist` (no `crashed` flag, returns nothing: the crash is
  the machine's, decision C); `read(seq, key, timeout)` (the client's sequence number: a second read of
  the same `seq` returns no answer while one waits; the context's facts come with the request,
  `F.readOk id seq key`, not from `readSeqs`).
- **Gone**: `readSeqs.next`, `Replica.{stop,crash,conf}`; kvdurablenoax's `Cluster` (kvnet's driver is
  kvcheck over the network).

**What the copies need besides the Go**: kvdurablenoax's proofs stand on kvreconf's shared lemma modules
(`DefsCluster`, `RunFrozen`, `RunBatch`, `BagSend`, `ReadLemmas`, `ConfStep`, `ClientLemmas`, `ReadSlot`,
`Halves`, `PureLemmas`, ...), which import kvreconf's `Base`, so its translation. RaftNoAx has that
translation for this reason (a part of project kvreconf); **KvNet should get it the same way** (a third
`Part` of project kvreconf, root `KvNet`), then copy-part takes those modules as RaftNoAx does. The
alternative, splitting each of them into pure and translation-naming halves, is larger.

**What does not copy**: kvdurablenoax's `Defs.lean` (`isRep`, `isReplica`, `KdNames`, the file
invariant over `durableExt`: `Proof/.../lib/durable/Files`) and everything built on its field layout
(`DefsLaws`, `RunInv`, `RunDmu`, `Alloc`, `StartLemmas`): kvnet's `Replica` struct differs (no stop
channels, no `seqs`, `stats` a `*Stats` of counters) and its file is the bodied `durable` over fsExt. A
kvnet `Defs.lean` is written fresh from it, field by field, keeping the store-level parts (`rkvInv`,
`opSlot`, `readSlot`, `waitP`, `kvLb`, `kvCore`: kvreconf's model, copied from kvdurablenoax's `Defs`
into a module of their own first, so both stores share them).

**Draft specs** (over kvnet's names `γ : KnNames`, the cluster `γ.r.cluster`, `rep γ id r`):

- `Replica.propose(op, timeout)`: kvdurable's, unchanged: `{{ isRep γ id r ∗ d ↪[γ.r.ops]□ γp ∗
  op ↦*□ d }} … {{ v ok; if ok then waitP γ d v }}`; with `F.opOk d := ∃ γp, d ↪[γ.r.ops]□ γp` and
  `F.ansOp := waitP γ`, this is the server side's `Replica.propose.spec F rep`.
- `Replica.read(seq, key, timeout)`: `{{ isRep γ id r ∗ F.readOk id seq key }} … {{ v ok; if ok then
  F.ansRead id seq key v }}`, `F.readOk`/`F.ansRead` as in `notes/kvnet-protocol.md`'s table (the
  context minted by the client, `kd_mint_next`'s facts; the answer `kvLb`-based after `readCtxAfter`).
- `Replica.run(send, …)`: kvdurable's, with `send` the transport's `Send` (`Transport.Send.spec`: each
  message with `msgPtsC`, `F.msgOk src st` and the frame bound, given by raft's `node.Ready` facts,
  `sentMsg`, at `F`'s instance after B) and without the stop clause (it never returns: partial).
- `Replica.persist()` (decision C): under `dmu`, `durable.Write(file, encode())` over fsExt's
  `Write.spec` (WalTester's, copied): the write's update opens the generation's crash invariant
  `inv (body ∨ crashed ∗ tok)` holding `durInv`/`durSt`, the writer's half of the store's per-id ghost
  and `StorageHolds S (decode cur-or-alt)`, and fires the batch's *enter* (`readyEnter`, under
  `notCrashed`) at `durWriteSync` (not at the rename: a crash between them restores the old file).
  Same two forms as kvdurable's (`spec`, `specRun`), without the `ok` result.
- `StartNode(cfg)` (node.go): `durable.Read(file)` (fsExt; the crash invariant's `crashed` side gives
  `durBoot`), `openStorage` (copied), then raft's `RestartNode` at the id's armed vacancy
  (`nodeVacantA γ id x`, from the crash invariant of the previous generation, `nodeVacant_arm`), the AU
  over `raftState` built from the file's decoding (`StorageHolds`), `newTransport`/`start`
  (`start_bag` per peer queue), `newReplica`, the goroutines. Its spec is the server side's
  `StartNode.spec F rep cf S` with `S` the id's start resources (vacancy, file, per-id ghost).

**Hypotheses kept for B** (as the server side's): every cluster-facing fact through `KvFacts F`
(`msgOk`, `opOk`, `readOk`, `ansOp`, `ansRead`) and `stepLaw`/`confLaw`; the store invariant `rkvInv`
and raft's `isCluster` passed as persistent premises (their allocation, at `GooseGlobalGS`, is B's).

**Order** (once builds are allowed): (1) kvreconf's translation into KvNet (goose part) and the reused
proofs of the same text; (2) the store-level `Defs` split in the main tree (rkvInv & co. into a module
both stores import); (3) kvnet `Defs` and the small-edit proofs; (4) `persist` and `run` (decision C);
(5) `read(seq)`, `StartNode`.

### Step 1 done without a build (2026-11-21); kvnet's `Defs` skeleton

kvreconf is translated into KvNet (a third `Part` of project kvreconf; identical to RaftNoAx's up to the
prefix), and `KVNET_REUSED` lists storage.go's and the codecs' functions (`newStorage`, `image.*`,
`Storage.{ApplySnapshot,Append,CreateSnapshot,Compact,encode}`, `encodeState`/`decodeState`,
`putMap`/`getMap`, `less`/`sortStrings`, `readCtx`/`decodeReadCtx`, `validConf`, `fits`, `oneIn`, `below`):
copy-part writes 309 copies (kvreconf's shared modules, kvdurablenoax's `KdStorage`/`Image`/`SnapLemmas`/
`Codec` and those functions' specs and proofs, renamed); built 2026-11-22 (`lake build KvNet`, 2898 jobs).
`Storage.{SetHardState,snapIndex,InitialState,Snapshot}` and `openStorage` are not reused yet: their specs
name kvdurablenoax's `Defs` (its file invariant over `durableExt`); they wait for kvnet's `Defs`.
`Replica.{request,applyOp,answer,propose}` wait for kvnet's `Defs`, which waits for B's shared store
module.

The skeleton (`KvNet/Proof/.../kvnet/Defs.lean`, to be written when B's module lands; the store-level
names are what B is expected to export, at `GooseGlobalGS`: `rkvInv`, `opSlot`, `readSlot`, `waitP`,
`kvLb`, `kvCore`, and the node handle `nh` of B's NodeH API):

```lean
structure KnNames where
  r     : StoreNames      -- B's shared store names (kvreconf's `KvrNames`): cluster, ops, mint, rmint, rds, val, opn
  wr    : w64 → GName     -- per id: the file writer's ghost (decision C: crosses a crash)
  files : DurGS           -- fsExt's durable files (bodied `durable`'s `DurGS`)

-- the replica's fields (replica.go's `Replica`: no stop channels, no `seqs`)
def replicaFields (r : Loc) (id : w64) (file : GoString) (nh : NodeH) (st sts : Loc) (snapc : chan.t) ... :=
  r.[Replica, "id"] ↦□ id ∗ r.[Replica, "file"] ↦□ file ∗ r.[Replica, "node"] ↦□ nodeIface nh ∗
  r.[Replica, "storage"] ↦□ st ∗ r.[Replica, "stats"] ↦□ sts ∗ isStats sts ∗ r.[Replica, "tick"] ↦□ _ ∗
  r.[Replica, "snapc"] ↦□ snapc ∗ isChan… snapc (snapReq protocol) ∗
  isMutex r.[Replica, "dmu"] (dmuInv …) ∗ isMutex r.[Replica, "mu"] (muInv …)

-- `dmu`'s invariant: kvdurable's (`KdDmuNames`, the pending batch's phase) with the file's half over
-- fsExt (`dfile`/`durSt` of `files`), and the crash invariant's view (decision C)
-- `mu`'s invariant: kvdurable's `repOwn` (kv, applied, cs, index, waiters) with `reads : seq ↦ ch`
--   keyed by the client's `seq` (no `seqs`): each waiting read's handoff answers `F.ansRead id seq key`

def isReplica (γ : KnNames) (F : KvFacts GF) (id : w64) (r : Loc) (nh : NodeH) : IProp GF := ...  -- persistent
def rep (γ) (F) : Loc → w64 → IProp GF := fun r id => ∃ nh, isReplica γ F id r nh   -- the server side's `rep`

-- the facts' instance (notes/kvnet-protocol.md's table), over B's shared names
def kvFacts (γ : KnNames) : KvFacts GF := { msgOk := fun src st => sentMsg γ.r.cluster N src st ∗ □ msgCredits … ∗ ⌜..⌝, ... }
```

### The replica layer, done so far (2026-11-22)

Proved, no axiom or `sorry` (`lake build KvNet`: 2965 jobs):

- **`Defs.lean`, `DefsLaws.lean`** (the part's own): kvdurablenoax's interface at kvnet's `Replica`
  (no stop channels, no crashed flag, no `seqs`; kvnet's `Stats`); the file's invariant not yet in
  `isReplica` (it comes with `persist`).
- **Copies of kvdurablenoax's proofs over it** (`KVNET_REUSED`; the copies drop kvdurablenoax's
  `[HasExt durableExt]`, `TEXT_FIXES_KVNET`): `Replica.{request,applyOp,answer}`,
  `Storage.{SetHardState,snapIndex,InitialState,Snapshot}`, `openStorage`, with `SnapMake`,
  `ApplyLemmas`, `ClientLemmas`.
- **Adapted (the part's own)**: `Replica.{snapshot,install,applyEntry,applyConf}` (`Stats.add` by
  index, no crashed half), `Replica.{ticker,snapshotter}` (`for range`, no stop),
  `readSeqs__nextLemmas` (without the `readSeqs.next` spec: `kd_readAu`, `kd_mint_next` for the clients).
- **At the protocol's facts** (`Facts.lean`: `kvFacts γ cf`, `kvRep γ vs dir`): the server side's
  `Replica.read.spec` and `Replica.propose.spec` are proved at `kvFacts`/`kvRep` (the read with the
  client's context and the busy-`seq` check; the proposal with its slot from the request).

**Seams**: `kvFacts`'s `confOk` is a parameter (`cf`) until `confLaw` is discharged. (`ansLen.law`,
`waitLen.law`, added with `read`/`propose`, are gone: next section.)

### The answers' lengths (2026-11-22): a local bound, no store-level seam

`Replica.read`/`propose` promised `len(v) < 2^61` to the server, which neither `waitP` nor `readAns`
gives (they say which committed history the value is from, nothing of its length), hence the two seams.
What the server really needs: `serveClient` writes `resp = append([]byte{1}, ans...)` with
`writeFrame`, which computes `make([]byte, 0, 8+len(body))`, so `len(v) + 9 < 2^63` (Go panics on the
negative capacity otherwise); `kvQ`/`server_reply` need only `len(v) < 2^63`. A slice gives `len(v) <
2^63` (`ownSlice_len`), not the `+ 9`: the bound has to come from an invariant. It is local to the
replica: every value it holds is `b[17+n:]` of an entry `b` it decoded (`decode`; `decodeOp_val_len`:
`len(val) + 17 <= len(b) < 2^63`), or a value of a snapshot's map (`install`'s new premises `MapFits K'`,
`MapFits A'`, which `run` gets from `decodeState`: each value sits inside the snapshot's slice after two
8-byte length prefixes). So `Defs.lean` has `MapFits M` (every value `v` has `len(v) + 9 < 2^63`) in
`repOwn` (the store's map `K`) and `repShared` (the applied table `A`), and the waiters' handoffs carry the
bound with the answer (`waiterOk`, `readWaiterOk`). The server side's posts (`Replica.read`,
`Replica.propose`, `Node.handle`) promise `(len(v) : Int) + 9 < 2^63`, weaker than `2^61`. That is
exactly what `serveClient` uses (its proof needed no change). The store-level alternative (lengths in kvreconf's `MintOk`,
derived through `rkvInv`) would have touched the main tree and kvdurable's minting proofs for no gain.
Cost: `Replica.{applyOp,answer,request}` and `ApplyLemmas` are now the part's own (out of
`KVNET_REUSED`: their texts differ from kvdurablenoax's by the bound).

**Next: `persist` (decision C)**. The file's invariant moves to fsExt: per id, with the bodied
`durable`'s names `γd : DurGS` and file `f : DFile`,
`kdFileInv γ γd id := inv (kdRepN .@ id) (∃ S s, raftState γ.r.cluster id S ∗ durSt γd s ∗
ghostVar (γ.wr id) ½ (S, s.cur) ∗ ⌜StorageHolds S (decodeOpt (s.alt.getD s.cur))⌝ ∗ …)` (while a write's
rename may still be lost, `alt` holds the old contents, which hold the durable state; the batch's *enter*
fires at `durWriteSync`, when `alt := none`); `dmu` holds the call's `durHandle γd f R` and its
`osCallPerm` (exclusive: one writer at a time), `isReplica` the persistent `durInv γd f`, `osInv`,
`osSharedInv R`. `persist`'s two forms (`spec`, `specRun`) are kvdurable's without `ok`. Then `run`
(kvdurable's 1615-line proof and its `Run*` lemmas, over `persist.specRun`), `newReplica`, `StartNode`
(`durable.Read` under the crash invariant's `crashed` side, `openStorage`, `RestartNode` at
`nodeVacantA`).

### `persist`: what decision C's design needs, and the gap found (2026-11-22)

Read against the bodied `durable`'s `Write.spec` (`WalTester/Spec/.../lib/durable/Write.lean`), three findings.

1. **The sync update needs the crash token (done).** Raft's batch *enter* (`readyEnter`) takes `notCrashed`, and
   decision C fires it at `durWriteSync`. That update was a plain atomic update, so a client could not get the token
   there. But `Write`'s proof fires it at a ghost step after `Sync` returns, where it holds the token
   (`durInv_commit`, after `wp_notCrashed_acc`). Now `durWriteSync γ Ψ` is `notCrashed -∗ AU <{…}> <{ durSt γ
   ⟨s.cur, none⟩, COMM notCrashed ∗ Ψ }>` (WalTester's `durable/Defs.lean`). `durInv_commit` passes the token,
   and `durWriteSync_of_au` turns a plain update into one (the tester's `storeOracle` uses it). The rename's update
   is unchanged: it fires inside the os rename's update, which gives no token. Ledger, 2026-11-22.
2. **The 1 GiB bound (lifted 2026-11-22**: `ReadAt.specLong`, `tryWrite` over `WriteAt.specLong`, `Write.spec` takes `len(data) < 2^63`; the text below is the finding as it was). `Write.spec` takes `len(data) <= 2^30` (`DCand.Ok`: one `WriteAt`, one `ReadAt` of
   at most `maxRW`). kvnet writes `string(storage.encode())`, and its image has no size bound (the Go code checks
   none). `WriteLong` (`Spec/os/WriteLong.lean`) already covers `WriteAt` of any length. Lifting the bound needs the
   same for `ReadAt` (`durable.tryRead` reads the whole file), then `tryWrite`/`tryRead` over them. Until then
   `persist` can only take a `Write` spec without the bound as a callee (unproved), or the closed theorem bounds
   the store's size. Either way it is a decision.
3. **The rename/sync window (the gap, open).** Between `Write`'s rename and its sync, a crash may keep **either**
   file (`durInv_crash`: `cur` or `alt`). Decision C fires the *enter* at the sync. But if the crash keeps the
   new file (`cur`, the batch's durable state `S'`), raft's durable state is still `S` (`nodeCrash` keeps it),
   and `RestartNode` needs `StorageHolds S σ` of the storage it reads: the restart is not provable. Firing the
   *enter* at the rename fails the other way (the old file may survive). Every choice of a single ghost point
   fails, because the kernel decides at crash time which file survives. Ways out:
   - (a) raft: a crash law for a batch cut and not entered, `crashed ∗ <the cut's crash-side resource> ∗ raftState
     S ={E}=∗ raftState S'`, handed out with `readyEnter` and used by the next boot when the file it reads holds
     `S'`. The cut already moves the durable maps forward (`notes/raft-crash-law-design.md` (j)), so it may be
     provable;
   - (b) kvnet: a boot that picks the surviving file's state, which needs (a) or an equivalent;
   - (c) `durable`: a write with one durability point. The rename-then-sync protocol does not have one.

   (a) is the only option I see. `persist`'s proof does not depend on the crash story beyond the file
   invariant's shape. That shape would record, while `alt = some old`, that `old` holds `S` and `cur` holds the
   pending batch's `S'`, plus the crash-side resource of (a). So `persist`, `run` and `StartNode` wait for this
   decision.

### The crash law kvnet needs: entering a cut batch at the next boot (2026-11-22, for raft's agent)

**Decided** (the coordinator, 2026-11-22): raft adds a variant of `nodeCrash`. At a crash with a batch cut and not
entered, the next generation may either discard the batch (today's `nodeCrash`) or enter it: `StartNode` chooses
by what `durable.Read` returns. Until raft proves it, kvnet takes it as a law hypothesis (`abbrev
readyCrashEnter.law : Prop` in kvnet's defs, passed to the `wp_proof`s that need it).

**The statement kvnet needs**, over raft's existing API names (`KvNet/Proof/go_etcd_io/raft/v3/InvNode.lean`:
`readyEnter` `:1082`, `raftState` `:716`, `nodeVacant` `:721`, `nodeCrashTok` `:734`, `nodeCrash`
`InvNodeRule.lean:665`, `isCluster`; `crashed` is the generation's, under `[CrashGS GF]` as in `nodeCrash`):

```lean
variable [CrashGS GF] in
/-- A batch cut and not entered (its *enter*, `readyEnter`, unused) may be entered after the crash, by
the next generation: the arm's crash token gives the vacancy back (as `nodeCrash`) and the durable
state moves to the batch's. -/
abbrev readyCrashEnter.law : Prop :=
  ∀ (n : NodeH) (γ : Cluster) (N : Namespace) (id : w64) (st st' : NodeDriverState) (ms : List QMsg)
    (x : CrashNames) (E : CoPset), ↑N ⊆ E →
  ⊢ isCluster (GF := GF) γ N -∗ crashed -∗ nodeCrashTok γ id x -∗
      readyEnter n γ N id st st' ms -∗ raftState γ id st.durable ={E}=∗
      raftState γ id st'.durable ∗ nodeVacant γ id
```

Notes for its proof:
- `readyEnter` is a plain `def` today, a wand that needs `notCrashed`. The law needs raft to keep, behind it, the
  batch's crash side: the `pendBatch γ.raft id g st'.durable W` of the cut generation `g`
  (`Protocol/GhostState.lean:3110`), which `raft_enter` consumes. One way that keeps every client: redefine
  `readyEnter := readyEnterLive ∧ <crash side>`, where `readyEnterLive` is today's wand. The clients that fire it
  then add an `and_elim_l`, and the law is `and_elim_r` plus the crash-side lemma. Another way: seal the hand-out
  and prove the law from it. Either is raft's choice, as long as the statement above holds of the `readyEnter`
  that `node.Ready`'s post (`readyPost`, `InvNode.lean:1686`/`:1730`) gives.
- **What kvnet does with it.** `persist` moves the batch's `readyEnter` into the file's invariant at the rename
  (`alt = some old`: `old` holds `st.durable`, the new `cur` holds `st'.durable`). At the sync
  (`durWriteSync`, with `notCrashed`) it takes it back out and fires it. After a crash in between, the boot
  (`StartNode`) reads the file. If the file holds `cur`, the boot applies the law; if it holds `old`, it applies
  `nodeCrash`, which drops the batch.
- The crash token is the arm's `nodeCrashTok γ id x` (`nodeVacant_arm`). kvnet keeps it in its crash obligation.

### `Replica.contents`, `PutStatus`, `Node.status` (2026-11-22)

- **`kv` under `mu`.** Half of the `kv` field and of its map moved from `repOwn` into `repShared`, as for
  `applied`, with `MapFits K`. Every access in the Go holds `mu`. `applyOp` combines the halves to write,
  `install` to store a new map, and `answer`/`request` read with their half. `applyEntry`, `applyConf` and
  `propose` pass the halves through.
- **`Replica.contents` is proved** (`Replica__contents.lean`). Pre `isRep γ vs dir id r`; post a fresh map `m ↦$ M`
  with `MapFits M`, the applied index, and `csOpt csp DFrac.discard c`.
- **`PutStatus` (open).** Its current spec is unprovable: it takes nothing of what it encodes, and its `< 2^61`
  has no source. Ownership is easy to add (`s.Contents ↦${dq} M ∗ csOpt s.Conf dq c`, as `putMap`/`putConfState`
  take; the loops unfold to `wp_for`). The **length bound is not derivable**: `MapFits` bounds each value, but no
  invariant bounds the number of keys, so the status encoding is unbounded in the model. `serveClient` then needs
  `len + 9 < 2^63` for `writeFrame`'s `make([]byte, 0, 8+len(body))`. Options:
  - (a) Go: `writeFrame` returns `false` for a body past `maxFrame`. `readFrame` refuses such frames anyway, so
    nothing is lost. `writeFrame`'s premise then disappears, and so do the answers' `+ 9` bounds (`MapFits` would
    be needed only by `PutStatus`'s callers, if at all).
  - (b) a store-size invariant: lengths in the minted operations plus a bound on their number. Much larger.
  I left `PutStatus.spec` and `Node.handle` unchanged until this is decided.
- **`Node.status` (open).** Besides `contents`, it reads `st.HardState`'s term and commit from raft's `Status`, whose
  `statusOwn` is sealed. It needs a raft API law exposing the hard state's read access (`statusOwn st ⊢ ∃ hs,
  hsRO st.BasicStatus'.HardState' hs ∨ …`, as `InvStatus.statusOwnRaw` holds), and a spec for `Stats.Snapshot`
  (easy: the counters under the mutex).

### `persist` proved (2026-11-22)

- **Defs** (`Defs.lean`). `KdDmuNames` gains the file's names: `γd : DurGS`, `df : DFile`, `fR : Roots`, so
  `isReplica`'s arity is unchanged.
  - `dmu` holds `durHandle` and a share of the directory's `osCallPerm`.
  - `isReplica` holds `osInv`, `osSharedInv`, `durInv`, the file invariant, and `df.Ok ∧ df.name = kdFileName dir id`.
  - The file invariant `kdFileInvK γ id n ph` is a plain invariant of the generation; the crash obligation carries
    its contents. It holds `raftState γ id S ∗ durSt γd s ∗` the writer's half `(S, s, pb)`, and `kdFileState`:
    - outside a window, the file holds `S` (`fileHolds`: decodes, `KdFileOk`, certificate);
    - in a window, the old contents hold `S`; the new ones hold `S`, or, with `pb = some (γb, S2)`, the batch's
      `S2`, whose `readyEnter n … st st' ms` and `savedPropOwn γb □ (kdBatchRes …)` wait there. This is what the
      boot hands to `readyCrashEnter.law`.
  - The writer's value is `KdWv := RaftState × DurSt × Option (GName × RaftState)`. A `NodeH` cannot sit in a ghost
    variable (it lives in `Type 1`), hence the node `n` as the invariant's parameter: one node per generation.
  - Every kvnet file over these predicates now declares `[ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]`.
    Four former copies became the part's own (the `answer`, `request` and `persist` specs, and `ClientLemmas`).
- **`PersistLemmas.lean`.** `kd_writeAU`, the write's two atomic updates. At the rename, the batch's *enter*
  moves into the invariant. At the sync (crash token, one later credit), it fires and the batch's results stay at
  `γb`. `kdPendIn`/`kdPendOut`, `pbTarget`, `fileHolds_some`.
- **`Replica__persist.lean`.** `persist.wp_proof`: a batch `waiting` in `dmu` becomes `fired`.
  `persist.wp_proofRun`: `run`'s own batch's results come back by the saved proposition's agreement, and the phase
  returns to `idle`. Its spec is the kvdurable one without `ok` (kvnet's `persist` returns nothing).
- **Next.** `run` (kvdurablenoax's 1615-line proof and its `Run*` lemmas, over `persist.specRun`), `newReplica`
  (allocates the file invariant: the writer at `(S, ⟨cur, none⟩, none)`), and `StartNode` (reads the file:
  `fileHolds` of `cur` or of `alt` per durable's crash lemma; `RestartNode` at `nodeVacantA`; after a crash
  in a window, `readyCrashEnter.law` or `nodeCrash`).

### Drafts written with no `.lake` (2026-11-22, unchecked)

The worktree's `.lake` was lent to raft's agent. These files are drafts, to check once it returns. The
**first step** then is `python3 etc/copy-part.py --part KvNet && python3 etc/gen-init.py` (both need
Perennial's checkout under `.lake`): `RunLemmas` imports `kvreconf.RunBatch`, whose copy does not
exist yet.

- **`Replica.run`** (`Replica__run.lean`, from kvdurablenoax's, with `RunDmu`, `RunImage`, `RunInv`,
  `RunLemmas`; `sendSpec` added to `Defs.lean`). Changes:
  - the `Ready` is a plain receive (`chan.wp_receive` over `isReadyChan_recvAu`'s update), the `select`'s
    clause body dedented and the `stopc` clause gone;
  - `run_exit` just returns;
  - no `runDone` producer (`runInv`, the write's `wp_join`);
  - `persist` returns nothing (the crashed branches gone);
  - `Stats.add` by index;
  - `kdDmuRest` carries the file's handle and call permission (no crashed flag). `dmu_close_enter`
    enters a commit-only batch through `kdFileInvK`: the file keeps its contents, now holding the new
    state (`fileVal_commit`, `holds_commit_only`);
  - `kdDmuInv`'s call-permission field is renamed `Hcpm` (it clashed with `runInv`'s `Hcp`).

  Expected failures:
  - the receive's shape: `chan.wp_receive`'s continuation, and whether `<-ch` is `Fst (chan.receive …)`;
  - the clause body's `wp_*` steps after the receive (which ran inside a `select` before);
  - `notCrashed`'s instance in `dmu_close_enter` and `wp_ncfupd`;
  - the iframe/iNamed patterns over `kdDmuInv`'s new fields (`Hdh`, `Hcpm`);
  - heartbeats (the proof is 1600 lines).
- **`newReplica`** (`newReplica.lean`, spec and proof). As kvdurable's, without the stop channels, the
  crashed flag and `seqs` (12 arguments). It takes the file's names, handle and call permission, and the
  generation's `kdFileInvK γ id n γd` (now over `γd`, not `KdDmuNames`). New premises `MapFits Kv`,
  `MapFits A`. Half of `kv` goes to `mu`. Post: `isReplicaR`.

  Expected failures: `iStructNamed`'s field names for kvnet's `Replica`, the order of `isReplica`'s
  pure conjuncts, and `sq` (passed as `sts`; unused).
- **`BootLemmas.lean`**:
  - `readyCrashEnter.law` (the hypothesis);
  - `kd_boot_choose`: from the crashed generation's `kdFileState` and the contents `v` that durable's
    crash lemma reports (`v = s.cur ∨ s.alt = some v`), either the law (the new contents survived
    with a pending batch) or raft's `nodeCrash`. It gives `raftState S' ∗ nodeVacant ∗ fileHolds S' v`;
  - `kvStart`: the concrete start resource `StartNode` takes (`StartNode.spec`'s `S`).

  The branch is at the boot (the crash obligation), not in `StartNode`'s code: durable's crash lemma
  decides at the crash which file the next generation finds.
- **`StartNode`'s proof: not drafted.** kvdurable's `Cluster.start` (524 lines) is the model, but it
  goes through kvdurable's cluster helpers (`fileOf`, `config`, `tick`, `sender`), which kvnet inlines
  (`FileOf`, the `raft.Config` literal, `newTransport`/`t.start`, `t.Send`). The plan:
  - `durable.Read`'s atomic update over `kvStart`'s `durSt`;
  - `openStorage` of `encStor f` (`fileHolds S cur` gives `cur = kdFileVal o` with `KdFileOk`);
  - `MemoryStorage.Snapshot`, `decodeState` and `Applied` as in kvdurable;
  - `RestartNode` at `nodeVacantA γ id x`, its update over `raftState S` (`StorageHolds S`);
  - after `RestartNode` (the node `n` exists), allocate `kdFileInvK γ id n γd` from `raftState`,
    `durSt` and one writer half (`kdFileState` at `alt = none`: `fileHolds S cur`);
  - `newTransport`, `t.start(node)` (the step law: `kv_stepLaw`), and `t.Send` for `sendSpec`
    (`Transport.Send.spec`: `msgPtsC`, `F.msgOk` from `sentMsg`/`msgCredits`/`MsgWf`, and the frame
    bound, which `writeFrame`'s change may make unnecessary);
  - `newReplica`.

### The drafts checked, raft's real crash law, `Node.status` (2026-11-22)

- **Raft's `readyCrashEnter`** (landed on lean) replaces the hypothesis. It also takes `nodeArm n γ x` and a share
  of `nodeRunning`. In a write's window the file invariant now keeps that share with the batch's *enter*
  (`KdWv`'s batch records the share `q`). `kd_writeAU` takes `kdRunKeep` (the writer's share, if no batch) and
  gives back `pbQ q pb`. `persist` puts its share into the batch at the rename and takes it back at the sync.
  `kd_boot_choose` (`BootLemmas.lean`) takes `nodeArm` and uses the share that waited. `readyEnter` is
  `readyEnterLive ∧ readyEnterCrash`: the live uses take the left half.
- **The drafts, checked and fixed**: `writeFrame`, `Node.handle`, `RunDmu`, `newReplica` (`sendSpec` persistent),
  `Replica.run`. In `run`, the receive's credits come from `chan.wp_receive` (`wp_Ready` without `lc`), and a
  snapshot's maps get their `MapFits` from their encoding (`MapFits_of_lookup`, `RunLemmas.lean`).
- **Proved**: `Node.status` (at `kvRep`, through `statusOwn_hardState`), `Stats.Snapshot` (it gives the array's
  length, 23), `PutStatus` (it takes that length: the stats loop indexes the array value).
- **`StartNode`: next.** Its callees still without specs: `newTransport`, `Transport.start`, `FileOf` (with
  `itoa`), `quietLogger`'s methods. Its post also has `confLaw` (not discharged: the real `confOk`).
  The plan is as above ("Drafts written with no `.lake`"), from `kvStart` (`BootLemmas.lean`), allocating
  `kdFileInvK` after `RestartNode` gives the node (and `nodeArm`).

## Handoff (2026-11-22)

Branch `worktree-agent-a9b8a3f3fbe5852a9`, head `f580a06a79` (land requested on #22; built: `lake build
KvNet` 2984 jobs, `WalTester KvNet` 4288, tier/copy-part/gen-init checks). Everything below is in the part
`KvNet/` (`KvNet/{Spec,Proof}/github_com/mit_pdos/etcd_grove/examples/raft/kvnet[/kvcheck]/`); no axiom, no
`sorry`. kvnet's design: this file (the part, the replica layer) and `notes/kvnet-protocol.md` (the wire
protocol, decision E); the plan `notes/kvnet-proof-plan.md`.

**State of every kvnet function.**
- **Proved (93 in kvnet, 11 in kvcheck)**: the codecs (reused from kvdurablenoax by `RENAME_KVNET`:
  put/get Uint64, Bytes, IDs, Entry, Snapshot, Map; encode/decode, readCtx/decodeReadCtx,
  encodeState/decodeState, less/sortStrings, validConf, fits, oneIn/below, withTimeout); storage.go
  (`newStorage`, `image.*`, `Storage.*`, `openStorage`); the wire (`writeAll`, `readFull`, `writeFrame`,
  `readFrame`, `putMsg`/`getMsg`, `putConfState`/`getConfState`, `closeAfter`); addresses (`SplitAddrs`,
  `JoinAddrs`, `decimal`, `AddrOk` = `Net.addrOk`, `ValidAddrs`, `ValidCluster`); the client (`DialTCP`,
  `RequestVia`/`RequestWithin`/`Request`, `EncodeOp`/`EncodeRead`/`EncodeDisrupt`); the server
  (`Transport.{dropped,enqueue,Send,dial,runPeer,servePeer}`, `listen`, `Node.{serve,serveClient,handle,status}`,
  `Run`, `RunNode`, `Stats.{add,Snapshot}`, `PutStatus`); the replica (`newReplica`, `Replica.{run,persist,
  request,snapshot,snapshotter,install,applyEntry,applyConf,applyOp,answer,propose,read,contents,ticker}`);
  kvcheck (`oneIn`, `below`, `sleep`, `checker.{randomID,changeID,randomChange,fresh,randomMember,request,do,read}`).
- **Spec only** (a callee hypothesis of a proof): `StartNode` (taken by `Run`), `GetConfChange` (by
  `Node.handle`).
- **No spec yet**: `newTransport`, `Transport.start`, `FileOf`, `itoa`, the `quietLogger` methods, `RandomOptions`,
  `FormatStats`, `PutConfChange`, `GetStatus`, model.go's `Model`/`Gen`/`copyMap`/`within`/`hashString`/`hashMap`,
  kvcheck's `checker.{conf,reconfigure,disrupt}` and `Check`.

**Seams still hypotheses, and what discharges them.**
- `confLaw F rep cf γ N id` (`NodeDefs.lean`; a premise of `Node.handle`/`serveClient`/`serve`/`Run`): from a
  decoded requested change it gives `node.ProposeConfChange`'s precondition (the `□?γ.dup` AU over
  `ownCommittedOps`). Discharged by the store's conf policy (kvdurable's `Cluster.Reconfigure`/`kd_confAu`
  pattern: `confPolicy`, `ConfShaped`), at `kvFacts`' `confOk` := the real shape (`ccTransOk` of
  `GetConfChange`'s model; `cf` is today a parameter of `kvFacts`).
- `GetConfChange.spec cf` and `StartNode.spec`: prove them (GetConfChange: kvdurable has no counterpart;
  write it over raftpb's ConfChange/ConfChangeV2 constructors, `cf c pl` := the model of `pl`).
- The minting laws of kvcheck's `do`/`read` (the caller's: `issued … ={⊤}=∗ F.opOk …`/`F.readOk …`):
  discharged at `kvFacts` by the store's `kd_mint` / `kd_mint_next` (kvdurable's `ClientLemmas`,
  `readSeqs__nextLemmas`; kvnet's own copy) — now possible on the client machine, since decision B made the
  store invariant global.
- `stepLaw` and `msgOk_wf`: discharged (`kv_stepLaw`, `kvFacts.msgOk` carries `MsgWf`); `stepLaw`'s pure
  cluster premises (untraced, no data bound, no snapshot directories) are the cluster's allocation facts.

**Next steps, in order.**
1. `StartNode` (node.go): specs and proofs of `newTransport` (the peers map, a `make(chan, queueLen)` per
   peer: `start_bag`/`isChanBag`, building `isPeers`), `Transport.start` (go `runPeer` per peer), `FileOf`/`itoa`,
   the `quietLogger` methods (copy kvdurablenoax's `QLogger.lean`/`quietLogger__*`); then StartNode itself per
   the plan above (`kvStart` → `durable.Read` → `openStorage` → `RestartNode` with `nodeVacantA`, allocate the
   file invariant with `nodeArm`, `newReplica`, the goroutines). The boot's crash choice is `kd_boot_choose`
   (`BootLemmas.lean`, over raft's `readyCrashEnter`/`nodeCrash`).
2. `confLaw` and `GetConfChange` (above); `kvFacts`' real `confOk`.
3. kvcheck's `Check` over lintest (kvdurable's `Run`/`Main` and `lintest/Run.lean` as the pattern: timeout 0
   gives `Ok`-or-`Illegal`; `applySpec` an AU over `libState`), with `checker.{conf,reconfigure,disrupt}`,
   `Gen`/`Model`, the minting laws discharged.
4. Adequacy and linking: kvnet's `Link.lean` (an `etc/gen-link.py` mode as `--kvdurable-noax`; it imports
   raft's Link, so the part copies raft-noax's ~1000 proof modules: budget ~12 min / 3 GB more); `Hstart` with
   `cluster_alloc_nb` (B: global, no bootstrap log, `dup = true`), the store's allocation (B's `Store.lean`),
   `addrs_set_proto` of every replica address with `kvP (kvFacts …) id`/`kvQ …`; the per-node crash frame
   `P i L` (the generation's crash invariant: `nodeVacant` from `readyCrashEnter` or `nodeCrash`, `durSt`, the
   per-id ghost; decision C); the stable client node (kvcheck, no crash obligation: Perennial's mixed
   adequacy, decision F).
5. `Spec/.../kvnet/TopLevelRobustness.lean` (`def raft_kvnet_robust.spec`), over lean's `Robust` with its new
   `threads` parameter (`DistCrashNstepsBelow`), the programs and definitions in `Proof/.../kvnet/TopLevelDefs.lean`;
   `Proof/.../kvnet/TopLevelRobustness.lean` from the closed theorem; the corollary and the non-vacuity lemma
   (`notes/kvnet-robust-goal.md`, CLAUDE.md's layout).

**Scripts** (they were in `/tmp`, not in the repo; each is a few lines):
- regenerate to a fixpoint: `etc/copy-part.py --part KvNet && etc/gen-init.py && etc/copy-part.py --part
  KvNet`, then `etc/copy-part.py --check` and `etc/gen-init.py --check` (needs `.lake/packages/perennial` or
  `PERENNIAL_DIR`).
- the full check: the above, then `nice lake build KvNet` (and `WalTester` when `durable` changes),
  `etc/tier-check.py --check`, and a grep for `sorry`/`axiom` in `KvNet/{Spec,Proof}/.../kvnet`.
- lean-check by short name: `etc/lean-check.py -q [-a] KvNet/Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/<F>.lean`.
- translations: `etc/goose.py --project kvnet` (and the parts: `--project raft-noax --project net --project
  durable --project etcd --project kvreconf`; `--check` to compare). Go: `cd examples/raft/kvnet && go test
  ./... && go test ./driver -run TestKill -count=1` (PATH with `/usr/local/go/bin`, `GOTOOLCHAIN=go1.27.3`).

**Pitfalls.**
- copy-part prefers the part's **own** file at a path, and `RENAME_KVNET` maps kvdurablenoax's modules to
  kvnet's paths: an own `kvnet/X.lean` silently replaces kvdurablenoax's `X` for every copy that imports it
  (how `Defs`/`DefsLaws` work); a copied file edited by hand must lose its first (copy) line, or the next run
  overwrites it. Don't write a script that bulk-copies RaftNoAx files into `KvNet/` (one such run overwrote
  kvnet's own `Run` spec/proof with kvdurable's cluster `Run`; restored from git).
- A kvdurablenoax module whose spec names its `Defs` (durableExt's file invariant) cannot be reused as is
  (`Storage.InitialState` once pulled `lib/durable/Files` into the part and broke the build): reuse only via
  kvnet's own `Defs` at the same path.
- Gen-init's KvNet initializers read the part's copies' instances, and copy-part reads gen-init's imports:
  after a change, run the pair twice (the fixpoint).
- The main tree's protobuf instances live in cache's `Base`; the part has its own
  (`KvNet/Proof/google_golang_org/protobuf/PkgInit.lean`, a follow-up to move them in the main tree).
- Builds: one lake build at a time on this machine (coordinate on #22); disk is tight (a `.lake` is ~45 GB;
  seed by `cp -a` from a worktree at the same Perennial pin).
- The worktree-isolation guard rejects compound shell commands naming long paths with `git`/`cd`: put such
  sequences in a script file.

## `StartNode`'s callees, `GetConfChange`, the conf law (2026-11-22, branch `kvnet-proof`)

Proved (no axiom, no `sorry`; `lake build KvNet` 3008 jobs):
- `FileOf` (own) and, copied from kvdurablenoax (`KVNET_REUSED`, the same Go text), `itoa`, the four
  `quietLogger.*f` methods (`QLogger.lean` with them) and `ReconfAu` (`kd_ccAu`, `kd_ccAu_dup`).
  `qLogger_isLogger` is not copied: kvdurablenoax has it in `Config.lean` with `Cluster.config`; `StartNode`'s
  proof restates it (ten lines).
- `newTransport`: the peers map built by `wp_map_for_range` over the read-only address map, each other
  replica's peer with a fresh bag channel (`start_bag` of `qElem F pid`), given `addrProto a (kvP F pid) (kvQ F
  pid)` and `addrOk a` of every other address (a persistent premise); post: the id, stats, the unset node field,
  `isPeers`.
- `Transport.start`: stores the node, makes `isTransportCore` (the step law and an untraced cluster are the
  caller's), forks `runPeer` per peer.
- `getUint64.specAny` (own spec module `getUint64Any`, proof `getUint64.wp_proofAny`): on any bytes; not `ok`
  (rest the nil slice) when shorter than eight.
- `GetConfChange` at `cf := kvConfRead` (`ConfDefs.lean`): on any payload, an owned change
  (`ownConfChangeI … (some o)`) of a defined transition (`ccTransOk`). The payload is made read-only first (the
  post does not give it back), so the two `getUint64` of the input and `b[0]` share it.
- `kv_confLaw γ vs dir id` (`ConfLaw.lean`): `confLaw (kvFacts γ (fun _ => True)) (kvRep γ vs dir) kvConfRead
  γ.r.cluster kdRaftN id`. So `kvFacts`' `confOk` is `True` at the top level: the server proposes whatever change
  it is asked, and the store's conf policy decides at the commit.
- kvcheck's `checker.disrupt` (a loop over `sleep`, its answers dropped). Left in kvcheck: `checker.conf` (needs
  `GetStatus`, a decoder like `GetConfChange`), `reconfigure` (needs `PutConfChange`, whose payload bound
  `len + 17 < 2^63` needs `randomChange`'s post to bound its changes, at most three, and a premise
  `∀ pl, F.confOk pl`), `Check`.
- Built after merging `lean` at the Perennial pin `c14cca87a` (`lake build KvNet` 3016 jobs).

### `StartNode` and the crash frame: blocked on raft's `RestartNode` update (2026-11-22)

**The gap** (ledger 2026-11-22, `RestartNode`). Perennial's (mixed) crash adequacy takes a generation's crash
obligation when the generation starts (`∀ L', crashed -∗ extsCrashStart … ={⊤}=∗ P i L'`), not as a WPC carried
through the code. So the next generation's exclusive start resources must sit, from the generation's start on,
in invariants that the obligation can empty with `crashed` and a token it keeps: `inv (body ∨ crashed ∗ tok)`.
For kvnet those are raft's `raftState γ id S` and the file's state (what `kd_boot_choose` takes). Any other
opener must refute the crashed side with `notCrashed`, which a thread has only at a step (`wp_ncfupd`,
`wp_atomic_nc`, channel `ncfupd`s), or must not need what the crash takes. `RestartNode`'s client update is a
plain atomic update fired inside `RestartNode` and needs `raftState`: on the crashed side it can produce neither
`raftState` nor `StorageHolds S σ`, and taking `raftState` out before the call loses it to a crash during
`RestartNode`. Hence: **`RestartNode`'s update must take and give back `notCrashed`** (as `durWriteSync` does;
raft's proof fires it before any step). Raft's change: reported on #22, not made here.

**kvnet's design once that lands** (each item checked against the current proofs, not built):
- The file invariant is allocated at the generation's boot (the crash obligation's `P i L'`, or `Hstart` for the
  first), not after `RestartNode`: `kdFileInvK γ id γd wr x` with
  `inv (∃ S s pb, durSt γd s ∗ ghostVar wr ½ (S, s, pb) ∗ fileHolds-part (persistent) ∗
   ((raftState γ id S ∗ batch's exclusive pieces) ∨ crashed ∗ tokK))`.
- The node moves into the batch record: `pb = some (γb, S2, q)` holds `∃ n, nodeArm n γ x ∗ readyEnter n … ∗
  nodeRunning n q ∗ savedPropOwn γb (kdBatchRes γ id n st' ms)`. `persist`/`run` need no `n = n'`: `run` gets
  its batch's results through the saved proposition's agreement, as now. `persist` needs `nodeArm n γ x` at the
  rename (from `RestartNode`'s post, kept in `isReplica`).
- The writer variable becomes per generation (the dead generation's `dmu` keeps the other half): `KdNames.wr`
  goes, its name joins `KdDmuNames`.
- Openers: the rename's update (no token) touches only `durSt` and the writer and, on the crashed side, drops the
  batch's pieces; the sync update and `dmu_close_enter` (`wp_ncfupd`) and `RestartNode`'s update (once it has the
  token) refute the crashed side.
- The crash obligation: open the file invariant with `tokK`, take `raftState` and the batch, run `durInv_crash`
  with `durSt` (given back), close with `crashed ∗ tokK`; `kd_boot_choose`; a fresh writer variable and the
  next `kdFileInvK` from `durBoot`'s new names.
- `StartNode.spec`'s `S` must depend on the configuration (`S : NodeConfig → GMap w64 GoString → IProp GF`, and
  `Run`/`RunNode` likewise): the start resources name `dir`, the id, the voters (`kdCluster γ vs` with `vs` the
  bootstrap voters), every other address's protocol (for `newTransport`), and the globals `runPeer` needs
  (`net.errTimeout`). A ledger entry when it is changed.

**Next, in order.** (1) Raft: `RestartNode`'s update with the crash token (raft's agent). (2) kvnet: the file
invariant's restructuring above (`Defs`, `PersistLemmas`, `Replica.persist`, `RunDmu`, `newReplica`,
`BootLemmas`), then `StartNode` (template: kvdurablenoax's `Cluster.start`, 524 lines; plus the boot
configuration loop, `&Stats{}`'s mutex, `newTransport`/`start`, `sendSpec` from `Transport.Send.spec`).
(3) Independent of (1)-(2): kvcheck's `checker.{conf,reconfigure,disrupt}`, `Gen`/`Model`, `Check` over lintest,
the minting laws; `PutConfChange`.

## The file invariant from the generation's boot (2026-11-22, branch `kvnet-proof`)

Raft's `RestartNode` update now takes and gives back `notCrashed` (ledger 2026-11-22, raft's
`RestartNode`; `restartAu_nc` for clients that do not need it). kvnet's side (ledger 2026-11-22, kvnet's
`StartNode`), as built:

- `KdFileNames` (`Defs.lean`): a generation's file names, allocated at its boot: `durable`'s `γd`, the file
  `df`, its roots `fR`, the writer's variable `wr` (per generation: `KdNames.wr` is no longer used, left in
  `Store.lean`), the invariant's crash token `tk`, raft's arm `x`. `KdDmuNames.fl` holds them.
- `kdFileInvK γ id fl` := `inv (∃ S s pb, durSt fl.γd s ∗ ghostVar fl.wr ½ (S, s, pb) ∗
  ((raftState S ∗ kdFileState γ id fl.x S s pb) ∨ crashed ∗ token fl.tk))`. The pending batch `pb` carries its
  node (`KdWv`'s `Option (GName × RaftState × Qp × NodeH)`), and its record holds `nodeArm n γ x` (what
  `readyCrashEnter` needs), so the invariant names no node. `isReplica` keeps `nodeArm n γ ph.fl.x`.
- Openers: `kd_writeAU`'s rename update (no token) moves only `durSt` and the writer on the crashed side,
  dropping the batch; its sync update, `dmu_close_enter` and `kv_restartAu` (`StartLemmas.lean`) refute the
  crashed side with `notCrashed` (`notCrashed_or_crashed`).
- `kd_file_alloc` (`BootLemmas.lean`): the invariant, the writer's other half and the token, from `durSt`
  outside a window, `raftState` and `fileHolds`. `kvStart γ vs dir id fl qc` is what `StartNode` starts from
  (the invariant already allocated, the writer's half, `fileHolds`, `nodeVacantA γ id fl.x`).
  `kd_boot_choose` takes the record's arm.
- `StartNode.spec`/`Run.spec`/`RunNode.spec`: the start resource is `S id dir opts M`, `StartNode` owns
  `cfg.Addrs ↦$□ M`; `RunNode` gives `S` at every `M` with `addrMapOk (splitAddrs addrs) M` (`Addrs.lean`), the
  loop's map shown to be exactly that.

Still to do for the crash frame (task 4's): the crash obligation's lemma (open `kdFileInvK` with `tk`, take
`raftState` and `kdFileState` (under a later: the next generation strips it at its first step, or a credit
kept with the token), run `durInv_crash` with `durSt`, close with `crashed ∗ token`), then `kd_boot_choose`
and `kd_file_alloc` for the next generation.

### Handoff (2026-11-22, second session on `kvnet-proof`)

- Commit `657f10a456`: raft's `RestartNode` change (spec, `raft_restart`, clients, copies regenerated and
  `--check`ed). Built: the edited modules (`lake build` of `RestartNode`, kv `StartCluster`, kvdurable
  `Cluster.start`, kvreconf `Cluster.startNew`/`StartCluster`, the server's `newRaftNode`: 3679 jobs, green). The
  full leaf build (80 leaves of `etc/importers.py --leaves`, ~7900 jobs: every `Link`/`Results` above raft's
  `Api`) reached 7874/7900 with no proof error but was killed twice by the machine's memory pressure (one
  unrelated module, `rpctypes.InitLinked`, OOM-killed). Not yet done: finish that build, regenerate
  `interface/` (`etc/gen-interface.py etc/api/raft.txt`: `Spec/.../RestartNode.txt`, `Proof/.../RestartNode.txt`,
  `Linked.txt` move), `etc/tier-check.py --check`, the STATUS entry (text in the session's report), then the land request.
- The WIP commit after it: the section above, **unbuilt and unchecked** (written while the build ran). Check
  with `etc/lean-check.py` in order: `Defs`, `DefsLaws`, `PersistLemmas`, `RunDmu`, `BootLemmas`, `StartLemmas`,
  `Replica__persist`, `newReplica` (spec, proof), `Addrs`, `StartNode`/`Run`/`RunNode` (specs, proofs); then
  `lake build KvNet`. Then `StartNode`'s proof (template kvdurablenoax's `Cluster.start`; `kv_restartAu`
  replaces `kd_restartAu`).

### The WIP checked and built (2026-11-22, third session on `kvnet-proof`)

`lake build KvNet` 3018 jobs green; `tier-check`, `copy-part --check`, `gen-init --check` pass; no axiom or
`sorry`. What changed against the WIP's design:

- **The batch record names its node existentially.** `NodeH` is in `Type 1` (its names hold `Type 1` data), so
  it cannot be in the writer's ghost variable (`KdWv`). `KdWv`'s batch is `Option (GName × RaftState × Qp ×
  GName)`: the last name `γr` is a saved proposition. The record is `∃ n, kdBatchRec γ id x S S2 q γb n ∗
  savedPropOwn γr □ (kdBatchRec … n)` (`Defs.lean`). `kd_writeAU` (`PersistLemmas.lean`) allocates `γr` at the
  rename for the writer's node; at the sync the saved proposition's agreement moves the record to the writer's
  node under a later, so the lemma takes **two** later credits (`persist` takes `lc := 2`, its `run` variant
  `lc := 3`). The callers' batch (`kdPendIn γ id n S pb`, `pbTarget`, `pbQ`, `kdRunKeep`, `kdPendOut`) is back to
  the three-tuple of before the WIP; `pbW γr` makes the writer's four-tuple. `kd_boot_choose` opens the record's
  existential (it needs no agreement).
- `fileHolds_persistent` moved to `DefsLaws.lean`. `addrMapOk`'s binder renamed (`as` is a keyword).
  `RunNode`'s `split_ifs` (Mathlib, not available) replaced by `by_cases`.
- The ledger entry the WIP cited (kvnet's `StartNode`) was missing; written.
- **`StartDefs.lean`**: `kvNodeStart γ vs id dir opts M`, the `S` `StartNode`'s proof is to instantiate:
  `kvStart` (the boot), `kvStartGlobals γ` (kvdurable's `isClusterC` facts: `dup`, no bootstrap log, untraced,
  no snapshot directories, no data bound, `readyFits`, `kdStorInv`, `context.isClosedchanInit`, the globals
  `net.errTimeout` and `poll.ErrDeadlineExceeded`), `kvPeerAddrs γ id M` (`newTransport`'s premise at `kvFacts γ
  (fun _ => True)`), `kvOptsOk opts` and `vs = bootVoters opts.Voters`.
  **A gap to settle at the top level**: `kvOptsOk` has `MaxInflightMsgs < 2^62` (raft's `RestartNode`), but
  `ValidCluster` checks only `< 2^63`: either the top-level statement takes it as a premise (the concrete
  corollary fixes it anyway) or `ValidCluster` (Go, ours) is tightened and retranslated.

**`StartNode`'s proof, what is left to write** (template kvdurablenoax's `Cluster.start`, 526 lines; this
order follows the Go code):
1. the boot `ConfState` loop (`boot.Voters = append(...)`, ids `1..Voters`: `ownCSM bp □ (bootCS vs)`), and
   `&Stats{}` (`isStats`: allocate the mutex with `statsInv`);
2. `FileOf`; `newStorage`; `durable.Read` (spec `WalTester/Spec/.../durable/Read.lean`: import its KvNet
   copy, `KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read`, and rerun `etc/copy-part.py
   --part KvNet`), its update over `kdFileInvK` (`durSt` is outside the crash disjunction, so no `notCrashed`
   is needed; the writer's half pins `cur`, and `kvStart`'s `fileHolds γ S cur` gives the file's facts:
   simpler than kvdurable, which read the facts from its invariant);
3. `openStorage` or the empty storage, `MemoryStorage.Snapshot`, the replicated state, `FirstIndex`,
   `Applied` (`oneIn`/`below`), as in `Cluster.start`;
4. `newTransport` (from `kvPeerAddrs`), the `raft.Config` literal (`ConfigValid` from `kvOptsOk`, ID ≠ 0 from
   `1 ≤ id`; the IDs `2^64-1`, `2^64-2` excluded by `id ≤ γ.max`), `quietLogger{}` (restate
   `qLogger_isLogger`), `RestartNode` with `kd_restartStorage`, `kv_restartAu` (no `restartAu_nc`: the update
   takes the token), `nodeVacantA γ id fl.x`;
5. `t.start(node)` (`kv_stepLaw`, `snapLoc id = none` from `kvStartGlobals`);
6. `tick`, then `newReplica` with `t.Send`'s `sendSpec γ id` — **a lemma still to prove**: from
   `Transport.Send.spec`, `isTransportCore`, `isPeers` (persistent), each message's `msgOwn … ∗ sentMsg ∗
   msgCredits` gives `sendElem (kvFacts …)` (`msgPtsC` from `msgOwn`, `MsgWf`, the frame's length `< 2^63`,
   `□ msgCredits` by `msgCredits_copy` with `dup`);
7. the post: `isNodeS` (the `Node` struct's fields, `rep r id` = `isRep` from `newReplica`'s `isReplicaR`,
   `isTransportCore`) and `kv_confLaw`.
Then `Run`/`RunNode` need no change (they are generic in `S`); the top level instantiates `S := kvNodeStart γ vs`.

## `StartNode` proved (2026-11-22, fourth session on `kvnet-proof`)

`lake build KvNet` 3028 jobs green. `StartNode.wp_proof γ vs dir` (`StartNode.lean`): `StartNode.spec (kvFacts γ (fun _ => True)) (kvRep γ vs dir)
kvConfRead (kvNodeStart γ vs dir)`, kvdurable's `Cluster.start` over the network, in the handoff's seven steps.
No axiom or `sorry`. What changed on the way (each with a ledger entry of 2026-11-22):

- **`ValidCluster` checks `MaxInflightMsgs < 2^62`** (the coordinator's decision: raft's `RestartNode` needs it,
  `kvOptsOk`): Go (`addrs.go`), `validCluster`, the statement draft's `ClusterConfig.Ok`
  (`notes/kvnet-robust-goal.md`); retranslated, `go test` passes.
- **The transport takes no frame-length bound with a message** (`sendElem`, `qElem`): `run`'s messages carry no
  size bound (`MaxSizePerMsg` is any `uint64`); `runPeer` gets `(encMsg st).length < 2^63` from `putMsg`'s slice.
- **The wire reads a message's entries of any type** (new Go `getMsgEntry`, `MsgEntWf`; `MsgWf` weakened): raft's
  API says nothing of a sent message's entries' types (a forwarded `MsgProp`'s are whatever `Propose` got), so
  `MsgWf`'s `EntWf` was not derivable for `t.Send`'s messages. `getEntry` (the file's) keeps its check.
- **`newReplica`'s post names its node** (`isNodeS` needs the replica's node to be the transport's).
- `kvNodeStart γ vs dir0` takes the directory `kvRep` names (`⌜dir = dir0⌝`), and `kvStartGlobals` has
  `γ.max < 2^32` (raft's ids `2^64-1`, `2^64-2` excluded); `kvPeerAddrs_persistent`.
- New: `SendLemmas.lean` (`msgPtsC_lens`, `ownSnapM_wf`, `sentShape_known`, `sendElem_of_sent`, `kv_sendSpec`:
  `t.Send` is `run`'s `sendSpec` from `Transport.Send.spec`), and in `StartLemmas.lean` kvdurable's storage
  helpers (`startStor`, `kdImgOf`, `memLog_take_le`, ...), `kvCfgOk`, `qLogger_isLogger`, `tick_pos`. The KvNet
  copies of `durable.Read`'s spec and kvreconf's `ClusterLemmas` (`etc/copy-part.py --part KvNet`).

**Next** (the session's tasks 3-4, unchanged): kvcheck's `checker.conf` (a `GetStatus` spec on any bytes, as
`GetConfChange`'s: the protocol puts no obligation on a status answer, so it needs any-bytes variants of
`getConfState`/`getIDs` and `getMap`/`getBytes`, as `getUint64.specAny`; `conf`'s caller only stores `s.Conf`); done: `getBytes.specAny`, `getMap.specAny` (`getBytesAny.lean`, `getMapAny.lean`); left: `getIDs`,
`getConfState`, then `GetStatus` (a shortcut: when the bytes decode, apply the valid-bytes spec, run only the failing
paths by hand), `reconfigure` (`PutConfChange`: the payload bound, `randomChange`'s post), `Check` over lintest
(kvdurable's `DriverLemmas`/`Run` are the template: the porcupine result from the lintest theory); then kvnet's
`Link.lean`, the crash frame (the obligation's lemma: open `kdFileInvK` with `tk`, `durInv_crash`,
`kd_boot_choose`, `kd_file_alloc`), `TopLevelRobustness`, the corollary, non-vacuity, a tcb collection.

## kvcheck's decoders, `conf`, `reconfigure`; the plan for `Check` (2026-11-22, fifth session on `kvnet-proof`)

Proved (no axiom, no `sorry`):
- the any-bytes decoders `getIDs.specAny` (`getIDsAny.lean`), `getConfState.specAny` (`getConfStateAny.lean`:
  the four `getIDs` chained, a nil rest after a failure), and `GetStatus.spec` (`GetStatus.lean`, any bytes: a
  good status's `Conf` is an owned conf state; the two counter loops over `getUint64.specAny`, `f`'s cells and
  the status's `Stats` field through `array_acc`);
- kvcheck's `checker.conf` (the status request, `reqOk` of a status is `True`; the decoded conf state made
  read-only and stored in `lastConf`);
- `PutConfChange` (`encCC o`, `ConfCodec.lean`; `encCC_length`: at most `17 + 16 n`), over raftpb's getters
  (their main-tree specs, copied into the part);
- `checker.randomChange`'s post bounds its changes (`≤ 3`; ledger 2026-11-22), so `reconfigure`'s payload
  meets `checker.request`'s bound; `checker.reconfigure` (premise `∀ pl, F.confOk pl`: `True` at the top).

### `Check`: what the current kvcheck specs cannot give, and the plan

`Check` runs `lintest.Run` with `apply` calling `checker.do`/`read`; `applySpec` hands `apply` a one-shot
update over `libState` (kvdurable's `DriverLemmas.kdAu_of_run` turns it into the store's AU through the
invariant `checkN` and a copy of the client half). The store's operations then need, as kvdurable's
`Cluster.do`/`Read` do:
1. **`do`**: `kd_mint` (needs the store's op counter half `ghostVar γ.r.opn ½ nop`, mints at `nop + 1`,
   **sequentially**), then after the answer `kd_collect` with the ticket `token γp.2` and the saved
   predicate. Today's `checker.do.spec` fires its minting law **outside** the checker's lock, on the
   `issued γ false n` token (numbers issued in order but minted in any order: `kd_mint` cannot), and its
   post `∃ n, F.ansOp d v` drops the ticket. Fix: the checker's lock holds the store's counters
   (`checkerInv` with a parameter `Cnt : Bool → w64 → IProp GF`, or `CheckerNames` holding the store's
   `KdNames`: `ghostVar γ.r.opn ½ a` and, for reads, every replica id's `id ↪[γ.r.rseq] ns` with `ns ≤ b`);
   `fresh` takes the law `∀ a, ⌜uint.Z a + 1 < 2^64⌝ -∗ Cnt w a ={⊤}=∗ Cnt w (a+1) ∗ L (a+1)` and returns
   `L n` (no more `issued`); `do`'s law gives `F.opOk (encodeOp n …) ∗ R n` and its post `∃ n, F.ansOp … v ∗
   R n` (`R n`: the ticket and saved predicate, `£ 1` for `kd_mint` captured in the law from
   `wp_auto_lc`). Or (simpler to link) state `do`/`read` concretely at `kvFacts γ _` with kvdurable's
   `Cluster.do`/`Read` shape (AU in, `Φ` out) and do the minting/collecting in their proofs.
2. **`read`**: linearizable reads need the read slot (`kd_read_start` before minting, `kd_read_take` at the
   answer) and a **prophecy of the answer** (kvdurable's `Cluster.Read` has `primitive.NewProph()` and
   `trusted_proph.ResolveBytes(p, []byte(v))` in its Go source). kvcheck's `read` has none: add them to
   `kvcheck.go` (our own code, as kvdurable's; no-ops in Go; `go.mod` gets gokv's `trusted_proph`),
   retranslate (`etc/goose.py --project kvnet`). The slot's start history `H0` (`kvLb γ H0` = some committed
   `l` with `H0 <+: logHist l`) gives the `l0` for `kd_mint_next`, so the answer's `logHist l0 <+: L` gives
   `H0 <+: L`. The law fires under the lock for every replica id at once (`L (b+1) := [∗list] id, readOk id
   (b+1) key`: the id is chosen after `fresh`; unused contexts are harmless).
3. `Model`/`Gen` (model.go): the same Go text as kvdurablenoax's `check.go`'s; add `Model`, `Gen`, `copyMap`,
   `within`, `hashString`, `hashMap` (and `ModelDefs`) to `etc/copy-part.py`'s `KVNET_REUSED`.
4. `Check` itself: kvdurable's `Run` (wait group over the proposers and the disruptor, the `stop` broadcast,
   `lintest.Run` with `CounterClock`, timeout 0 so the result is `Ok`), plus `SplitAddrs`/`ValidAddrs` and
   the checker's allocation (`addrs`, the mutex with the store's counters).

## kvcheck's `do`/`read`/`Check` proved; the top-level statement (2026-11-22, sixth session on `kvnet-proof`)

Proved (no axiom, no `sorry`; ledger 2026-11-22, "kvcheck's `fresh`/`do`/`read` at the store"):
- **Go**: kvcheck's `read` creates `primitive.NewProph()` before its loop and resolves it with the answer
  (`trusted_proph.ResolveBytes(p, v)`, gokv's, as kvdurable's `Cluster.Read`; no effect in Go). `go.mod`
  requires gokv; project kvnet maps `github.com/mit-pdos/gokv=` to the main tree (`etc/goose.py`).
- **The checker's lock** (`kvcheck/Defs.lean`): `CheckerNames`/`issued` gone; `checkerInv c γ` holds a counter
  predicate `γ : CheckerCnt GF := Bool → w64 → IProp GF` (`γ false nextOp ∗ γ true nextRead`). At the store
  (`kvcheck/StoreDefs.lean`) `kvCnt γ n`: `ghostVar γ.r.opn ½ a` and, for `bootVoters n`, every replica's
  `id ↪[γ.r.rseq] ns` with `ns ≤ b`. `fresh` fires the caller's minting law under the lock and returns `L n`.
- **`do`**: logically atomic at the store (an `AU` over `rkvVal γ`, kvdurable's `Cluster.do` shape): the law is
  `kd_mint` (a credit taken before `fresh`); the loop keeps the ticket and two credits; the answer's `waitP`
  collects the result (`kd_collect`).
- **`read`**: kvdurable's `Cluster.Read` shape: `kd_read_start` at the start (history `H0 = logHist l`), the
  law mints the read at every replica id after `l` (`kv_mint_reads`, `kvReadMinted`: `readOkK` plus
  `readCtxAfter … l`); the answer's `ansReadK` names some `l0`, which is `l` by raft's new
  **`readCtxAfter_agree`** (`Proof/go_etcd_io/raft/v3/ReadCtxLaws.lean`, a new importable module of raft's API,
  `import all InvNode`, listed in `etc/api/raft.txt`, interface regenerated); `kd_read_take` with the prophecy.
  All other kvcheck specs only renamed `CheckerNames` to `CheckerCnt GF` (and lost `[AllG GF]`: kvcheck's
  sections now use `HeapGS`'s, as kvnet's store lemmas do, so the instances agree).
- **`Check`** (`kvcheck/Check.lean`; spec `KvNet/Spec/.../kvcheck/Check.lean`): at the store `γ`, from
  `rkvInv γ`, `rkvVal γ kvEmpty`, `kvCnt γ n false 0`, `kvCnt γ n true 0` (`n` the addresses), the addresses'
  protocols at `kvFacts γ (fun _ => True)`, `connGlobals`, `context.isClosedchanInit`, `receiptBound GF ≤ 2^63`
  and `validAddrs (splitAddrs addrs) voters`: returns (porcupine answers `Ok`). kvdurable's `Run`/`Main`: the
  checker's mutex over the counters, the proposers (`1 + below(3)`) and the disruptor joined by a wait group,
  `lintest.Run` with `CounterClock` over a driver's copy of the store's state (`kvcheck/DriverLemmas.lean`:
  `kvAu_of_run`, `checkN := nroot.@"kvnet_check"`, `clockN`).
- **The top-level statement** (statement only): `KvNet/Spec/.../kvnet/TopLevelRobustness.lean`
  (`raft_kvnet_robust.spec`, `raft_kvnet_robust_example.spec`) over `KvNet/Proof/.../kvnet/TopLevelDefs.lean`
  (`ClusterConfig`, `ClusterConfig.Ok`, `kvnetReplicaProgram`, `kvcheckProgram`, `fsOf`). The agreed text
  (`notes/kvnet-robust-goal.md`) adapted only to `Robust`'s thread bound (`threads := 2^61 + 1`, i.e. none, as
  kvdurable's) and to `MaxInflightMsgs < 2^62`; the trusted instances are `kvcheck.Assumptions` (which
  includes every imported package's, kvnet's and raft's among them) and `net.FieldAssumptions`. The replica
  id is `W64 ((i : Int) + 1)` (an elaboration detail of the draft's `(i + 1)`).
  The main tree's old draft `Proof/.../raft/kvnet/Robust.lean` is still there (CLAUDE.md names it); it goes
  with the proof, together with CLAUDE.md's mention (item 7 of the goal).

### Handoff: what is left for the top-level theorem

1. **kvnet's `Link.lean`.** No `etc/gen-link.py` mode yet. The list-driven modes (`--kvdurable-noax`) need a
   spec with no explicit arguments, but ten kvnet specs are parametric (`Run.spec F rep cf S`, `RunNode.spec`,
   `StartNode.spec`, `Node.{handle,serve,serveClient,status}.spec`, `GetConfChange.spec cf`,
   `Replica.{propose,read}.spec`). The binder-reading generator `etc/link_walfs.py` (`--walfs`/`--durable`/
   `--wal-tester`) already handles specs over model parameters (`PARAMS`) and other packages' linked results
   used as they are (`EXT_LINKS`): a `KVNET` cfg there is the likely route (`PARAMS`: `KvFacts GF`,
   `Loc → w64 → IProp GF`, `GoInterface → List w8 → IProp GF`, the start resource's type; `EXT_LINKS`: KvNet's
   copy of raft-noax's `Link` (copying it pulls ~1000 raft proof modules into the part: ~12 min, 3 GB more),
   KvNet's copy of `WalTester`'s `durable` `Link`, the main tree's lintest and porcupine `Link`s, Perennial's).
   Net's `net` proofs (`Net/Proof/net/`, KvNet copies) have no `Link` of their own: link them directly.
2. **The start resources** (the `Hstart` of Perennial's mixed adequacy, `goose_dist_mixed_crash_adequacy_init`;
   the all-crash `NetFs.kvnet_dist_crash_adequacy` exists in `GooseLang/Ext/NetFs/Adequacy.lean`, a mixed one at
   `kvnetExts` still to add): raft's cluster (`cluster_alloc_nb`, B: global, no bootstrap log, `dup = true`),
   the store (`Store.lean`; `kvdurable`'s `kd_alloc` as the template: `ghostVar γ.r.opn ½ 0`, the `rseq`
   elements of `freshIdsM γ.max 0`, of which `bootVoters n` is the client's `kvCnt γ n true 0`), the protocols of
   every replica address (`addrs_set_proto` with `kvP (kvFacts γ (fun _ => True)) id`/`kvQ …`), per replica
   `kvNodeStart γ vs dir` (incl. the directory, `γ.max < 2^32`: `StartDefs.lean`), and the client's `Check`
   resources above.
3. **The per-generation crash obligation** (`P i L'`): open `kdFileInvK` with `tk`, take `raftState` and
   `kdFileState` (under a later), `durInv_crash` with `durSt`, close with `crashed ∗ token`; then
   `kd_boot_choose`, `kd_file_alloc` for the next generation (`BootLemmas.lean`).
4. `KvNet/Proof/.../kvnet/TopLevelRobustness.lean` (`theorem raft_kvnet_robust : raft_kvnet_robust.spec`, a
   linking module), the example as a corollary (premises by computation: `addrOk` of the five addresses,
   `splitAddrs` of the joined string), a non-vacuity lemma (machine states with an empty root `dir`, `FsInit`),
   and `etc/tcb-collections/kvnet.txt` (roots `raft_kvnet_robust`; axioms only the existing trust base).

## kvnet's `Link`; two blockers for the top-level theorem (2026-11-22, seventh session on `kvnet-proof`)

**kvnet's `Link.lean`** (`KvNet/Proof/.../kvnet/Link.lean`, namespace `Perennial.EtcdGrove.kvnetLink`):
`etc/gen-link.py --kvnet` (`etc/link_kvnet.py`, a new binder-reading generator: `link_walfs.py`'s
rules did not fit, its parameters are WAL-specific and kvnet's specs are instantiated at different
places). Every kvnet and kvcheck proof is linked (140 results), from its binders: callees are the part's
own results (kvnet's, kvcheck's, `Net/`'s `net` proofs, copied; gokv's `ResolveBytes`, the main
tree's) or the linked results of raft-noax's `Link`/`Linked`, `durable`'s `Link` (both copied into the
part: `etc/copy-part.py` now copies a source part's `Link` when the part imports it, and takes the
part's own generated `Link` as a root), lintest's, porcupine's and Perennial's `Link`s. The generic proofs
(`Node.handle`/`serveClient`/`serve`, `Run`, `RunNode`) are linked at the store's parameters
(`kvFacts γ (fun _ => True)`, `kvRep γ vs dir`, `kvConfRead`, `kvNodeStart γ vs dir`: `INST`); the
applications pass `_` for parameters and Lean unifies them. The section has `[KdStor GF]` and
`kdStorageModel` as its `StorageModel`.

**The cost** (the coordinator's question): the raft closure is copied into the part (+773 modules, raft-noax's
proofs). There is no cheaper correct route under the part rules: the linked results' proofs are in the
cone of every theorem that uses them, and a part module cannot import `RaftNoAx.*` beside its own copies
of the same names (the part was built by copying for that reason). Importing `RaftNoAx`'s raft directly
would mean making the part's raft *be* `RaftNoAx`'s (no `KvNet.Code.go_etcd_io.raft`), a redesign of the
part, not worth it for one build of ~800 modules.

**`errors.IsPathErrnoNotExist.spec` moved** to its own module `Spec/errors/IsPathErrnoNotExist.lean`
(with `errIsNotExist`, unchanged), out of the WAL's `ExistCallees.lean`, so that `durable`'s `tryRead` (and
the part through it) does not import the WAL's `fileutil` specs (whose translation the part does not have).
The WAL's, the tester's and `durable`'s `Link`s regenerated (one import each).

**Blocker 1 (trusted semantics; reported on #22, 2026-11-22, with the exact text):** the agreed statement
relies on `Robust`'s `extsInitGlobal`/`extsInitLocal` for "no connection" and "files as on disk", but
`net_semantics`/`fs_semantics` set no `initLocal`/`initGlobal` (Perennial's defaults, `True`). Without them
the statement is false (a starting connection at a replica's address carries forged raft messages).
Option (a), preferred: items 3-4 of `kvnet-robust-goal.md` (`initLocal L _ := L.init`, `initGlobal g :=
g.init` in `net_semantics`; `initLocal st _ := FsInit st` in `fs_semantics`; untrusted `ExtInitCompat`
instances). Option (b): the two facts as premises of the statement. The user's decision.

**Blocker 2 (Perennial; reported on #22):** `StartNode` calls `durable.Read`, whose `tryRead` takes
`errors.IsPathErrnoNotExist.spec`, unproved (Perennial branch `errors-facts`, pending review since
2026-11-14, plus translating `(*fs.PathError).Unwrap` and `syscall.Errno.Is`). kvnet's `Link` carries it as
`h_errors_IsPathErrnoNotExist` in `section links_pending` (`StartNode`, `Run`, `RunNode`).

**Gap 3 (the statement's trusted instances; reported on #22):** `durable`'s proofs need `os`'s trusted
`[os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]` (`TrustedCode/os.lean`, struct-field facts as
`net.FieldAssumptions`), which `kvcheck.Assumptions` does not include: the statement needs both as
instance binders (proposed text on #22). Also: lintest's linked results take `[NaInvG GF]`, so the
top-level's ghost state is `kvnetGF` plus a `NaInvG` slot (kvdurable's `durableGF` has it at slot 11).

`#print axioms` (2026-11-22): `kvnetLink.raft_kvcheck.wp_Check` and `kvnetLink.raft_kvnet.wp_RunNode`
(over `h_errors_IsPathErrnoNotExist`): `propext`, `Classical.choice`, `Quot.sound`.

### Handoff: what is left for the top-level theorem (after the blockers)

1. **Package initializers**: kvnet's and kvcheck's `wp_initialize'` (and their `PkgTable`, as kvdurable's:
   `etc/gen-init.py`, `KVNET_INITS` gets `...raft.kvnet` and `...raft.kvnet.kvcheck`; RunNode's
   precondition needs `isPkgInit kvnet`, `io.EOF`'s and `poll.ErrDeadlineExceeded`'s points-to and
   `context.isClosedchanInit`; Check's `isPkgInit kvcheck`, `connGlobals`, `context.isClosedchanInit`).
   Check that gen-init adds no axiom (`etc/tcb-report.py`).
2. **The bridge**: `Net/Statement/NetFsBridge.lean`'s `robust_of_netFsBoot` (legacy file mode, which is
   enough: each generation switches to the shared mode at its first step, `Fs.wp_osShareE`, as the WAL
   tester's `tBoot0`/`tBootCrash` do) at `GF := kvnetGF` (every kvnet ghost state is `AllG`'s). It imports
   only base modules, so the part can import it as it is (or `copy-part` copies it). Under blocker 1's
   option (a) its `NetFsDeploy` premise follows from `Robust`'s own premises plus the statement's
   (`Nodup`, `addrOk`); a variant without `NetFsDeploy` is a few lines.
3. **The start** (`Hstart`, from `[∗list] a ∈ addrs, addrUnset a`): raft's cluster (`cluster_alloc_nb`,
   global, no bootstrap log, `dup = true`), the store (`kvdurable`'s `kd_alloc` as the template), every
   address's protocols (`addrs_set_proto` with `kvP (kvFacts γ (fun _ => True)) id`/`kvQ …`), the client's
   `Check` resources (`rkvInv γ`, `rkvVal γ kvEmpty`, `kvCnt … false 0`, `kvCnt … true 0`, `addrsProto`).
4. **A replica's generation** (`CrashBootWp`'s `P i L`): global facts (the store, the cluster, the
   protocols) and the generation's files (first: `fsStartRes`; later: the crash's `osTree`), the boot's
   choice (`kd_boot_choose`, done in the crash obligation) and the next file contents. Its WP: switch to
   the shared mode (`wp_osShareE`), `durable`'s boot on the directory (`DurFs.durBoot`), `kd_file_alloc`,
   a fresh `KdStor` registry (`kdStorInv`, per generation: it holds heap points-to), then
   `kvnet.initialize'` and `wp_RunNode γ vs dir` with `kvNodeStart`.
5. **The crash obligation** (`CrashBootWp`'s frame): as the WAL tester's `tester_crash`: open
   `kdFileInvK` with its token, `DurFs.durInv_crash`, `crashRest_treeS` for the next tree,
   `kd_boot_choose`.
6. **The top-level module** (`TopLevelRobustness.lean`, linking): `raft_kvnet_robust` from the above, the
   example by computation (`addrOk` of the five addresses, `splitAddrs` of the joined string), a
   non-vacuity lemma, `#print axioms`, `etc/tcb-collections/kvnet.txt`; then remove
   `Proof/.../raft/kvnet/Robust.lean` and CLAUDE.md's mention of it.

## The extensions' initial states; a crash frame cannot see what a generation's switch allocates (2026-11-22, eighth session on `kvnet-proof`)

**Done** (the coordinator's decisions on #22; landing requested at `792cb1f6c8`):
- Decision 1, option (a). `Net.net_semantics` has `initLocal L _ := L.init` and `initGlobal g := g.init` (D26, `TestFreshProcessNoSocket`). `Fs.fs_semantics` has `initLocal st _ := FsInit st` (`env_fresh_process.go`). Also `net_init_compat`, `fs_init_compat`, `NetFs.kvnetInitCompat`, and `Net.robust_of_netFsBoot_addrs`, which needs only `addrs.Nodup` and `addrOk`.
- Decision 3. Both statements take `[os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]` (ledger entry).
- Decision 2 (`errors.IsPathErrnoNotExist.spec` as a hypothesis of `raft_kvnet_robust_of_errors`): not started.

**Two more statement gaps**, reported on #22 with exact texts, awaiting decision:
- `[log.NewModel]`: raft's initializer calls `log.New`. Raft's `wp_initialize'` takes this class, and so does kvdurable's closed theorem.
- `dir.length < 2 ^ 39`: `durable`'s `DFile.Ok` needs `f.d.length + f.tb.length < 2^40`, and nothing in `FsInit`/`RootsOk` bounds a root's length.

**Unlanded, on the branch:**
- `Fs.osShare_ctx`: `wp_osShareE`'s core, as an update at the extension's interpretation. `wp_osShareE` is now proved from it, with an unchanged statement.
- `Fs.wp_ext_nc_acc`: Perennial's `wp_notCrashed_acc` and `wp_ext_acc` at once.
- `Fs.wp_osShareE_upd`: the switch with the history from a crash-token update, for a history kept in an invariant `inv N (P ∨ crashed ∗ Q)`.
- `KvNet/.../kvnet/TopCrash.lean`, `durFound_crash_legacy`: a replica's file across a crash before its generation switched. It takes half of `osTree` and `durFound`/`durFoundTmp`, plus the crash's `crashRest` in the legacy mode, and gives the same history and contents in the next generation. It is built from `durable`'s `durCrash_name`/`durCrash_tmp`.

All of these are `lean-check`ed. They are only needed by the design below, which is blocked.

**The blocker** (to be decided before going on). Kvnet's generation boots inside its WP:
1. the switch to the shared mode (`wp_osShareE`, at the first step);
2. `durable`'s boot (`durBoot`);
3. `kd_file_alloc`, `nodeVacant_arm`, and a fresh `KdStor` registry.

That is because Perennial's distributed adequacy gives a generation only `P i L -∗ threadTok ={⊤}=∗ WP ∗ crashFrame`, with no access to the extension's interpretation before the WP. This is the known gap "extension state access at generation start, distributed" (`notes/perennial-changes.md`, 2026-11-22; `notes/dist-crash-bridge.md`).

So the crash frame, proved outside the WP, gets what the boot allocated only through an invariant made before the WP. Those resources are `osSharedInv`, `durInv`, `kdFileInvK` and the crash tokens. The design tried here was `inv genN ((genA ∨ genB ∗ token) ∨ crashed ∗ True)`:
- genA: half of `osTree`, `durFound`, `durFoundTmp`, `raftState`, `nodeVacant`, `fileHolds`;
- genB: the switched generation's persistent facts and crash tokens;
- the switch opens it with `notCrashed` (`wp_osShareE_upd`);
- the crash frame opens it, takes genA (`durFound_crash_legacy`) or genB (`durInv_crash`, `crashRest_treeS`, `kd_boot_choose`), and closes it with `crashed`.

**Why it fails:** what comes out of an opened invariant is under a later, and the crash frame has no later credit. `▷ inv …` (`durInv`, `osSharedInv`, `kdFileInvK`) cannot be stripped, and neither can raft's sealed `raftState` (it holds `inv budgetN …`), `nodeVacant` or `kdFileState`'s `kdBatchRec`. A credit deposited by the WP's next step races with a crash before it.

The same later problem exists even with the Perennial change. The crash frame must open `kdFileInvK` (decision C's file invariant) and get `▷ (raftState ∗ kdFileState)`, but `kd_boot_choose` and raft's `nodeCrash`/`readyCrashEnter` take them without the later. The earlier handoff's step 3 ("under a later") left this open.

**Options:**
- (a) Perennial: give the generation the extension's interpretation before its WP (the recorded proposal). Then the boot happens in the frame's context and only `kdFileInvK`'s later is left. For that later, either (a1) Perennial also gives the crash frame a later credit (`£ 1` with `crashed`), or (a2) raft's API gets laws that strip a later given `isCluster` (`▷ raftState γ id S ⊢ ◇ raftState γ id S` from the global budget invariant, and the same for `nodeVacant` and the `kdBatchRec` pieces `readyCrashEnter` takes). (a2) holds only if every invariant inside those predicates is a global one that `isCluster` (or the frame) holds.
- (b) A local copy of the distributed mixed adequacy with both of (a), as `wal-safe` did for one node (`CrashAdequacyAcc.lean`). Several hundred lines of `DistAdequacy.lean`.

Both need a Perennial change or a copy of Perennial's adequacy. Per the task rules, I stopped here and reported on #22.

**Still to do after the decision:** the original handoff's items 1-6 above. Most of the start allocation is straightforward:
- `cluster_alloc_nb`, `confPolicy_alloc`, `joinAuth_join` for replicas past the voters;
- the store, after kvdurable's `kd_alloc`, with `kvCnt … 0` from `rseq` over `bootVoters n`;
- `netProto_alloc` then `addrs_set_proto`.

Also still to do: the package initializers (gen-init's `KVNET_INITS` plus kvnet's and kvcheck's `PkgTable`), the client's `Check` WP, the example (`splitAddrs` of the literal, `addrOk`, `validCluster`), and the non-vacuity lemma (dir an empty root, `FsInit`).

## The boot at the generation's start; the crash with a later credit (2026-11-22, ninth session on `kvnet-proof`)

The coordinator's decisions (posted on #22): `[log.NewModel]` and `dir.length < 2 ^ 39` are in the statement
(ledger 2026-11-22); the adequacy blocker takes route (a): Perennial's branch `crash-genstart` (a PR, not landed)
gives (1) each generation's obligation the node's extensions' local interpretation before its WP and (2) the
crash obligation `£ 1`. kvnet's proof is written against those shapes.

**Done:**
- **Package initializers**: kvnet's and kvcheck's `Init.lean` and their programs' `PkgTable.lean`
  (`etc/gen-init.py`: `KVNET_INITS` gets both, `KVNET_PROGRAMS`, kvnet's `SPECIAL` for `StatNames`); raft's
  `Init.lean` copied into the part (copy-part, from RaftNoAx's). Built.
- **`TopBoot.lean`** (defs), all proved:
  - `kvGen γ id f R` (a generation before its boot: `osInv`, the whole legacy tree with nothing logged and well
    formed, `raftState`, `nodeVacant`, `fileHolds`, `durFound`/`durFoundTmp`) and `kvCrashKeep γ id fl` (what the
    crash keeps: the file invariant and its token, raft's arm token, `durInv` and its token, `osSharedInv`);
  - `kvGen_boot`: at `Fs.fs_interp.localCtx … σ` (kept): `osShare_ctx`, the directory's claim, `durBoot`,
    `nodeVacant_arm`, `kd_file_alloc`, `osCallPerms_root`; gives `kvStart γ vs dir id fl 1` and `kvCrashKeep`;
  - `kvGen_crash`: with `£ 1`: `kdFileInvK` opened (the credit strips the later on its contents, so
    `raftState`/`kdFileState` come out without one: **`kd_boot_choose` needs no new raft law**), `durInv_crash0`
    inside it (masks disjoint: `ndot_sub_diff`), closed on its crashed side, `crashRest_treeWf`,
    `crashRest_treeS`, `kd_boot_choose`: the next generation's `kvGen` (at the next local ghost state);
  - `kvGen_first` (the first generation from `FsInit`'s start resources, the file's two names absent),
    `fileHolds_init`, `kvGen_stor` (`kvGen` names no storage registry: the same at any `KdStor`),
    `kdStor_alloc` (a generation's fresh registry: `KdStor` is per generation, its records name the heap).
- **`TopBridge.lean`**: `CrashBootWpG` and `RobustOfNetFsBootG`, `Net.robust_of_netFsBoot_addrs` in the proposed
  shape (the fs component of the local interpretation; `£ 1` in the crash obligation), as a `Prop` for
  `raft_kvnet_robust_of_errors` to take until the Perennial PR lands.
- **`TopStart.lean`** (defs): `kvnet_store_alloc` (global ghost state only: raft's cluster by `cluster_alloc_nb`,
  the conf policy, the store's invariant, the snapshots' registry, `readyFits`, every id `1..n`'s `raftState`/
  `nodeVacant` by `joinAuth_join` past the voters, the client's `rkvVal`, the op counter half and the read
  sequence numbers; needs `receiptBound GF ≤ 2^61`), `kvnet_addrs_alloc` (after `netProto_alloc`'s `regCtx`), and
  the conversions under a `HeapGS` (`kvnet_kdCluster`, `kvnet_kvCnt_op`/`_read`, `kvnet_addrsProto`,
  `kvnet_peerAddrs`). `kvFacts`/`kvQ` are defined over `HeapGS` though they read only global ghost state: the
  allocation uses global restatements `kvFactsG`/`kvQG` (`kvFacts_eq`, `kvQ_eq`: `rfl`).
- **`TopPkg.lean`**: `connGlobals_of_net`, `kvnet_pkg_deps`, `kvcheck_pkg_deps` (with Perennial's
  `context.isClosedchanInit_of_init`).
- **`TopPure.lean`**: `kvDFile` (`⟨dir, J, "replica-" ++ itoa id⟩`) with `kvDFile_ok`/`kvDFile_name`;
  `rootForm_of_fsInit`, `fsInit_entry_none` (the empty-directory premise to the tree's entries);
  `splitAddrs_intercalate`, `validAddrs_of`, `validCluster_of`, `replica_id`, `kvOptsOk_of_clOk`. Every premise was
  derivable from the statement: no gap.
- **`TopClient.lean`** (linking, `etc/tier-linking.txt`): `kvcheck_wp_program`, the client's program's WP from the
  store's client resources and `ownGoState ∅`.
- **`ReplicaLinked.lean`** (linking): `kvReplica_wp` (init, then linked `wp_RunNode` over
  `errors.IsPathErrnoNotExist.spec`) and **`kvRep_gen`**: a replica's generation in `CrashBootWpG`'s body shape (at
  the generation's registry `KdStor`, its invariant given): at the fs local interpretation, `kvGen_boot`, then the
  WP and the crash obligation (`kvGen_crash`) back to the next generation's `kvGen`. `#print axioms kvRep_gen`:
  Lean's three and **`path.filepath.opaqueInitsOk`** (the existing trust-base axiom of `filepath`'s untranslated
  variable initializers, `Proof/path/filepath/Init.lean`; `durable`'s initializer reaches it, kvnet's closure through
  `WalTester/`'s bodied `durable`). The top theorem will rest on it; kvdurable(-noax)'s does not (its `durable` is
  trusted).
- `kvnetGF` has a `NaInvG` slot (8), for lintest's linked results.

### Handoff: what is left for `raft_kvnet_robust_of_errors`

`theorem raft_kvnet_robust_of_errors (Hb : RobustOfNetFsBootG) (Herr : ∀ hG, errors.IsPathErrnoNotExist.spec) :
raft_kvnet_robust.spec`, a linking module (`KvNet/Proof/.../kvnet/TopLevelRobustness.lean`, name it so), at
`GF := kvnetGF`:
1. Apply `Hb` with `addrs := replicas.map (·.1)` (`Nodup`, `addrOk` from the premises).
2. `Hstart`: `netProto_alloc` (the `NetProtoGS`), `kvnet_store_alloc` (n = replicas.length, v = cl.voters),
   `kvnet_addrs_alloc` at `kvFactsG γ (fun _ => True)`; split the per-id `raftState`/`nodeVacant` list by index.
   `Pc i L := ∃ k : KdStor GF, (letI := k; persistent globals ∗ kvGen γ id (kvDFile dir J id) R) ∗ ownGoState ∅`
   with `J` the root ino of `dir` on machine `i` (the premise `dir ∈ roots`), `R` that machine's roots; the first
   generation by `kvGen_first` (`fsStartRes`'s `osInv` and `osTree`, the file starts dropped; `fsInit_entry_none`
   at the file's two names: export `NameOk` of `kvDFile`'s `b`/`tb` from `TopPure`). `Ps 0 :=` the client's pieces.
3. `CrashBootWpG (kvnetReplicaProgram …) (Pc i)`: per `L`, substitute `lctx` (as preface's `Results.lean` does),
   `kdStor_alloc` a fresh registry `k'`, move `kvGen`/`kdCluster` from `k` to `k'` (`kvGen_stor`; `kdCluster` the
   same by unfolding), then `kvRep_gen` at `k'` (premises from `TopPure`), and wrap its crash part into `Pc i L'`
   (∃ `k'`). The thread token is dropped.
4. `StableBootWp (kvcheckProgram …) σc (Ps 0)` from `kvcheck_wp_program` (`lctx` substitution; `validAddrs_of`,
   `receiptBound ≤ 2^63` from `Hstart`'s bound).
5. The Link's section instances (the imported packages' `Assumptions`) from `kvcheck.Assumptions`.
Then `raft_kvnet_robust_example` by computation, a non-vacuity lemma, `etc/tcb-collections/kvnet.txt`, and
removing `Proof/.../raft/kvnet/Robust.lean`. `CrashBootWpG` follows PR mit-pdos/perennial#683's exact shapes
(`threadTok -∗ ∀ w, extsLocalCtx w ={⊤}=∗ …`, the crash's `… -∗ ownGoState ∅ -∗ £ 1 ={⊤}=∗ P i L'`;
`HasExt.localCtx_get` takes the fs component; a clone is at `.lake/perennial-genstart`). When #683 lands: prove
`RobustOfNetFsBootG` in `Net/Statement/` from the new adequacy (the generation's `extsLocalCtx` projected to the
fs component by `HasExt.localCtx_acc`) and drop the hypothesis; adjust `CrashBootWpG` to the exact shapes.
