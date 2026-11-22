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
