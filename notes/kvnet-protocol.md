# kvnet's wire protocol: what the bytes on a replica's address mean (decision E)

Started 2026-11-21 (claim issue #22; `notes/kvnet-proof-plan.md`, decision E; the part is
`notes/kvnet-part.md`). This file is the design of the layer between kvnet's byte-level specs
(`readFrame`, `writeFrame`, `RequestVia`, `putMsg`/`getMsg`: what was written and read) and the
store's and raft's facts (`sentMsg`, `waitP`, `kvLb`, the read contexts): a **per-address protocol**
in the sense of the net extension's library (`GooseLang/Ext/Net/Proto.lean`), whose meaning is
**persistent** facts only, so that nothing exclusive crosses the wire (a connection may be cut, a
frame read twice by nobody, a request retried elsewhere).

## The library it is built on

`Proto.lean` gives, per address `a`, two protocols set once (`addr_set_proto`, from the
extension's start resources): `addrProto a P Q`, persistent, `P : Proto GF` what dialers write,
`Q` what acceptors write, `Proto GF := Nat → List w8 → IProp GF` (the connection number, the bytes
of one direction). A dialer gets `connEnd cn false P Q [] []` (`dial_au`, the update
`net.DialTimeout.spec` takes), an acceptor `connEnd cn true Q P [] []` (`accept_shared_au`).
Writing `bs` after `W0` needs `□ P cn (W0 ++ bs)` (`write_acc`, the accessor `Conn.Write.spec`
takes); reading gives `recvTokL`, whose protocol fact is `protoPrefix P cn R` one step later
(`read_au`, `recvTokL_elim`): `R` is a prefix of some `ext` with `□ P cn ext`. `sentLb cn s W`
(persistent) is what the other side may cite of a direction (`recvTok_sentLb`, `sendTok_sentLb`).
Because `Q` takes `cn`, the acceptor's bytes may be stated relative to the dialer's on the same
connection: `Q cn ext` may require `sentLb cn false W` of a request `W`.

## The protocols

kvnet's are parameterized by the persistent facts they carry, a record (`KvFacts GF`, in
`KvNet/Proof/.../kvnet/Proto.lean`), so that this layer is independent of the store's and raft's
predicates and of where their invariants live (decision B, below):

```lean
structure KvFacts (GF) where
  msgOk  : w64 → MsgSt → IProp GF          -- a peer frame's message, sent by `src` (persistent)
  opOk   : List w8 → IProp GF              -- a proposed datum is a minted operation
  readOk : w64 → w64 → List w8 → IProp GF  -- (replica id, seq, key): a minted read context
  confOk : ConfChangeIM → Prop             -- a requested change's shape (pure)
  ansOp  : List w8 → List w8 → IProp GF    -- (d, v): the answer of the operation d
  ansRead : w64 → w64 → List w8 → List w8 → IProp GF  -- (id, seq, key, v): a read's answer
  -- every field persistent: `∀ .., Persistent (msgOk ..)` etc. as instance fields
```

Instantiated (later, in kvnet's store layer) at:

| field | at | from |
|---|---|---|
| `msgOk src st` | `sentMsg γ N src st ∗ □ msgCredits γ N st ∗ ⌜st.msg.To' = id a⌝` | raft's `node.Ready` (the messages a `Ready` hands out); `msgCredits` is persistent at a cluster with `γ.dup = true` (`msgCredits_copy`), which TCP's retransmissions need anyway; `snapLocalMsg` is trivial with no snapshot directories (`snapLocalMsg_noDir`) |
| `opOk d` | `∃ γp, d ↪[γ.r.ops]□ γp` | the store's `kd_mint` (kvdurable's `ClientLemmas.lean`); what `Replica.propose.spec` takes |
| `readOk id seq key` | `(id, seq) ↪[γ.r.rmint]□ readCtxB id seq key ∗ isReadCtx γ N (readCtxB id seq key) _ ∗ ∃ l0, readCtxAfter γ N (readCtxB id seq key) l0 ∗ isCommittedLogLb γ l0` | kvdurable's `kd_mint_next` (there by the replica's `readSeqs`; in kvnet the client mints, `seq` its `fresh` number) |
| `confOk o` | `ccTransOk o` | `checker.randomChange`'s post |
| `ansOp d v` | `waitP γ d v` | `Replica.propose.spec`'s post |
| `ansRead id seq key v` | `∃ l0 L, readCtxAfter γ N (readCtxB id seq key) l0 ∗ kvLb γ L ∗ ⌜logHist l0 <+: L ∧ v = kvFold L key⌝` | kvnet's `Replica.read(seq, key)` (kvdurable's `Replica.read.spec`'s post, with the context the client minted) |

**Dialer bytes**, `kvP F a : Proto GF` (prefix-closed: every protocol here is stated as "a prefix
of a well-formed stream", `ProtoPrefixClosed`):

```lean
def peerFrames (F) : List w8 → IProp GF      -- frames of putMsg, each with its fact
  | ... ∃ frames, W = (frames.map (fun st => putB (encMsg st))).flatten ∧ ∀ st ∈ frames, ∃ src, F.msgOk src st

def reqOk (F) (id : w64) : w8 → List w8 → IProp GF   -- (kind, payload)
  | ReqPropose, d   => F.opOk d                 -- d = encodeOp ..
  | ReqRead,    p   => ∃ seq key, ⌜p = u64Le seq ++ putB key⌝ ∗ F.readOk id seq key
  | ReqConf,    p   => ∃ o, ⌜p = putConfChange o ∧ F.confOk o⌝
  | ReqDisrupt, _   => True
  | ReqStatus,  _   => True
  | _, _            => True                     -- (the server answers 0)

def kvP (F) (a : GoString) (id : w64) : Proto GF := fun cn W =>
  ⌜W = []⌝ ∨
  (∃ R, ⌜W = helloPeerB :: R⌝ ∗ peerFrames F R) ∨
  (∃ kind tmo pl, ⌜W = helloClientB :: putB (reqBytes kind tmo pl)⌝ ∗ reqOk F id kind pl)
```

(each disjunct closed under prefixes by taking `W <+: ext` of a full stream in the definition:
`kvP F a id cn W := ∃ ext, ⌜W <+: ext⌝ ∗ full F id ext`, the form `protoPrefix` gives anyway.)

**Acceptor bytes**, `kvQ F id : Proto GF`: nothing on a peer connection; on a client's, one reply
frame for the request the dialer wrote on the same connection:

```lean
def ansOk (F) (id : w64) : w8 → List w8 → List w8 → IProp GF   -- (kind, payload, answer)
  | ReqPropose, d, v => F.ansOp d v
  | ReqRead,    p, v => ∃ seq key, ⌜p = u64Le seq ++ putB key⌝ ∗ F.ansRead id seq key v
  | _, _, _          => True

def kvQ (F) (id : w64) : Proto GF := fun cn ext =>
  ⌜ext = [] ∨ ext = putB [0]⌝ ∨
  ∃ kind tmo pl v, sentLb cn false (helloClientB :: putB (reqBytes kind tmo pl)) ∗
    ⌜ext = putB (1 :: v)⌝ ∗ ansOk F id kind pl v
```

## The laws (what the client and the server use)

- **client_reply** (`checker.do`/`read`, over `RequestVia`): a client that wrote exactly
  `helloClientB :: putB (reqBytes kind tmo pl)` on its end (`sendTok cn false (kvP ..) W`, the
  write it owns) and read `putB (1 :: v)` (`recvTok cn false (kvQ ..) R`) has `ansOk F id kind pl v`:
  the reply's `sentLb` names a request frame, and frames are prefix-free (`putB` is a length
  prefix), so it is the client's own.
- **server_request** (`serveClient`): an acceptor that read `helloClientB :: putB body` with
  `body = reqBytes kind tmo pl` has `reqOk F id kind pl` and `sentLb cn false (...)`, which with
  `ansOk` is what `□ kvQ cn (putB (1 :: v))` needs for its `writeFrame` (via `write_acc`); `putB [0]`
  needs nothing.
- **server_peer** (`Transport.servePeer`): an acceptor that read `helloPeerB :: R ++ putB b` with `R`
  whole frames has, for `b`, some `st` with `b = encMsg st` and `F.msgOk src st` (`getMsg` then gives
  the message, `stepIn_intro` the step).
- **peer_send** (`Transport`'s sender): writing `putB (encMsg st)` after whole frames needs
  `F.msgOk src st`.
- **glue to the byte-level specs**: from `connEnd cn false (kvP ..) (kvQ ..) [] []` (`dial_au`) a
  dialer builds `RequestVia`'s `connRes cn false W Rd` with `W := fun cn s w => sendTok cn s P w`,
  `Rd := fun cn s got => recvTokL cn s Q got` (`write_acc`, `read_au`, and `close_au` for `cAcc`);
  the server side the same from `accept_shared_au` for `readFrame`/`writeFrame`.

## What depends on decision B

The instantiation of `KvFacts` (raft's `sentMsg`, the store's `rkvInv`, `isCommittedLogLb`) names
ghost state that today lives in invariants over a machine's `HeapGS` (`isCluster`'s `nodeTabInv`,
`notes/kvnet-proof-plan.md`, B): kvcheck, on its own machine, cannot open the store's invariant to
mint an operation's slot (`kd_mint`) or a read context (`kd_mint_next`), and a replica cannot hold
another's. So:

- **this layer** (the protocols, their laws, the client's `do`/`read` loops) is stated over an
  abstract `F : KvFacts GF` and abstract minting laws (an update the caller supplies), and is proved
  now;
- **the instantiation** (the table above) and the minting laws' proofs wait for B: the shared
  invariants (the store's `rkvInv`, raft's cluster) allocated at `GooseGlobalGS`, or their
  predicates shown independent of the local ghost state;
- **the addresses' protocols are set at the start** (`addrs_set_proto` over every replica address,
  in the top-level `Hstart`), with `F` the instance: also after B, since `F`'s predicates must be
  meaningful on every machine.

## The client's operations (kvcheck)

`checker.do(kind, key, val)`: `fresh` gives `n` (`issued γc false n`), `EncodeOp(n, ..)` the datum
`d = encodeOp n kind key val`; the caller's minting law turns the issue into `F.opOk d` (once:
`issued` is exclusive; the AU the store's `kd_mint` consumes is the caller's); then `request`s at
random members until one answers `(v, true)`, which `client_reply` turns into `F.ansOp d v`. Spec:

```lean
{{ isChecker c γc ls ∗ (∀ n, issued γc false n ={⊤}=∗ F.opOk (encodeOp n kind key val)) ∗ ... }}
  c.do kind key val
{{ v, RET #v; ∃ n, F.ansOp (encodeOp n kind key val) v }}
```

`checker.read(key)`: per attempt a fresh `seq` and the minting law `issued γc true seq ={⊤}=∗
F.readOk id seq key` at the replica `id` chosen; an answer gives `F.ansRead id seq key v`.
(kvdurable's `Cluster.do`/`Read` then turn these into the AU's `Φ`, by `kd_collect` and the read
slot: kvnet's store layer, after B.)

## Implemented (2026-11-21)

Proved, no axiom or `sorry` (`lake build KvNet`: 2765 jobs), over an abstract `F : KvFacts GF`:

- `KvNet/Proof/.../kvnet/Proto.lean`: `KvFacts` (persistent fields; `confOk` on the payload bytes,
  `PutConfChange` having no pure model yet), `kvFull`/`kvP` (a prefix of a full stream: prefix-closed,
  `kvP_closed`), `kvQ`, `framesOk`, `reqOk`, `ansOk`; the laws `client_reply` (and `client_reply_L`
  from `recvTokL`, `▷`), `server_request`, `server_reply`, `server_noans`, `peer_send`, `server_peer`,
  `putB_cons_prefix` (frames are prefix-free below `2^64`); the glue `kv_connRes` (from `dial_au`'s
  `connEnd` to `RequestVia`'s `connRes`) and `kv_dial` (`Request`'s dial update from `addrProto`).
  The protocols carry explicit length bounds (`putB`'s prefix is injective below `2^64` only).
- `Client.lean`'s `wAcc` now takes the stream the call will write (`T`): the library's `write_acc`
  builds an accessor only for bytes the protocol means; `RequestVia`/`RequestWithin`/`Request` pass
  `T := helloClientB :: putB (reqBytes kind tmo pl)`.
- kvcheck (`kvcheck/Client.lean`: `addrsProto F ls`, each replica address valid with its protocols,
  `isCheckerP`): `checker.request` (an answer gives `▷ ansOk F id kind pl b'`), `checker.randomMember`,
  `checker.do` (`∃ n, F.ansOp (encodeOp n kind key val) v`, from the caller's one-shot minting law),
  `checker.read` (`∃ id seq, F.ansRead id seq key v`, from a persistent per-attempt minting law).
  Partial correctness: the loops retry forever.

Waiting for B: `F`'s instance (the table above), the minting laws' proofs, `addrs_set_proto` in
`Hstart`; then the server side (`serveClient`, `servePeer`, `Transport`) over `server_request`,
`server_reply`, `server_peer`, `peer_send`, and kvdurable's `Cluster.do`/`Read`-style collection.

## The server side (2026-11-21)

Proved over the protocol layer, no axiom or `sorry` (`lake build KvNet`: 2793 jobs), the raft and store
calls as callee hypotheses (as a `Link.lean` passes them): `Stats.add` (a mutex over the counters),
`Transport.dropped`, `Transport.servePeer` (frames → `server_peer` → `getMsg` → the `To` check → the
step law → raft's `node.Step`), `Transport.dial` (`dial_au`, the hello byte through `write_acc`),
`listen` (`Listen` retried), `Node.serveClient` (`server_request`, `handle`, the reply through
`server_reply`/`server_noans`), `Node.serve` (hello dispatch), `Node.handle` (every kind), `Run` (the
accept loop forking `Node.serve`; partial correctness).

**Seams** (discharged after B and the crash law, at `F`'s instance): `stepLaw F γ N id` (raft's
`stepIn_intro`: `F.msgOk src st` and a fresh copy addressed to `id` give `stepIn`), the field
`KvFacts.msgOk_wf` (a peer frame's message is `MsgWf`), the replica predicate `rep`, `confLaw` (the
store's conf policy: `node.ProposeConfChange`'s precondition from the requested change), and the
stated, not yet proved, specs `Replica.propose`/`read` (`F.ansOp`/`F.ansRead`), `GetConfChange`,
`decode` (a weak form until kvdurable's spec imports kvreconf's `Pure`), `PutStatus`, `Node.status`,
`StartNode`. `reqOk` of `ReqDisrupt` now fixes the payload's shape (`EncodeDisrupt`'s).

**Left**: `Transport.enqueue`/`Send`/`runPeer` (a per-peer channel protocol carrying the message and
`F.msgOk`; `select` with `default`, `for range` over the channel), the stated specs' proofs, `RunNode`,
kvnet's `Link.lean`.
