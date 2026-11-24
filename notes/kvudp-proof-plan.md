# kvudp: the UDP transport's proof plan (phase 1: specs and invariants, 2026-11-24)

kvudp is kvnet with the replicas' raft messages over UDP datagrams (`examples/raft/kvnet/
udptransport.go`, `nodeudp.go`; `cmd/kvudp`), the clients' requests still over TCP. This note is the
design of its proof as built in phase 1 (every statement and definition compiles; every proof is
`sorry`), and the partition of phase 2 into tasks. The TCP twin and the transport contract
(`PeerTransport.lean`: `ptCtor`, `ptFresh`, `ptSend`, `ptStop`) are the kvnet lead's and unchanged.

Files (all under `KvNet/`, module prefix `KvNet.`; `K` = `.../examples/raft/kvnet`):

* defs: `Proof/K/UdpWire.lean` (pure: the datagram format, chunking, the boot file's contents,
  addresses), `Proof/K/UdpDefs.lean` (ghost state, datagram protocol, representation predicates),
  `Proof/K/UdpBootDefs.lean` (the boot counter's crash-aware invariant);
* a spec `Spec/K/<fn>.lean` and a proof skeleton `Proof/K/<fn>.lean` per Go function (list below);
* the top level: `GooseLang/Ext/NetFsUdp/Adequacy.lean` (the extensions `[netExt, fsExt, udpExt]`),
  `Proof/K/cmd/kvudp/TopLevelDefs.lean`, `Spec/K/cmd/kvudp/TopLevelRobustness.lean` (the statement),
  `Proof/K/cmd/kvudp/TopLevelRobustness.lean` (skeleton).

## The design

**Messages and names.** A message is `putMsg`'s encoding cut into chunks of 479 bytes, each sent as a
fragment datagram (at most 524 bytes: `maxDatagramN = Udp.intactMax`, so it arrives intact or not at
all) naming the message `(from, boot, seq)`. The receiver reassembles by name. Soundness rests on a
name never being reused across the cluster's life: the ghost state records, per name, the one body sent
under it.

**Ghost state** (`UdpNames`, four ghost maps, allocated once at the top level; `UdpDefs.lean`):

| map | elements | meaning |
|---|---|---|
| `msgs : MsgKey ↦ List w8` | `udpMsgAt k body`, persistent | the message named `k` is `body` |
| `toks : MsgKey ↦ Bool` | `udpSeqTok k`, exclusive | the right to record `k` once |
| `ctrs : (f, b) ↦ w64` | `udpCtr f b c`, exclusive | process `(f, b)` used its seq numbers up to `c` |
| `his : f ↦ w64` | `udpHi f hi`, exclusive | replica `f`'s boot numbers handed out are `≤ hi` |

`udpMsgInv γu` (one invariant, `udpMsgN`) holds the four authorities and `UdpMsgOk`: every recorded or
reserved name `(f, b, s)` has `s ≤ ctrs(f, b)`; a reserved name is not recorded; every counter `(f, b)`
has `b ≤ his f`. Recording consumes a token (`ghost_map_delete` on `toks`, `ghost_map_insert_persist`
on `msgs`): only existing Perennial ghost-map lemmas are needed (no own-to-discard update).

**The datagram protocol.** `udpDgOk F γu d` (persistent): `parseDg d = some dg`, and `dg` is an ack
(no claim) or a fragment with `udpFragOk`: the body recorded under `dg.key` is a message's encoding
with its fact (`udpBodyOk`: `body = encMsg st`, `F.msgOk src st`: as a TCP frame carries) and `dg` is
its `dg.index`-th chunk (`FragOf`). `udpAddrInv F γu a` (one per cluster address, namespace
`udpSentN`): `udpSent a ms ∗ [∗list] d ∈ ms, udpDgOk F γu d`. A sender proves `udpDgOk` of what it
sends; `parseDg_length` makes it at most 524 bytes, so `SendOut`'s `Intact` gives `d = bs`; the
receiver's `RecvOut` gives a member of `ms`, so `udpDgOk` of it, and its buffer (524) holds it whole.

**The boot counter** (`UdpBootDefs.lean`). The generation's boot file invariant `udpBootInv γu id bn`
(namespace `udpBootN.@id`) holds `durable`'s client state `s` of the file `BootFileOf(dir, id)`, the
writer's half `ghostVar bn.wr ½ s`, and either `udpHi γu id hi ∗ ⌜BootOk hi s⌝` (every contents a crash
may leave, `cur` and `alt`, hold a number `≥ hi`: `bootVal`) or, once the crash obligation has taken
them with the token `bn.tk`, `crashed ∗ token bn.tk` (as kvnet's `kdFileInvK`). `nextBoot` reads `n`
(the writer's half pins `cur`, so `hi ≤ n`), writes `n + 1`: at the rename `BootOk` holds (`cur = n+1`,
`alt = n`); at the sync (`alt := none`) it opens `udpMsgInv` too, bumps `his id` to `n + 1` and inserts
the counter `(id, n + 1) ↦ 0` (fresh: every counter of `id` is `≤ hi ≤ n`), returning `udpCtr γu id
(n+1) 0`. A crash before the sync leaves `cur` or `alt`, both `≥ hi`; after it `cur = n+1 = hi`. The
crash obligation (`udp_boot_crash`) takes `udpHi` and `s`; `durable`'s crash lemma gives the next
contents `v = cur ∨ alt = some v`, which `bootOk_crash` bounds; the next generation's boot reallocates
the invariant (`udp_boot_alloc`).

**The transport contract.** `udpNet.newTransport`'s spec gives `ptFresh` for the untraced cluster, and
the method value `u.newTransport` meets `ptCtor F γ N id AP` at **any** `AP`: the Go ignores its
`addrs` argument and uses the endpoint's, whose per-address facts `openUDP` put in `isUdpNet`. So there
is no `udpAP` (the design's `udpAP F pid a`, the peer's address with its invariant, is unnecessary):
`startNodeUDP`'s proof uses `ptCtor` at TCP's `tcpAP`, hence the kvnet lead's `start.wp_proof`,
`stopIncarnation.wp_proof`, `kvNodeStart`, `kvStp`, `kv_stepLaw`, `kv_confLaw` unchanged (`kvNodeStart`'s
TCP peer protocols are present in the UDP deployment anyway: the clients still use TCP, so the top level
allocates every address's TCP protocol, as kvnet's).

**Snapshots and acks.** Acks carry no claim; `acked` only closes the waiter's broadcast channel (the
closer is in the endpoint's mutex invariant, `ackWaitOwn`). `ReportSnapshot`/`ReportUnreachable` need
only `isNode` and the untraced cluster (`node.ReportSnapshot.spec`), which `isUdpCore` carries.

## The specs, one line each

Pure (`UdpWire.lean` models):
* `putHeader(buf, ...)`: `buf ++ headerBytes ...`, cap kept.
* `putFragment(...)`: a new slice `fragBytes ...`; `putAck(...)`: `ackBytes ...`.
* `getDatagram(b)`: `parseDg bs`: `some dg` → `true` and `dgOwn d dg`; `none` → `false`.
* `fragments(...)`: slices of `fragsOf ...`, nil iff `fragsOf = []`.
* `parseAddr(a)`: `ok = addrOk a`, and `parseAddrM a = some (ip, port)` when ok.
* `udpAddr(a)`: `ok = addrOk a`; when ok a `*UDPAddr` with `udpAddrAt` and `ValidDest ip port a`.
* `timer(d)`: a bag channel of `Unit`, no fact.

Endpoint (`isUdpNet F γu u id boot`, persistent):
* `nextSeq()`: `false`, or `true` with `udpSeqTok γu (id, boot, seq)`.
* `expectAck(to, seq)`: a broadcast channel (`Unknown`), its closer into the map.
* `forgetAck(seq)`, `acked(from, seq)`: no post.
* `write(to, b)`: `b ↦*□ bs ∗ udpDgOk F γu bs` → sent or not.
* `newTransport(id, addrs, stats)`: `ptFresh F γ N id tv` (any untraced `γ`).

Transport (`isUdpBase` before `start`, `isUdpCore F γu t γ N id n` after):
* `start(n)`: `isUdpBase` and the node → `isUdpCore`; `stop()`: the stop channel's closer.
* `Send(ms)`: TCP's `sendElem F` per message, slice read-only (as `Transport.Send`).
* `dropped(m)`: `msgPtsC` kept (as `Transport.dropped`).
* `writeAll(to, ds)`: `udpDgsOk F γu ds` → bool.
* `runPeer(p)`: `isUdpPeer F p pid` (queue of TCP's `qElem F pid`) → never stuck.
* `sendSnapshot(to, seq, ds)`: `dsl ↦*□ ds ∗ udpDgsOk` → no post.

Receiver:
* `newReassembler(stats)`: `ownReassembler F γu r`.
* `reassembler.add(d)`: `dgOwn d dg ∗ udpFragOk F γu dg` → complete with `body ↦* bs ∗ udpMsgAt γu
  dg.key bs ∗ udpBodyOk F bs`, or not; eviction, `reack`, bounds unspecified.
* `reassembler.remember(...)`: `ownReassembler` kept.
* `udpNet.receive(n)`: `isUdpNet ∗ isNodeS F rep stp nd γ N id` → never returns.
* `udpNet.stepper(n, q)`: `q` a bag of `recvElem F id` (what `Node.stepPeer` takes).
* `udpNet.ack(n, ...)`: the node's stats only.
* `udpNet.handle(n, r, steps, b)`: `b ↦*{q} bs ∗ udpDgOk F γu bs`, `ownReassembler` kept.

Entry:
* `BootFileOf(dir, id)`: `bootFileName dir id`.
* `nextBoot(dir, id)`: `udpMsgInv ∗ udpBootStart γu id dir bn qc` → `udpCtr γu id boot 0`,
  `udpBootStart` back.
* `listenUDP(p)`: `udpAddrAt p ip port ∗ ValidDest ip port a` → `udpConnAt c s a`.
* `openUDP(cfg)`: own address in `M`, every address valid (`ValidCluster`), `udpProcStart` →
  `isUdpNet F γu u cfg.ID boot`. The own-address panic is excluded by `M !! cfg.ID = some a` with
  `addrOk a` (a fact `RunNodeUDP` has from `ValidCluster`): no new premise.
* `startNodeUDP(cfg)`: `StartNode.spec`'s shape plus `udpProcStart` → `isNodeS ∗ confLaw ∗ isUdpNet`.
* `RunUDP(cfg)`: `Run.spec`'s plus `udpProcStart`; `RunNodeUDP(...)`: `RunNode.spec`'s, with
  `S ... M ∗ udpProcStart F γu id dir M` for every `addrMapOk` map.

## Key lemmas (stated, `sorry`)

`UdpWire.lean`: `parseDg_fragBytes`, `parseDg_ackBytes`, `parseDg_length`, `parseDg_kind`, `fragsOf_ok`,
`fragsOf_nil`, `chunks_flatten`, `chunkAt_length`, `fragBytes_length`, `ackBytes_length`,
`parseAddrM_ok`. `UdpBootDefs.lean`: `udp_boot_alloc`, `udp_boot_crash` (`bootOk_crash` is proved).
To add in phase 2 (in `UdpDefs.lean` or a `UdpLemmas.lean`): `udp_seq_fresh` (nextSeq's token from
the counter), `udp_record` (token → `udpMsgAt`), `udp_boot_bump` (the sync's ghost step),
`udpDgOk_recv` (what `RecvOut` gives, read into a 524-byte buffer, is `udpDgOk` of the datagram whole),
`udpDgOk_send` (`Intact` keeps `udpDgOk`), and the reassembly lemma (the chunks of one name, all
`udpMsgAt`-agreeing, flatten to the body).

## The Link wiring (later: the kvnet lead's transport and node proofs are still landing in `Link.lean`)

Each `Proof/K/<fn>.lean` declares `<fn>.wp_proof` taking its callees' specs (the files' hypotheses).
For `etc/gen-link.py` (KvNet's list, `etc/link-lean-first-kvnet*.txt` or wherever the TCP functions
are listed): add the 35 functions `putHeader, putFragment, putAck, getDatagram, fragments, parseAddr,
udpAddr, timer, udpNet.{nextSeq, expectAck, forgetAck, acked, write, newTransport, receive, stepper,
ack, handle}, udpTransport.{start, stop, Send, dropped, writeAll, runPeer, sendSnapshot},
newReassembler, reassembler.{add, remember}, BootFileOf, nextBoot, listenUDP, openUDP, startNodeUDP,
RunUDP, RunNodeUDP`. The parametrized ones are linked at kvnet's instantiation: `udpNet.receive`,
`udpNet.stepper` at `F rep stp` (as `Node.servePeer`); `startNodeUDP` at `(γ vs dir)` (as
`StartNode`: `kvFacts γ (fun _ => True)`, `kvRep γ vs dir`, `kvConfRead`, `kvStp γ vs dir`,
`kvNodeStart γ vs dir`, callees `startNode`, `start`, `stopIncarnation` at the same, `openUDP`,
`udpNet.newTransport`); `RunUDP`, `RunNodeUDP` at `F rep cf S` (as `Run`, `RunNode`). Perennial callees
not yet hypotheses (phase 2 adds them): `time.Sleep`, `time.AfterFunc` (as `listen.lean`, via
`Perennial.Proof.time.Link`), `littleEndian.Uint32/Uint64`, and `littleEndian.AppendUint32` (**no spec in
Perennial**: a Perennial change, `notes/perennial-changes.md`).

## Design risks

1. **Two durable files in one directory.** `durable`'s boot (`DurFs.durBoot`) takes the whole claim on
   the directory's names (`osNames f.J (.except [])`); kvnet's `kvGen_boot` gives it to the storage
   file. The boot counter needs a second file in the same directory: a `durBoot` on the claim of its
   two names only (`.only [f.b, f.tb]`; it splits internally already, `osNames_split`), and kvnet's
   `kvGen`/`kvGen_boot`/`kvGen_crash` generalized to leave the other names' claim (and `durFound` of the
   boot file) to the caller. A change to `WalTester/`'s `durable` (`Boot.lean`) and to the kvnet lead's
   `TopBoot.lean`; the call permission of the root is split between the two (`qc`).
2. **`littleEndian.AppendUint32`** has no Perennial spec (`putHeader`, `putFragment`).
3. **The reassembler's `chunks[i] != nil`.** `ownPartial` tracks which chunks arrived by a ghost list
   (`got`), tied to `c ≠ slice.nil`; the proof must show a chunk `getDatagram` copies is non-nil
   (`append([]byte(nil), nonempty...)`).
4. **`received`'s channel.** `isChanBag` needs `Pos.Countable received` (defined in `UdpDefs.lean`) and
   `IntoValTyped received`; the generated `IntoValTypedUnderlying` should give it.
5. **`GooseLang/Ext/Udp/Specs.lean`** did not compile on this branch (`recvVal` without `[GooseExts]`):
   fixed here with the two instance binders (the UDP extension's owner should take the fix).
6. **Datagrams from outside.** The address invariants hold only the deployment's datagrams: the
   statement's closed-world assumption (prose, as kvnet's TCP one).

## The partition (riskiest first; disjoint files)

1. **Boot counter** (`nextBoot`, `BootFileOf`; `UdpBootDefs.lean`'s `udp_boot_alloc`, `udp_boot_crash`,
   the sync's ghost step): the crash-aware invariant over `durable`'s two atomic updates.
2. **Top-level generation and crash** (`cmd/kvudp/TopLevelRobustness.lean`, `NetFsUdp/Adequacy.lean`'s
   adequacy and projections; with risk 1's `durable` and `TopBoot` generalization): the global
   allocation of `UdpNames` and the address invariants from `udpStart`.
3. **Reassembler** (`reassembler.add`, `reassembler.remember`, `newReassembler`; the reassembly lemma).
4. **Receiver** (`udpNet.receive`, `udpNet.handle`, `udpNet.stepper`, `udpNet.ack`; `udpDgOk_recv`).
5. **Sender** (`udpTransport.runPeer`, `sendSnapshot`, `writeAll`, `udpNet.write`, `udpNet.nextSeq`; the
   record step; `udpDgOk_send`).
6. **Endpoint and transport plumbing** (`udpNet.{expectAck, forgetAck, acked, newTransport}`,
   `udpTransport.{start, stop, Send, dropped}`): mirrors TCP's.
7. **Pure helpers** (`UdpWire.lean`'s laws; `putHeader`, `putFragment`, `putAck`, `getDatagram`,
   `fragments`, `parseAddr`, `udpAddr`, `timer`; with risk 2's Perennial spec).
8. **Entry** (`listenUDP`, `openUDP`, `startNodeUDP`, `RunUDP`, `RunNodeUDP`).
