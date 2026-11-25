# Narrowing `http.reserve`: it spends the address's pending set (2026-11-25)

**Target.** `axiom http.reserve` (`Proof/net/http/Axioms.lean`, D39a), with `PeerServe_dist`
(`notes/etcd-dist-plan.md` §16.3, the review of 2026-11-24).

**Finding (the PeerServe_dist review, 2026-11-24).** A single-process run holds, per address `pa`, both
`netAddrFree pa` (`addrClaim pa` from `goose_adequacy_start` with the net extension's `addrUnset pa`, which sets
the extension's protocols: `http_addr_set`, `addr_set_proto`) and `httpProtoFree pa` (from `goose_adequacy_start`) (the single-process HTTP registry's right:
`http.reserve`). A one-process program set `pa` to etcd's peer protocols, served etcd's peer handler there
(`PeerServe_dist`), reserved `pa` in the registry with the request protocol `True`, and sent a forged raft
heartbeat through `rafthttp.NewRoundTripper`'s round tripper: the member's raft panics
(`tocommit(1000000) is out of range`; evidence `/tmp/peerforge/`, not kept).

**Old statement.**
```
axiom reserve (a : GoString) (P : Proto GF) (hP : P.srvOk) :
  ⊢ httpProtoFree (GF := GF) a ==∗ httpProtoAt a P ∗ httpProtoOwn a P
```

**New statement.**
```
axiom reserve (a : GoString) (P : Proto GF) (hP : P.srvOk) :
  ⊢ httpProtoFree (GF := GF) a ∗ netAddrPend (hG := hG) a ==∗ httpProtoAt a P ∗ httpProtoOwn a P
```
`netAddrPend a := ∃ _ : HasExt netExt, netPend NG a ∅` (`Proof/net/InvNet.lean`): the address's empty pending
set, the exclusive piece of `addrUnset a` and of `netAddrLeft a` that every law setting the address's
net-extension protocols spends (`addr_set_proto`, `addr_set_proto_tok`; a wildcard's `lis_set_proto` holds the
pending sets of the addresses it takes in `lisUnset`). A narrowing: a stronger premise, the same post (the old
axiom implies the new one by dropping `netAddrPend`).

**What else changed (no other axiom, no premise).**
- `Proof/net/InvNet.lean`: `netAddrPend`, `netAddrRsv a := addrClaim a ∗ ∃ _, addrTok a ∗ netLisTok NG a`
  (`netAddrFree` without the pending set), `netAddrLis a := ∃ _, addrTok a ∗ lisTokInv a`; theorems
  `netAddrFree_split : netAddrFree a ⊢ netAddrRsv a ∗ netAddrPend a` and
  `netAddrLeft_intro : netAddrPend a ∗ netAddrLis a ⊢ netAddrLeft a`.
- `net.Listen.spec` (proved, `Spec/net/Listen.lean`): takes `netAddrRsv addr` (was `netAddrFree`), gives
  `netListenerAt l addr ∗ netAddrLis addr` (was `netAddrLeft`). Callers that set a listened address's protocols
  (`cluster3.StartBridge`, `cluster3.StartMember`, `etcdstart.Serve`) split `netAddrFree` before and rejoin
  `netAddrLeft` after; the peer listeners (`etcdstart.NewMember`, `StartMemberAuth`, `auth3.startMember`,
  `restart.newMember`, `restartN.newMember`) listen with `netAddrRsv` from their bundle.
- The reservations (`netHttp_reserve3`, `netHttp_reserveL`, `alloc3Http`, `alloc3OnHttp`, `memberStartRes_split`)
  take `httpProtoFree a ∗ netAddrPend a` per peer address; `alloc3`, `alloc3On`, `allocN`, `allocNOn` split the
  start bundle's `netAddrFree`. The fresh and restart bundles (`memberFreshRes`, `memberRestartRes`) hold
  `netAddrRsv p ∗ httpProtoOwn p`; the two restart specs (`restart`/`restartN` `newMember.spec`) take `netAddrRsv`.
- The draft `http.ListenerClose_spec` (no user) gives back `netAddrRsv a`.

**Why it closes the route.** After `reserve`, `pa`'s pending set is spent: no `addr_set_proto`/`_tok` at `pa`, so
no `httpAddrAt γ id pa` (it is `addrProto pa (httpPeerSvc γ id)`, and every law that makes an `addrProto`,
`lis_set_proto`/`lis_set_protoD` through `lisUnset` included, spends the pending set), so no
`PeerServe_dist` at `pa`. Conversely `http_addr_set pa` spends the pending set, and `reserve pa` cannot run.

**Fresh review.** See `notes/etcd-dist-plan.md` §16.3 (2026-11-25) for the verdict of the fresh `axiom`-skill
review of `PeerServe_dist` with the narrowed `reserve`.
