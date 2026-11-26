---
upstream: none
checked: 2026-11-25
links: []
blocks-proof: no
---

# etcdserver: a peer's `/members` answer holding `null` panics `bootstrap`

At a first start, `isMemberBootstrapped` sends `GET <peer>/members` to every other member of the initial
cluster and decodes the answer into `[]*membership.Member` (`server/etcdserver/cluster_util.go:98`); a
non-empty list goes to `membership.NewClusterFromMembers` (`:122`), which dereferences each element
(`server/etcdserver/api/membership/cluster.go:101`: `c.members[m.ID] = m`). A JSON `null` element is a nil
`*Member`, so the answer `[null]` makes `bootstrap` (through `NewServer`) panic with a nil dereference.
At the fork pin `e94f33b50`: `examples/axiomcx/bootstrapdist`'s `TestNullMemberAtPeer` (a stand-in server at
the peer address) and `TestProxyNull` (an HTTP proxy, from `HTTP_PROXY`, answering for a non-loopback peer
URL).

**Why not an issue:** input only an untrusted or non-member peer sends: etcd's own peer handler answers
`/members` with the JSON of `cluster.Members()` (`etcdhttp/peer.go:112-120`), never a `null` element, and the
peer URLs are the operator's configuration. A hardening fix would skip nil members.

## Proof

no: the interim axiom `bootstrap.wp_proof_dist` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/bootstrapDist.lean`)
takes the round-tripper contract `etcd_dist.bootRTOk`: every other member's peer address is set to etcd's
peer protocols (`httpAddrAt`, whose only writer is `PeerServe_dist`'s etcd peer handler), and no proxy
variable is set (`noProxyEnv`). The review: `notes/axiom-review/bootstrap-dist.md`.
