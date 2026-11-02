# The client's `kv.Compact` (2026-10-31)

etcd's client `(*kv).Compact(ctx, rev)` (`client/v3/kv.go`): one gRPC call to a member, whose
server proposes the compaction through raft; mvcc answers `ErrCompacted` at or below the
compaction revision and `ErrFutureRev` above the current revision. The server's spec
(`EtcdServer.Compact.spec`) excluded `ErrFutureRev` by a premise: a certificate of the member's
own store that the revision is reached (`srvRevLb E.γ r`). The client has no such certificate.

## The user's first choice: keep the server's premise, give the client a certificate

Two designs were put to the user: (a) the client gets a persistent certificate of a reached
revision from a `Put`'s reply and passes it to `Compact`; (b) the server models `ErrFutureRev`
(a no-op) and `Compact` takes no revision premise (stronger, but it reverses an approved server
design). The user chose (a).

## The first version (candidate 1)

```lean
-- the certificate: today's server-side `cmpReach`, renamed
def kvRevLb (γk : KVNames) (r : w64) : IProp GF :=
  iprop(∃ l : mvcc.Log, kvCert γk l ∗ ⌜sint.Z r < l.length⌝)   -- kvCert: γk.cok's map

abbrev kv.Compact.spec : Prop :=
  ∀ kv γ dup ctx ctx_desc (rev : w64) opts_sl,
  1 ≤ sint.Z rev → γ.cmp = true →
  {{ isPkgInit … ∗ isKv kv γ dup ∗ ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗
      ⌜opts_sl.len = W64 0⌝ ∗ kvRevLb γ rev }}
    kv.Compact(ctx, rev, opts_sl)
  {{ resp err, (⌜err = nil⌝ ∗ ∃ m, compactRespMsg resp m) ∨ (⌜err ≠ nil ∧ resp = null⌝ ∗ kvErr err) }}
```

with `kv.Put.spec`'s post gaining `kvRevLb γ m.hdr.revision`, and `isKv`'s tie between the
client's names and its members' widened from the state name to the certificate map:
`∀ x ∈ ms, x.γr.kv.st = γ.st ∧ x.γr.kv.cok = γ.cok ∧ x.γr.kv.cmp = γ.cmp`.

## Review 1, and the user's second choice

The spec reviewer found the tie unsatisfiable for a client of several members: every member's
store has its own certificate map (`Alloc3` allocates `cok₁ cok₂ cok₃`; `kvCertInv` owns its
map's authority), so no single `γ.cok` equals them all. The certificate a `Put` returns is the
replying member's; a later `Compact` may reach another member. Only single-member producers
existed, so nothing failed yet: the design would have broken at the next step (multi-member
clients). Options: (a1) define the certificate over what the members share, the cluster's
requested raft log and the KV model; (a2) keep the tie, recorded as a single-member restriction;
(b) after all. **The user chose (a1).**

## The approved spec (candidate 3)

```lean
structure KVNames where
  …
  rlog : GName   -- the cluster's requested raft log (SrvRaft.log); kvInv ties γk.rlog = γ.raft.log

def kvSame (γk γk' : KVNames) : Prop :=   -- two names of one cluster's KV (member's cok, hi aside)
  γk.st = γk'.st ∧ γk.c0 = γk'.c0 ∧ γk.ch0 = γk'.ch0 ∧ γk.log0 = γk'.log0 ∧
    γk.rlog = γk'.rlog ∧ γk.cmp = γk'.cmp

/-- etcd's KV `γk` has reached revision `r`: the cluster's requested raft log has a prefix whose
KV model is longer than `r`. -/
def kvRevLb (γk : KVNames) (r : w64) : IProp GF :=
  iprop(∃ L₀, monoListLbOwn γk.rlog L₀ ∗ ⌜sint.Z r < (kvModel γk L₀).length⌝)
```

`kv.Compact.spec` as above; `isKv`'s tie `∀ x ∈ ms, kvSame x.γr.kv γ` (its producers take one
`kvSame` hypothesis in place of `hst`); `kv.Put.spec`'s post gains `kvRevLb γ m.hdr.revision`
(last); `reqPropOk`'s compaction form and `EtcdServer.Compact.spec` take `kvRevLb` (the latter in
place of `srvRevLb E.γ r`: weaker, so stronger); the members' registrations gain `Compact`
(`etcdCompactSpec`, the bound at the member's names, moved by `kvRevLb_same`).

Review 2 confirmed the log is one per cluster (`{γ with reg}` members), that the bound is what the
commit step needs (`kv_prop_au_cmp` already reduced `cmpReach` to it), and placed the new tie in
`kvInv` rather than the server's view (no new `NewServer` premise).

## What it teaches

- A certificate a client carries from one call to the next must hold at every member the next
  call may reach: build it from the state the members share, not from one member's ghost state
  ("A client's certificate is the cluster's", PRINCIPLES.md).
- Check a tie against the multi-member allocation, not only today's single-member producers.
