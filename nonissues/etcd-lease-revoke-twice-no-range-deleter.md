---
upstream: none
checked: 2026-11-07
links: []
blocks-proof: no
---

# lease: a second `Revoke` of a lease panics when the lessor has no range deleter

`lessor.Revoke(id)` closes the lease's `revokec` (`defer close(l.revokec)`,
`server/lease/lessor.go:335` at the pin `673da07c8f`). It returns early when no range deleter is
set (`if le.rd == nil { return nil }`, `:339`), which leaves the lease in `leaseMap`. A second `Revoke`
of the same id finds the lease again and closes `revokec` a second time, so it panics with "close of
closed channel".

**Why not an issue:** a precondition etcd meets. The server always sets the range deleter: `Recover`
and `SetRangeDeleter` are called at boot, before any `Revoke`. The failing test calls the lessor
directly with no deleter (`TestRevokeTwiceNoRd` in `examples/axiomcx/lessormethods`, branch
`axiom/lessormethods`), which is not a way etcd uses it.

## Proof

no: `Revoke`'s spec (`Spec/go_etcd_io/etcd/server/v3/lease/lessor__Revoke.lean:51`) takes the range deleter the lessor holds (`rdOwn γl rd`, `mvcc.rdIs rd …`), so it is set.

## Notes

Found by the axiom sweep, B3-2 (2026-11-07, etcd-grove-56; `notes/axiom-review/lessor-methods.md`).
