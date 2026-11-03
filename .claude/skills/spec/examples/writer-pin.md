# The writer's pin: the sole writer's observations of a snapshot (2026-11-02, M2's item 37)

Two laws of the sole writer were open (named `sorry`s, `txn/KeyObs.lean`), for the merged snapshot's
window (`etcdserver.mergedCreate_window`): with a view of the backend's data (`backend.viewAt`), the
writer at log `log` sees the `Key` bucket thin of `bucketMap log` (exact with compaction off), and,
with a reader's bound of the compaction-key flag (`fkRd`), no compaction key with compaction off.
mvcc's store held the bucket's view in two places: half in `writerRes` (behind the batch lock's
resource, reached through `lateW`), half in `s.revMu`'s body.

## The plan's route, and why it was not taken

The plan (`notes/m2-storage-plan.md`, Task 4) pinned `writerRes`'s log (a third share of the log's
ghost name) and read the view through `lateW`, which `backend.Snapshot`'s observation gets. But
after `store.Restore`, `lateW` is *unregistered* until the next writer takes the lock: a snapshot sent
in that window sees nothing of the data. The law, stated over `lateW`, was unprovable there.

## The approved spec (candidate 1, approved as first presented)

    writerLoan γ := if kbCmpM γ.kb then True else kbNoCmp γ.kb γ.bucket ∗ kbNoDel γ.kb
    writerPin γ log := bucketView γ ¼ (bucketMap log) ∗ writerLoan γ

- The writer holds a quarter of the view itself (`writerRes` drops to a quarter); `store.Write`
  joins the two quarters into the transaction's half (they agree), `storeTxnWrite.End` splits them
  back. The laws read the pin, not `lateW`: `kvWriter_keyObs` loses its `lateW d.gx` argument.
- With compaction off, the store *lends* the writer the backend's no-compaction token and its
  "nothing deletable" fact, which `NewStore` used to drop (`kbMW` only in compaction mode now); the
  creators take `kbNoDelOff kb`, the restores `kbNoDel (some d')`.
- The pin is threaded explicitly through the plain store's specs (`NewStore`'s post, `store.Write`'s
  pre, `End`'s post, `writeView.Put`/`DeleteRange`, `store.Restore`), and folded into the
  definitions of `watchWriter` and `txn.wlogOwn` above them, so the txn and server texts did not
  change.

Not chosen (presented as the alternative): hiding the pin in `writerFrag`, tied to the writer's log
through the revision tokens' and the log's authorities: fewer spec diffs, a less direct contract
and a harder refactor.

## What it shows

- A law about what a client observes should rest on a share the client holds, not on a resource
  registered on its behalf later (`lateW`): check every window in which the registration is pending.
- A token the implementation would discard (off-mode `kbMW`) is better lent to the client that
  needs it than re-derived.
- Thread a new piece explicitly at the layer that owns it, and fold it into the predicates of the
  layers above when their clients never touch it.
