---
upstream: unchecked
checked: 2026-10-27
links: []
---

# client-go's work queue hands one item to two workers after a `Done` without a matching `Get`

- **Status**: an unstated precondition. `Typed[T].Done(item)` is correct only for an item a `Get`
  returned and no `Done` has finished yet. Called for an item that is dirty (added) but not being
  processed — a second `Done` for one `Get`, or a `Done` for an item never handed out — it pushes
  a second copy of the item into the FIFO. The FIFO then holds the item twice, and two `Get`s
  return it to two workers at the same time: the queue's guarantee that an item is processed by one
  worker at a time (the package documentation: "Stingy: a single item will not be processed
  multiple times concurrently") is gone for that item, from then on until both copies drain. The
  API says only "You must call Done with item when you have finished processing it" (`Get`) and
  "Done marks item as done processing" (`Done`); nothing says `Done` must not be called otherwise,
  or that a second `Done` is harmful.
- **Where**: `k8s.io/client-go/util/workqueue/queue.go` at the pinned
  `v0.0.0-20261021054439-569675c57fa3` (unchanged on kubernetes/kubernetes master `a7225301`,
  2026-10-26, `staging/src/k8s.io/client-go/util/workqueue/queue.go:292`), `(*Typed[T]).Done`:

  ```go
  q.processing.Delete(item)
  if q.dirty.Has(item) {
      q.queue.Push(item)   // pushed whether or not item was being processed
      q.cond.Signal()
  }
  ```

  An item that is dirty and not being processed is already in the FIFO (`Add` pushes it), so the
  push duplicates it. `Add` cannot repair this: it dedups on the dirty set only.
- **What happens** (Go test, run against the pin, both fail as described):

  ```go
  func TestDoneWithoutGetDuplicates(t *testing.T) {
      q := workqueue.NewTyped[string]()
      defer q.ShutDown()
      q.Add("a")
      q.Done("a") // "a" queued, not processing: pushed again; q.Len() == 2
      k1, _ := q.Get()
      k2, _ := q.Get()
      if k1 == k2 { t.Errorf("two concurrent Gets both returned %q", k1) } // fails: "a", "a"
  }

  func TestDoubleDoneDuplicates(t *testing.T) {
      q := workqueue.NewTyped[string]()
      defer q.ShutDown()
      q.Add("a")
      k, _ := q.Get()
      q.Add(k)  // added again while processing: dirty
      q.Done(k) // queued again (correct)
      q.Done(k) // second Done: "a" dirty, not processing: pushed a second time
      a, _ := q.Get()
      b, _ := q.Get()
      if a == b { t.Errorf("after a double Done, two Gets both returned %q", a) } // fails
  }
  ```

  The second test is the realistic path: a worker that calls `Done` twice for one `Get` (a
  `defer q.Done(key)` plus an explicit `Done` on an early-return path, a pattern easy to write)
  while an informer event re-adds the key. Afterwards two workers sync the same key concurrently,
  which every controller built on the queue assumes cannot happen (the DaemonSet controller's
  consistency store states it as a precondition, client-go `util/consistency/consistency.go:44`).
- **Expected**: either `Done` documents that it must be called exactly once per `Get` that
  returned the item, or it ignores an item that is not being processed (`if !q.processing.Has(item)
  { return }` before the push, as `Add` checks `processing` before pushing).
- **How the proof handles it**: `Typed.Done.spec` (`Spec/k8s_io/client_go/util/workqueue/
  Typed__Done.lean`) takes the item's token `keyTok γ k`, which only the `Get` that returned `k`
  gives and which `Done` consumes, so a second `Done` (or one without `Get`) is outside the spec.
  The abstract state's invariant `QState.wf` (`Proof/k8s_io/client_go/util/workqueue/Defs.lean`:
  the FIFO has no duplicates and holds exactly the dirty items not being processed) is preserved by
  `QState.done` only for an item being processed (`QState.done_wf`, `Lemmas.lean`).
- **Possible fixes**: the guard above (one line; `Done` of an item not being processed becomes a
  no-op, which also keeps `processing.Len() == 0`'s `Signal` for `ShutDownWithDrain` unchanged), or
  the documentation of the precondition on `Done` and `TypedInterface.Done`.
- **Found**: 2026-10-27, specifying `(*Typed[T]).Done` for the DaemonSet plan's phase 2
  (`notes/k8s-daemonset-plan.md`): the per-key token is what makes `Done` provable.
