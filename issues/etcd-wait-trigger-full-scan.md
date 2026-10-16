---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22450 issue open: the report (leader apply backlog does not recover; Trigger time rises with the backlog)
  - etcd-io/etcd#22495 pr open: the fix (a min-heap of deadlines in timeList)
  - etcd-io/etcd#22496 pr open: related (queued apply jobs keep the raft log's entries alive: the memory half)
---

# `timeList.Trigger` scans every pending waiter on each apply batch

- **Status**: a performance bug, with a feedback loop. `applyWait.Trigger(appliedIndex)` runs at
  the end of every apply batch and visits every registered deadline, not only the expired ones.
  When the apply falls behind, linearizable reads pile up waiters for future indices, each batch
  gets slower, and the backlog can stop draining (#22450).
- **Where**: at the etcd pin of `etc/goose.py` (`107edf7e4`; same on upstream `main`):
  `timeList.Trigger` (`pkg/wait/wait_time.go:58-67`, `for t, ch := range tl.m { if t <= deadline
  {…} }` under `tl.l`). The caller is `EtcdServer.applyAll`
  (`server/etcdserver/server.go:984`). Waiters are registered by `timeList.Wait` from the read
  path.
- **What happens**: reproduced at the pin by
  `issues/etcd-wait-trigger-full-scan/trigger_scan_test.go` (package `wait`; passes at the pin). A
  `Trigger` that releases nothing costs ~1.5 µs with 100 waiters pending at future indices and
  ~1.4 ms with 100 000. The report measured ~1.2 ms per `Trigger` at the peak, with the gap rising
  from that moment.
- **Expected**: a `Trigger` costing O(released waiters + log pending), so that apply throughput
  does not degrade with the number of pending reads.
- **How the proof handles it**: admitted; correctness only.
  `wait.timeList.Trigger.spec` (`Spec/go_etcd_io/etcd/pkg/v3/wait/timeList__Trigger.lean`) has
  post `True` beyond closing the expired waiters' channels (`isTimeList`), and Perennial's Lean
  port has no cost model. The heap-based fix meets the same spec.
- **Possible fixes**: keep the deadlines in a min-heap and pop only those `≤ deadline` (#22495).
- **Found**: 2026-10-16, by the bug triage of etcd-io/etcd#22450 (`notes/bug-triage/etcd-22450.md`).
