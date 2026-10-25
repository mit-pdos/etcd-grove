# Verification Artifacts for `etcd-io/etcd#21744`

This directory contains the Go reproduction tests and execution log for the findings identified while verifying [`etcd-io/etcd#21744`](https://github.com/etcd-io/etcd/pull/21744) (`server, e2e: auto-promote learners that have caught up with the leader`, head `b3a94fda4d5d860dfbf4ef9491fcb9c05264fea0`).

## Contents

- [`auto_promote_verify_test.go`](./auto_promote_verify_test.go): Unit/reproduction tests in `package etcdserver`:
  1. `TestVerifyPR21744_Finding1_MissingReqTimeoutDeadlocksMonitor`:
     - **Part A**: Uses a real `go.etcd.io/raft/v3` `RawNode` to demonstrate that when a second `ConfChange` (such as a learner auto-promotion) is proposed while an earlier `ConfChange` is still pending (`r.pendingConfIndex > r.raftLog.applied`), `ProposeConfChange` returns `nil` (no error) and `stepLeader` rewrites the second `EntryConfChange` in-place into an empty `raftpb.EntryNormal` (`len(Data) == 0`). When `EtcdServer.applyEntryNormal` (`server.go:1980`) applies that entry, `len(e.Data) == 0` returns early without calling `s.w.Trigger(cc.GetId(), ...)`.
     - **Part B**: Runs `s.tryAutoPromoteLearners()` on an `EtcdServer` with a caught-up learner (`id = 2`) when the promotion `ConfChange` is rewritten to that empty `EntryNormal`. Confirms that `ctx := s.authStore.WithRoot(s.ctx)` has no deadline (`_, hasDeadline := ctx.Deadline()` is `false`), `tryAutoPromoteLearners()` remains blocked in `s.configure(ctx, &cc)` past `s.Cfg.ReqTimeout()`, and `s.w.IsRegistered(ccID)` remains `true` (leaking the wait registration).
     - **Part C**: Confirms that even when `s.ctx` is canceled (`context.Canceled`), `s.parseProposeCtxErr(context.Canceled, start)` returns `errors.ErrCanceled` (`!= errors.ErrTimeout`), making `case errors.Is(err, errors.ErrTimeout)` in `tryAutoPromoteLearners` dead code.
     - **Part D**: Confirms the fix: wrapping `ctx` with `context.WithTimeout(ctx, timeout)` causes `s.promoteMember` to return `errors.ErrTimeout` and clean up `s.w`.
  2. `TestVerifyPR21744_Finding2_TransientErrorsCountedAsFailed`:
     - Runs `s.tryAutoPromoteLearners()` when `ProposeConfChange` returns each of the three transient leadership-flip / proposal-timeout errors omitted from the 10-way `switch`:
       - `raft.ErrProposalDropped` (`"raft proposal dropped"`)
       - `errors.ErrTimeoutDueToLeaderFail` (`"etcdserver: request timed out, possibly due to previous leader failure"`)
       - `errors.ErrTimeoutDueToConnectionLost` (`"etcdserver: request timed out, possibly due to connection lost"`)
     - Confirms that all three fall into `default:`, increment `learnerPromoteFailed{ReasonForFailure=err.Error()}`, and log `WARN "auto-promote failed"`.
- [`test.log`](./test.log): Full output of `go test -v -run TestVerifyPR21744 ./etcdserver`.

## How to Reproduce

From the Goose fork worktree `/root/etcd-pr/etcd-21744` (branch `pr-etcd-21744-goose-lean`):

```bash
cp /shared/etcd-grove-pr/etcd-21744/notes/pr-verify/etcd-21744/auto_promote_verify_test.go \
   /root/etcd-pr/etcd-21744/server/etcdserver/auto_promote_verify_test.go
cd /root/etcd-pr/etcd-21744/server
go test -v -run TestVerifyPR21744 ./etcdserver
rm /root/etcd-pr/etcd-21744/server/etcdserver/auto_promote_verify_test.go
```
