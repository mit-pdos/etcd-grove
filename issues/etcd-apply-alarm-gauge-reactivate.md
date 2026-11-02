---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# server: the alarms gauge counts an alarm activated twice twice, and stays at 1 after it is disarmed

The `etcd_debugging_server_alarms` gauge counts alarm activations, not alarms: when the same alarm
(say `NOSPACE` for a member) is activated twice, the gauge reads 2 while the member has one alarm,
and after the alarm is disarmed it reads 1 until the member restarts.

**Expected:** the gauge should read the number of alarms set, as its help text says ("Alarms for
every member in cluster"): 1 while the alarm is set, 0 once it is disarmed.

**Impact:** monitoring that alerts on this gauge keeps alerting after `etcdctl alarm disarm`. A
second activation happens without any operator action: a member that runs out of space proposes a
`NOSPACE` activation for every write that fails with "no space" before the first activation is
applied; an admin's repeated `etcdctl alarm` activation does the same. Metric only; the alarms
themselves are correct.

**Reproduction:** `TestAlarmGaugeReactivate` in
[`issues/etcd-apply-alarm-gauge-reactivate/alarm_gauge_test.go`](etcd-apply-alarm-gauge-reactivate/alarm_gauge_test.go),
copied into `server/etcdserver/apply` at etcd-io/etcd@1573d5941 (2026-10-28), go1.27.3
linux/amd64. It applies two `NOSPACE` activations and one deactivation through the applier
(`UberApplier.Apply`, as the apply loop does):

```
$ go test ./etcdserver/apply/ -run '^TestAlarmGaugeReactivate$' -count=1
--- FAIL: TestAlarmGaugeReactivate (0.01s)
    alarm_gauge_test.go:38:
        	Error:      	Not equal:
        	            	expected: 1
        	            	actual  : 2
        	Messages:   	the gauge should count the one alarm once
FAIL
```

**Cause:** [`applierV3backend.Alarm`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/apply/backend.go#L115-L131)
increments the gauge whenever `AlarmStore.Activate` returns a member, but
[`Activate`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3alarm/alarms.go#L53-L64)
returns the existing member, without adding one, when the alarm is already set.

## Proof

no: a metric; no statement of the apply package models the gauge.

## Fix

Count only a newly added alarm (have `Activate`/`Deactivate` report whether they changed the
store), or set the gauge per label (`Set(1)`/`Set(0)`) instead of `Inc`/`Dec`.

## Notes

The 2026-10-23 review's plan: skip for now (trivial fix, little impact). Kept as an issue: it has a
failing test through the applier; it is a debugging metric, so maintainers may not care.
