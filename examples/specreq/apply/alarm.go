package apply

import (
	"errors"

	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	errs "go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/raft/v3/raftpb"
)

// REQ apply/nospace-capped: once a NOSPACE alarm is applied, a put is refused with ErrNoSpace (the
// capped applier: nothing written), on every member alike.
// Users: server/etcdserver/server.go:2000-2015 (applyEntryNormal: the NOSPACE alarm proposed after
// an ErrNoSpace), v3rpc's quota interceptors (2a).
// Assumes: alarmEnt is a committed entry of AlarmRequest{ACTIVATE, member, NOSPACE}; putEnt the
// next committed entry, a valid put; no CORRUPT alarm; this goroutine is the apply thread.
// Specs: Apply.spec, isUber_apply; laws: irrStep_alarm (the activation), irrStep_step (the refusal).
func ReqNoSpaceCapped(lg *zap.Logger, alarmEnt, putEnt *raftpb.Entry, ua apply.UberApplier, w wait.Wait) {
	ar, _ := apply.Apply(lg, alarmEnt, ua, w, true)
	if ar != nil && ar.Err != nil {
		panic("nospace: the activation failed")
	}
	ar, _ = apply.Apply(lg, putEnt, ua, w, true)
	if ar != nil && !errors.Is(ar.Err, errs.ErrNoSpace) {
		panic("nospace: a put applied under a NOSPACE alarm")
	}
}

// REQ apply/corrupt: under a CORRUPT alarm the KV requests are refused with ErrCorrupt.
// Users: server/etcdserver/corrupt.go (the corruption checker proposes CORRUPT), applyEntryNormal.
// Assumes: rangeEnt is a committed entry of a valid Range (a key, a valid sort: reqAdmitted); a
// CORRUPT alarm is raised in ua's alarm store; this goroutine is the apply thread.
// Specs: Apply.spec, isUber_apply; laws: irrStep_step.
func ReqCorrupt(lg *zap.Logger, rangeEnt *raftpb.Entry, ua apply.UberApplier, w wait.Wait) {
	ar, _ := apply.Apply(lg, rangeEnt, ua, w, true)
	if ar != nil && !errors.Is(ar.Err, errs.ErrCorrupt) {
		panic("corrupt: a read served under a CORRUPT alarm")
	}
}
