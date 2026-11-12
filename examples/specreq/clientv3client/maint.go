package clientv3client

import (
	"context"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3client/status: Status of an endpoint returns a reply whose fields can be read, or an
// error; nothing about the cluster's state.
// Users: Kubernetes' feature_support_checker.go:194 (resp.Version), storagebackend/factory/etcd3.go:277
// (status.DbSize), client.go's checkVersion.
// Assumes: as clientv3client/endpoints (the endpoints token's fraction, a non-empty list); ep serves
// the cluster.
// Specs: Client.Status.spec (Maint.StatusTriple: statusRespOwn; its field unfold is 3h's).
func ReqStatus(ctx context.Context, cli *clientv3.Client, ep string) {
	st, err := cli.Status(ctx, ep)
	if err != nil {
		return
	}
	_ = st.Version
	_ = st.DbSize
}

// REQ clientv3client/alarm-disarm: disarming a raised alarm removes it: a later list does not show
// it, unless raised again (an environment step the owner's invariant sees).
// Users: etcdctl alarm disarm, the e2e tests (quota).
// Assumes: no alarm is raised meanwhile (the owner's invariant: no EnvStep.alarm).
// Specs: maintenance.AlarmDisarm.spec, maintenance.AlarmList.spec; model: clusterStep.
func ReqAlarmDisarm(ctx context.Context, cli *clientv3.Client, member uint64) {
	am := &clientv3.AlarmMember{MemberID: member, Alarm: pb.AlarmType_NOSPACE}
	if _, err := cli.Maintenance.AlarmDisarm(ctx, am); err != nil {
		return
	}
	l, err := cli.Maintenance.AlarmList(ctx)
	if err != nil {
		return
	}
	for _, a := range l.Alarms {
		if a.MemberID == member && a.Alarm == pb.AlarmType_NOSPACE {
			panic("alarm-disarm: alarm still raised")
		}
	}
}
