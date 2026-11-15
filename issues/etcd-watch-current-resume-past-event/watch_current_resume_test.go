package watch

import (
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestWatchFromCurrentRevisionResumeDeliversPastEvent: a watch from the current revision (no
// WithRev) must deliver only events that happen after the server receives the request. The
// client stores the creation response's header revision H as the watch's resume revision, not
// H+1, so after a reconnect the watch is re-created from H and delivers revision H's events,
// which were committed before the watch was created.
func TestWatchFromCurrentRevisionResumeDeliversPastEvent(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1, UseBridge: true})
	defer clus.Terminate(t)
	cli := clus.Client(0)
	ctx := t.Context()

	presp, err := cli.Put(ctx, "k", "before-the-watch")
	if err != nil {
		t.Fatal(err)
	}
	wch := cli.Watch(ctx, "k", clientv3.WithCreatedNotify())
	created := <-wch
	if !created.Created {
		t.Fatalf("expected the created response first, got %+v", created)
	}
	if created.Header.Revision != presp.Header.Revision {
		t.Fatalf("the watch was created at revision %d, after the put at %d", created.Header.Revision, presp.Header.Revision)
	}

	// a transient disconnect: the client resumes the watch on a new stream
	clus.Members[0].Bridge().DropConnections()

	select {
	case wr, ok := <-wch:
		if !ok {
			t.Fatal("watch channel closed")
		}
		for _, ev := range wr.Events {
			if ev.Kv.ModRevision <= created.Header.Revision {
				t.Fatalf("after a reconnect, the watch created at revision %d delivered an event at revision %d (%q), committed before the watch",
					created.Header.Revision, ev.Kv.ModRevision, ev.Kv.Value)
			}
		}
	case <-time.After(5 * time.Second):
	}
}
