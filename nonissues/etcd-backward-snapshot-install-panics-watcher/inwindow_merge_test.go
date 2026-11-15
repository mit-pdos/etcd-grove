// restart3 A0 / D-A0-3 (etcd-grove): a member installs a snapshot older than its backend, reached
// through etcd's own graceful paths, and a watch catching up at that member then panics the member.
//
// Five members S1, S2, R, X, Y (no disk snapshot: SnapshotCount large, so every restart replays its
// whole WAL as a replay window; memory snapshots every 100 entries compact the raft log).
//  1. R stops early (its log is short). S1 (leader), S2, X, Y write; S2 stops at z; S1, X, Y write on
//     to J; all stop. Only gofail sleeps and peer partitions (both etcd test facilities) steer timing.
//  2. L (S1 or X, both at J) restarts with S2 and X, R restarts cut off. L leads at a new term while
//     still replaying (its backend's consistent index J is ahead of its applied index). Once L has
//     compacted past R's log, R is connected to L: L merges a snapshot at its applied index i with its
//     whole backend (index J). R's peer links are cut again as soon as the stream arrives, so R stays at
//     raft index i, commit i, backend J.
//  3. Leadership moves to S2, which applies slowly (applied a2, z < a2 < J) and has compacted past i.
//     R is connected to S2: S2 merges at a2 with its backend (index a2 < J); R installs it, a backward
//     install. A watch opened at R just before, from a revision above the restored one, is unsynced
//     (the watch sync loop is slowed by a gofail sleep); the next sync panics in chooseAll.
package integration

import (
	"context"
	"fmt"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	gofail "go.etcd.io/gofail/runtime"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func zzPuts(t *testing.T, c *integration.Cluster, i, from, n, size int) {
	val := strings.Repeat("x", size)
	for k := from; k < from+n; k++ {
		ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
		_, err := c.Client(i).Put(ctx, fmt.Sprintf("/k/%05d", k), val)
		cancel()
		require.NoError(t, err)
	}
}

func zzCut(a, b *integration.Member) {
	a.Server.CutPeer(b.Server.MemberID())
	b.Server.CutPeer(a.Server.MemberID())
}

func zzMend(a, b *integration.Member) {
	a.Server.MendPeer(b.Server.MemberID())
	b.Server.MendPeer(a.Server.MemberID())
}

func zzWait(t *testing.T, what string, d time.Duration, f func() bool) {
	deadline := time.Now().Add(d)
	for !f() {
		require.Truef(t, time.Now().Before(deadline), "timed out waiting for %s", what)
		time.Sleep(10 * time.Millisecond)
	}
}

func zzLog(format string, args ...any) {
	fmt.Fprintf(os.Stderr, time.Now().Format("15:04:05.000")+" ZZ "+format+"\n", args...)
}

// zzLeader waits until the given members agree on a leader among them (no linearizable read).
func zzLeader(t *testing.T, m []*integration.Member, idx []int) int {
	deadline := time.Now().Add(120 * time.Second)
	for {
		lead := m[idx[0]].Server.Lead()
		ok := lead != 0
		for _, i := range idx[1:] {
			ok = ok && m[i].Server.Lead() == lead
		}
		if ok {
			for _, i := range idx {
				if uint64(m[i].Server.MemberID()) == lead {
					return i
				}
			}
		}
		require.Truef(t, time.Now().Before(deadline), "no leader among %v", idx)
		time.Sleep(20 * time.Millisecond)
	}
}

func TestZZBackwardInstallWatcherPanic(t *testing.T) {
	integration.BeforeTest(t)
	c := integration.NewCluster(t, &integration.ClusterConfig{Size: 5, SnapshotCount: 1000000,
		SnapshotCatchUpEntries: 5})
	defer c.Terminate(t)
	defer func() {
		for _, fp := range []string{"raftBeforeSave", "beforeApplyOneEntryNormal", "beforeSyncWatchers"} {
			gofail.Disable(fp)
		}
	}()

	s1 := c.WaitLeader(t)
	var others []int
	for i := range c.Members {
		if i != s1 {
			others = append(others, i)
		}
	}
	s2, r, x, y := others[0], others[1], others[2], others[3]
	m := c.Members
	const size = 100 << 10
	const z, J = 250, 450

	// 1.
	zzPuts(t, c, s1, 0, 5, 10)
	m[r].Stop(t)
	zzPuts(t, c, s1, 5, z, size)
	m[s2].Stop(t)
	zzLog("s2 stopped")
	zzPuts(t, c, s1, 5+z, J-z, size)
	m[x].Stop(t)
	m[y].Stop(t)
	m[s1].Stop(t)
	zzLog("phase 1 done: r, s2 at z, s1 x y at J stopped")

	// 2.
	require.NoError(t, gofail.Enable("raftBeforeSave", "sleep(100)"))
	require.NoError(t, gofail.Enable("beforeApplyOneEntryNormal", "sleep(20)"))
	for _, i := range []int{s1, s2, x} {
		require.NoError(t, m[i].Restart(t))
		for _, k := range []int{r, y} {
			m[i].Server.CutPeer(m[k].Server.MemberID())
		}
	}
	require.NoError(t, m[r].Restart(t))
	for _, k := range []int{s1, s2, x} {
		zzCut(m[r], m[k])
	}
	stopMon := make(chan struct{})
	defer close(stopMon)
	go func() {
		for {
			select {
			case <-stopMon:
				return
			case <-time.After(time.Second):
			}
			line := ""
			for i, mm := range m {
				if mm.Server == nil {
					continue
				}
				line += fmt.Sprintf(" [%d %s lead=%x term=%d commit=%d applied=%d]", i, mm.Name, mm.Server.Lead(), mm.Server.Term(), mm.Server.CommittedIndex(), mm.Server.AppliedIndex())
			}
			zzLog("%s", line)
		}
	}()
	zzLog("roles s1=%d s2=%d r=%d x=%d y=%d", s1, s2, r, x, y)
	L := zzLeader(t, m, []int{s1, s2, x})
	zzLog("leader %d", L)
	require.NotEqual(t, s2, L)
	ce := m[L].Server.CommittedIndex()
	zzLog("leader %s at applied %d, handed-out commit %d at its election", m[L].Name, m[L].Server.AppliedIndex(), ce)
	// the leader merges only at the end of a batch handed out at its term: wait until it applies those
	zzWait(t, "the leader to apply the batches of its term", 120*time.Second, func() bool {
		return m[L].Server.AppliedIndex() > ce+5 && m[L].Server.AppliedIndex() > 115
	})
	require.Less(t, m[L].Server.AppliedIndex(), uint64(J), "the leader's window closed too early")
	zzLog("mending R to the leader at applied %d", m[L].Server.AppliedIndex())
	zzMend(m[L], m[r])
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	lines, err := m[r].LogObserver.Expect(ctx, "restored mvcc store", 1)
	cancel()
	if os.Getenv("ZZ_EXPECT_DEFER") != "" {
		// A-g: the leader defers the merge inside its window; R installs after the window, forward
		zzLog("A-g: R's first install: %v (err %v)", lines, err)
		require.NoError(t, err)
	} else {
		require.NoError(t, err)
		zzLog("R's first install: %v", lines)
		al, _ := m[r].LogObserver.Expect(t.Context(), "applied snapshot", 1)
		zzLog("R's applied snapshot: %v", al)
	}
	gofail.Disable("raftBeforeSave")
	gofail.Disable("beforeApplyOneEntryNormal")
	for _, k := range []int{s1, s2, x} {
		zzMend(m[r], m[k])
	}
	zzLeader(t, m, []int{s1, s2, x, r})
	// R serves every acknowledged write: a linearizable read through R
	ctx, cancel = context.WithTimeout(t.Context(), 30*time.Second)
	g, err := c.Client(r).Get(ctx, "/k/", clientv3.WithPrefix(), clientv3.WithCountOnly())
	cancel()
	require.NoError(t, err)
	zzLog("R's linearizable count %d revision %d", g.Count, g.Header.Revision)
	require.Equal(t, int64(5+J), g.Count)

}
