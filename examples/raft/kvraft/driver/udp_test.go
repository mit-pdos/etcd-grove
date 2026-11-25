package driver

import (
	"bytes"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvraft"
)

// udpRound runs one round with the replicas' raft messages over UDP (kvraft-udp: TransportUDP), in
// crash mode crash (with the network's faults if netns), fails t unless porcupine answers Ok and
// nothing else failed, and returns the replicas' counters.
func udpRound(t *testing.T, crash string, netns bool) [kvraft.NumStats]uint64 {
	cfg := RandomConfig(crash, netns)
	cfg.Transport = TransportUDP
	if netns {
		// faults held, and crashed replicas down, longer than a snapshot's resends last
		// (snapAckWait*(snapResends+1), 1.2s), so that some snapshot goes unacknowledged
		// throughout, and some sender crashes in the middle of a message, whose fragments its
		// receiver then evicts
		cfg.NetHold = 3 * time.Second
		cfg.Downtime = 2 * time.Second
	}
	res, c := Run(cfg, self(t), t.TempDir())
	if c == nil {
		t.Fatal(res.Err)
	}
	var dump string
	if res.Err != nil || res.Check != porcupine.Ok {
		dump = c.Dump()
	}
	c.Stop()
	t.Logf("udp %+v: %v\n  %v\n  network: %s", cfg.Options, res.Check, &c.Stats, c.NetStats())
	if res.Err != nil {
		t.Fatalf("%v\n%s", res.Err, dump)
	}
	if res.Check != porcupine.Ok {
		t.Fatalf("porcupine answered %v\n%s", res.Check, dump)
	}
	return c.Stats.Node
}

// TestUDPKill runs a round over UDP whose crashes are kills, on one loopback address (no network
// faults): the replicas' processes run kvraft.RunNodeUDP, and the checking client's history passes
// porcupine.
func TestUDPKill(t *testing.T) {
	s := udpRound(t, CrashKill, false)
	if s[kvraft.StUDPFragmentsReceived] == 0 || s[kvraft.StDials] != 0 {
		t.Fatalf("fragments received %d, dials %d: not over UDP", s[kvraft.StUDPFragmentsReceived], s[kvraft.StDials])
	}
}

// udpFaultCounters are the counters TestUDPNetns requires nonzero (summed over its rounds): the
// network's faults reached the transport (fragments duplicated, reordered, lost), snapshots were
// sent and acknowledged and at least one was reported failed, and replicas restarted in their
// processes.
var udpFaultCounters = []int{
	kvraft.StUDPFragmentsDuplicate, kvraft.StUDPFragmentsReordered, kvraft.StUDPMsgsReordered,
	kvraft.StUDPReassembliesEvicted, kvraft.StUDPMultiFragment, kvraft.StSnapshotsSent,
	kvraft.StUDPSnapshotsAcked, kvraft.StUDPSnapshotsFailed, kvraft.StRestartsInProcess,
}

// TestUDPNetns runs rounds over UDP on machines that are network namespaces, with the network's
// faults (partitions, delay, loss, duplication, reordering; each held 3s on average) and kills and
// power losses (a replica down up to 2s), until the counters of udpFaultCounters are all nonzero (at most KVRAFT_UDP_ROUNDS rounds, default 10), each
// round's history passing porcupine: the test is not vacuous. It needs sudo without a password,
// and runs only with KVRAFT_NETNS set, as TestNetns.
func TestUDPNetns(t *testing.T) {
	if os.Getenv("KVRAFT_NETNS") == "" {
		t.Skip("set KVRAFT_NETNS=1 to run (needs sudo: network namespaces, iptables, tc, disks)")
	}
	if !robust.IsRoot() {
		var out bytes.Buffer
		args := []string{"-test.run=^TestUDPNetns$", "-test.v", "-test.count=1", "-test.timeout=60m"}
		err := robust.RerunAsRoot(args, []string{"KVRAFT_NETNS=1", "KVRAFT_UDP_ROUNDS=" + os.Getenv("KVRAFT_UDP_ROUNDS")}, &out)
		for _, l := range strings.Split(out.String(), "\n") {
			if strings.TrimSpace(l) != "" {
				t.Log(l)
			}
		}
		if err != nil {
			t.Fatalf("as root: %v", err)
		}
		return
	}
	if err := robust.NetnsAvailable(); err != nil {
		t.Skip("network namespaces unavailable:", err)
	}
	crash := CrashKill
	if robust.PowerAvailable() == nil {
		crash = CrashMixed
	}
	rounds := 10
	if r := os.Getenv("KVRAFT_UDP_ROUNDS"); r != "" {
		rounds = 0
		for _, ch := range r {
			rounds = rounds*10 + int(ch-'0')
		}
	}
	var total [kvraft.NumStats]uint64
	for i := 0; i < rounds; i++ {
		s := udpRound(t, crash, true)
		for k := range s {
			total[k] += s[k]
		}
		missing := ""
		for _, k := range udpFaultCounters {
			if total[k] == 0 {
				missing += " " + kvraft.StatNames[k]
			}
		}
		t.Logf("after round %d: %s", i+1, kvraft.FormatStats(total))
		if missing == "" {
			return
		}
		t.Logf("still zero:%s", missing)
	}
	t.Fatalf("after %d rounds, some fault counters are still zero: %s", rounds, kvraft.FormatStats(total))
}
