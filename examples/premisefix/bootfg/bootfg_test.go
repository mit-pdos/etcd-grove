// Package bootfg checks bootstrap's feature-gate precondition (premise fixes 1, 2026-11-10):
// storage's newBackend (server/storage/backend.go) calls cfg.ServerFeatureGate.Enabled(
// NonBlockingDefrag) on a non-nil gate, and featuregate panics when the feature is not registered,
// so bootstrapContract (Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean) holds only for a
// nil gate or one that answers it (isFeatureGate), as storage.openPre already says.
package bootfg

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/pkg/v3/featuregate"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/features"
)

// cfgFor is etcdstart.newServerMode's configuration for StartServer("putget", ...), with the
// feature gate fg: it meets cfgOk "putget" "putget", urls1, bootCfgOk and bootCfgFresh, and its
// data directory is fresh.
func cfgFor(dir string, fg featuregate.FeatureGate) config.ServerConfig {
	lg := zap.NewNop()
	peer := types.URLs{{Scheme: "http", Host: "127.0.0.1:23800"}}
	return config.ServerConfig{
		Name:                "putget",
		DataDir:             filepath.Join(dir, "putget.etcd"),
		InitialPeerURLsMap:  types.URLsMap{"putget": peer},
		PeerURLs:            peer,
		ClientURLs:          types.URLs{{Scheme: "http", Host: "127.0.0.1:23790"}},
		InitialClusterToken: "putget",
		NewCluster:          true,
		TickMs:              100,
		ElectionTicks:       10,
		SnapshotCount:       etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:           128,
		MaxRequestBytes:     1536 * 1024,
		AutoCompactionMode:  "revision",
		Logger:              lg,
		ServerFeatureGate:   fg,
	}
}

func TestChild(t *testing.T) {
	mode := os.Getenv("BOOTFG_MODE")
	if mode == "" {
		t.Skip("child only")
	}
	lg := zap.NewNop()
	var fg featuregate.FeatureGate
	if mode == "default" {
		fg = features.NewDefaultServerFeatureGate("putget", lg)
	} else {
		fg = featuregate.New("putget", lg) // a valid gate, no feature registered
	}
	_, err := etcdserver.NewServer(cfgFor(os.Getenv("BOOTFG_DIR"), fg))
	t.Logf("NewServer returned err=%v", err)
}

func run(t *testing.T, mode string) (string, error) {
	cmd := exec.Command(os.Args[0], "-test.run=^TestChild$", "-test.v")
	cmd.Env = append(os.Environ(), "BOOTFG_MODE="+mode, "BOOTFG_DIR="+t.TempDir())
	out, err := cmd.CombinedOutput()
	return string(out), err
}

func TestBootstrapFeatureGate(t *testing.T) {
	out, err := run(t, "default")
	t.Logf("default gate: err=%v\n%s", err, out)
	if err != nil {
		t.Fatalf("control failed")
	}
	out, err = run(t, "empty")
	t.Logf("empty gate: err=%v\n%s", err, lastLines(out, 40))
	if err == nil || !strings.Contains(out, "is not registered in FeatureGate") {
		t.Fatalf("expected bootstrap's newBackend goroutine to panic")
	}
}

func lastLines(s string, n int) string {
	l := strings.Split(s, "\n")
	if len(l) > n {
		l = l[:n]
	}
	return strings.Join(l, "\n")
}
