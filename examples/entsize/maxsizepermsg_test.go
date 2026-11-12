// Package entsize checks, at the pinned etcd, the facts about etcd's raft configuration that the
// raft-entsize stage records as premises of the Lean proofs.
//
// TestMaxSizePerMsg backs `rnStartCfg`'s field `maxMsg` (`uint.Z cv.MaxSizePerMsg' ≤ 2^20`,
// Proof/go_etcd_io/etcd/server/v3/etcdserver/InvNodeStart.lean), a field of the bootstrap
// contract: every bootstrapped raft node's configuration has MaxSizePerMsg = 1 MiB
// (server/etcdserver/raft.go: `maxSizePerMsg = 1 * 1024 * 1024`; server/etcdserver/bootstrap.go:
// both `bootstrappedRaft` constructions take `config: raftConfig(...)`, which sets
// `MaxSizePerMsg: maxSizePerMsg`).
package entsize

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	_ "unsafe" // go:linkname

	"go.etcd.io/etcd/server/v3/config"
	_ "go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/raft/v3"
	"go.uber.org/zap"
)

// raftConfig is etcdserver's (unexported) raft configuration builder, which both of
// bootstrap.go's bootstrappedRaft constructions call.
//
//go:linkname raftConfig go.etcd.io/etcd/server/v3/etcdserver.raftConfig
func raftConfig(cfg config.ServerConfig, id uint64, s *raft.MemoryStorage) *raft.Config

// TestMaxSizePerMsg: the configuration raftConfig builds has MaxSizePerMsg = 2^20 (run), and
// every bootstrappedRaft literal of bootstrap.go takes its config from raftConfig (source).
func TestMaxSizePerMsg(t *testing.T) {
	for _, pre := range []bool{false, true} {
		c := raftConfig(config.ServerConfig{Logger: zap.NewNop(), ElectionTicks: 10, PreVote: pre},
			1, raft.NewMemoryStorage())
		if c.MaxSizePerMsg != 1<<20 {
			t.Fatalf("raftConfig: MaxSizePerMsg = %d, want %d", c.MaxSizePerMsg, 1<<20)
		}
	}

	out, err := exec.Command("go", "list", "-f", "{{.Dir}}", "go.etcd.io/etcd/server/v3/etcdserver").Output()
	if err != nil {
		t.Fatalf("go list: %v", err)
	}
	file := filepath.Join(strings.TrimSpace(string(out)), "bootstrap.go")
	f, err := parser.ParseFile(token.NewFileSet(), file, nil, 0)
	if err != nil {
		t.Fatalf("parse %s: %v", file, err)
	}
	lits := 0
	ast.Inspect(f, func(n ast.Node) bool {
		cl, ok := n.(*ast.CompositeLit)
		if !ok {
			return true
		}
		if id, ok := cl.Type.(*ast.Ident); !ok || id.Name != "bootstrappedRaft" {
			return true
		}
		lits++
		fromRaftConfig := false
		for _, e := range cl.Elts {
			kv, ok := e.(*ast.KeyValueExpr)
			if !ok {
				t.Fatalf("%s: a positional bootstrappedRaft literal", file)
			}
			if k, ok := kv.Key.(*ast.Ident); ok && k.Name == "config" {
				call, ok := kv.Value.(*ast.CallExpr)
				if fn, ok2 := call.Fun.(*ast.Ident); ok && ok2 && fn.Name == "raftConfig" {
					fromRaftConfig = true
				}
			}
		}
		if !fromRaftConfig {
			t.Fatalf("%s: a bootstrappedRaft literal whose config is not raftConfig(...)", file)
		}
		return true
	})
	if lits != 2 {
		t.Fatalf("%s: %d bootstrappedRaft literals, want 2 (fromCluster, fromWAL)", file, lits)
	}
	t.Logf("raftConfig: MaxSizePerMsg = 2^20; %d bootstrappedRaft literals, each config: raftConfig(...)", lits)
}
