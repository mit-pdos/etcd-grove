"""The swiftpaxos kit (notes/dsv-swiftpaxos.md): its etc/goose.py project (format: etc/dsv/README.md; no
etc/gen-init.py configuration yet)."""
import os

# etc/goose.py's project dsv-swiftpaxos (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-swiftpaxos",
    # dsverify-lab's swiftpaxos kit (notes/dsv-swiftpaxos.md; notes/dsverify-net-port-plan.md,
    # phase 6): the lab's fork of imdea-software/swiftpaxos (examples/swiftpaxos/fork/swiftpaxos
    # at lab master 915f964, fork 66dfc21, run swift-n2nofast-1), the system's packages with its
    # kit ported onto examples/lib/remote, `examples/dsverify/swiftpaxos` (a Go module of its
    # own, module path the fork's). Into the part `Dsverify/`, with remote, `net` and the
    # net/rpc and net/http models the part `Net/`'s (std_models), lintest, porcupine, bufio and
    # encoding/hex the main tree's; encoding/json the part's names-only one (dsv-vr's, as dsv-epaxos). Names and types only, in the part (no model yet: their
    # specs are the proof's hypotheses): encoding/gob, os/signal, github.com/google/uuid,
    # github.com/orcaman/concurrent-map (`Dsverify/Code/**.toml`). gods v1.18.1 translated as
    # project dsv-epaxos translates it (the same files: the red-black tree's iterator Next/Prev
    # names only); its treemap's specs are hypotheses here too.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "swiftpaxos"),
    root="Dsverify",
    lean_roots=["github.com/imdea-software/swiftpaxos=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "github.com/emirpasic/gods=Dsverify", "github.com/google/uuid=Dsverify",
                "github.com/orcaman/concurrent-map=Dsverify", "encoding/gob=Dsverify",
                "os/signal=Dsverify",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "encoding/hex=", "encoding/json=Dsverify", "net/url=", "path=", "crypto/tls=", "vendor=Net",
                "golang.org/x/net/http/httpguts=Net", "go/token=Net"],
    packages=["github.com/emirpasic/gods/utils", "github.com/emirpasic/gods/containers",
              "github.com/emirpasic/gods/maps", "github.com/emirpasic/gods/trees",
              "github.com/emirpasic/gods/trees/redblacktree",
              "github.com/emirpasic/gods/maps/treemap", "github.com/google/uuid", "github.com/orcaman/concurrent-map", "encoding/gob",
              "os/signal", "encoding/json",
              "./rpc", "./dlog", "./config", "./state", "./hook", "./replica/defs", "./replica",
              "./client", "./swift", "./master", "./examples/swiftnet",
              "./examples/swiftnet/cmd/orch"]
             + ["./examples/swiftnet/cmd/client%d" % c for c in range(6)]
             + ["./examples/swiftnet/cmd/server%d" % s for s in range(1, 7)],
    owned=[os.path.join("github_com", "imdea_software"), os.path.join("github_com", "emirpasic"),
           os.path.join("github_com", "google", "uuid"), os.path.join("github_com", "orcaman"),
           os.path.join("encoding", "gob"), os.path.join("os", "signal"),
           os.path.join("encoding", "json")],
    std_models=["net/rpc", "net/http", "encoding/json"],
)
