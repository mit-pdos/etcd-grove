"""The gryff kit (notes/dsv-gryff.md): its etc/goose.py project (format: etc/dsv/README.md; no
etc/gen-init.py configuration yet)."""
import os

# etc/goose.py's project dsv-gryff (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-gryff",
    # dsverify-lab's gryff kit (notes/dsv-gryff.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's fork of Gryff (examples/gryff/fork/gryff, commit ef17c2d, run gryff-bump-1, at
    # lab master 915f964) with its kit ported onto examples/lib/remote, `examples/dsverify/gryff`
    # (a Go module of its own, module path the fork's, `gryff`). Into the part `Dsverify/`
    # (modules `Dsverify.*`), with remote, `net` and the net/rpc and net/http models the part
    # `Net/`'s (std_models, as project models-net), lintest and porcupine the main tree's.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "gryff"),
    root="Dsverify",
    lean_roots=["gryff=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "net/url=", "path=", "crypto/tls=", "vendor=Net",
                "golang.org/x/net/http/httpguts=Net", "go/token=Net"],
    packages=["./src/fastrpc", "./src/dlog", "./src/state", "./src/stats", "./src/clientproto",
              "./src/genericsmrproto", "./src/masterproto", "./src/epaxosproto",
              "./src/gryffproto", "./src/bitvec", "./src/bloomfilter", "./src/genericsmr",
              "./src/gryffcommon", "./src/gryff", "./src/masterlib", "./src/serverlib",
              "./examples/gryffnet", "./examples/gryffnet/cmd/orch"]
             + ["./examples/gryffnet/cmd/client%d" % c for c in range(6)]
             + ["./examples/gryffnet/cmd/server%d" % s for s in range(1, 5)],
    owned=["gryff"],
    std_models=["net/rpc", "net/http"],
)
