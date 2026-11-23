"""The paxos kit (notes/dsv-paxos.md): its etc/goose.py project and its etc/gen-init.py
configuration, in the format of etc/dsv/README.md."""
import os

# etc/goose.py's project dsv-paxos (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-paxos",
    # dsverify-lab's paxos kit (notes/dsv-paxos.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's fork of xiang90/paxos (examples/paxos/fork/paxos at lab master 7a84fb35) with
    # its kit ported onto examples/lib/remote, `examples/dsverify/paxos` (a Go module of its
    # own, module path the fork's). Into the part `Dsverify/` (modules `Dsverify.*`), with
    # remote and `net` the part `Net/`'s, lintest and porcupine the main tree's, marshal
    # Perennial's.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "paxos"),
    root="Dsverify",
    lean_roots=["github.com/xiang90/paxos=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
    packages=[".", "./examples/paxosnet", "./examples/paxosnet/cmd/orch"]
             + ["./examples/paxosnet/cmd/client%d" % c for c in range(4)]
             + ["./examples/paxosnet/cmd/server%d" % s for s in range(1, 6)],
    owned=[os.path.join("github_com", "xiang90")],
)

# etc/gen-init.py: the packages whose `Init.lean` is generated into `Dsverify/Proof/`, and the
# programs whose `PkgTable.lean` is
PAXOS = 'github_com.xiang90.paxos'
NODES = ['orch'] + [f'client{c}' for c in range(4)] + [f'server{s}' for s in range(1, 6)]
PKGS = [PAXOS, f'{PAXOS}.examples.paxosnet'] + [f'{PAXOS}.examples.paxosnet.cmd.{n}' for n in NODES]
PROGRAMS = {f'{PAXOS}.examples.paxosnet.cmd.{n}':
            f'Proof/{PAXOS.replace(".", "/")}/examples/paxosnet/cmd/{n}/PkgTable.lean'
            for n in NODES}
