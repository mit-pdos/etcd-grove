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

# etc/gen-init.py: the fork's packages, the kit's and its eleven programs (notes/dsv-gryff.md,
# "Package initializers")
GRYFF = 'gryff'
GRYFF_SRC = ['fastrpc', 'dlog', 'state', 'stats', 'clientproto', 'genericsmrproto', 'masterproto',
             'epaxosproto', 'gryffproto', 'bitvec', 'bloomfilter', 'genericsmr', 'gryffcommon',
             'gryff', 'masterlib', 'serverlib']
GRYFF_NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 5)]
PKGS = [f'{GRYFF}.src.{p}' for p in GRYFF_SRC] + [f'{GRYFF}.examples.gryffnet'] + \
    [f'{GRYFF}.examples.gryffnet.cmd.{n}' for n in GRYFF_NODES]
PROGRAMS = {f'{GRYFF}.examples.gryffnet.cmd.{n}':
            f'Proof/{GRYFF}/examples/gryffnet/cmd/{n}/PkgTable.lean' for n in GRYFF_NODES}
# the main tree's packages the part's closure adds to `NET_MAIN` (bufio and net/http's), as EPaxos
MAIN = ['bufio', 'path', 'internal.bytealg', 'net.url', 'crypto.tls']
MAIN_GEN = ['bufio']
# initializers that are hypotheses (the `InitHyp` classes, notes/dsv-gryff.md, "Hypotheses"):
# net/rpc's and net/http's (`Net/`'s models, no initializer proof), math/rand's (Perennial has none)
HYP_INITS = ['net.rpc', 'net.http', 'math.rand']
HYP_IMPORTS = 'none'


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL = {}
    SPECIAL[f'{GRYFF}.src.dlog'] = dict(
        doc='''Its fact is `True`. Its initializer initializes its imports, allocates `DLOG` and stores
`false`.''',
        alloc_types={'DLOG': 'Bool'})
    SPECIAL[f'{GRYFF}.src.gryff'] = dict(
        doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables, stores
`stack` (`make([]*Instance, 0, 100)`), `cpcounter` (0) and `deferMap` (`make(map[uint64]uint64)`), and
runs its `init()` (`proph.go`: the trace prophecy, `traceProph = primitive.NewProph()`; ghost code,
notes/dsv-gryff.md). The variables and the prophecy are dropped here: a replica node keeps them
from its own boot (`Dsverify/Proof/gryff/Boot/Defs.lean`, `cmd/server{2,3,4}/Boot.lean`; notes/dsv-gryff.md, "Package
initializers").''',
        alloc_types={'traceProph': 'github_com.goose_lang.primitive.ProphId', 'deferMap': 'GoMap',
                     'aokr': 'src.gryffproto.AcceptOKReply',
                     'paokr': 'src.gryffproto.PreAcceptOKReply',
                     'ecs': 'src.epaxosproto.CommitShort', 'ec': 'src.gryffproto.ECommit',
                     'ea': 'src.gryffproto.EAccept', 'tpa': 'src.gryffproto.TryPreAccept',
                     'pa': 'src.gryffproto.PreAccept', 'happy': 'w64', 'slow': 'w64',
                     'weird': 'w64', 'conflicted': 'w64', 'cpcounter': 'w64',
                     'cpMarker': 'GoSlice', 'bf_PT': 'w32', 'stack': 'GoSlice'},
        before={'stack': ['try wp_auto',
                          'wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 100) (by decide)) as %stk -',
                          'try wp_auto'],
                'deferMap': ['try wp_auto',
                             'wp_apply (wp_map_make1 (K := w64) (V := w64) go.uint64 go.uint64) as %dm -',
                             'try wp_auto']},
        after={'init.«0»': ['wp_apply github_com.goose_lang.primitive.wp_NewProph as %pvs %p -',
                            'try wp_auto']})
    return SPECIAL
