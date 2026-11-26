"""The craq kit (notes/dsv-craq.md): its etc/goose.py project and etc/gen-init.py
configuration (format: etc/dsv/README.md)."""
import os

# etc/goose.py's project dsv-craq (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-craq",
    # dsverify-lab's craq kit (notes/dsv-craq.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's fork of despreston/go-craq (examples/craq/fork/go-craq at lab master 915f964,
    # fork a0238ac) with its kit ported onto examples/lib/remote, `examples/dsverify/craq` (a
    # Go module of its own, module path the fork's). Into the part `Dsverify/`, with remote,
    # `net`, `net/rpc` and `net/http` the part `Net/`'s (the models: std_models), lintest and
    # porcupine the main tree's.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "craq"),
    root="Dsverify",
    lean_roots=["github.com/despreston/go-craq=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "net/url=", "path=", "crypto/tls=", "vendor=Net",
                "golang.org/x/net/http/httpguts=Net", "go/token=Net"],
    packages=["./transport", "./transport/netrpc", "./store", "./store/kv", "./node",
              "./coordinator", "./examples/craqnet", "./examples/craqnet/cmd/orch"]
             + ["./examples/craqnet/cmd/client%d" % c for c in range(5)]
             + ["./examples/craqnet/cmd/server%d" % s for s in range(1, 7)],
    owned=[os.path.join("github_com", "despreston")],
    std_models=["net/rpc", "net/http"],
)

# etc/gen-init.py: go-craq's packages, the kit and its twelve machines' commands.
# net/rpc's and net/http's initializers are `Net/`'s (external; their `wp_initialize'` and
# first-run `wp_init_first` Net's interim axioms, `etc/gen-init.py`'s `NET_AXIOM_INITS`)
CRAQ = 'github_com.despreston.go_craq'
CRAQ_NODES = ['orch'] + [f'client{c}' for c in range(5)] + [f'server{s}' for s in range(1, 7)]
PKGS = [f'{CRAQ}.{p}' for p in ['transport', 'store', 'store.kv', 'node', 'coordinator',
                                'transport.netrpc', 'examples.craqnet']] + \
    [f'{CRAQ}.examples.craqnet.cmd.{n}' for n in CRAQ_NODES]
# the twelve commands' package tables (the deployment's boots)
PROGRAMS = {f'{CRAQ}.examples.craqnet.cmd.{n}':
            f'Proof/{CRAQ.replace(".", "/")}/examples/craqnet/cmd/{n}/PkgTable.lean'
            for n in CRAQ_NODES}
HYP_INITS = []
# the main tree's packages net/http's closure needs, added to `NET_MAIN` (as EPaxos)
MAIN = ['bufio', 'path', 'internal.bytealg', 'net.url', 'crypto.tls']
MAIN_GEN = ['bufio']


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL, FIN_PRE, DSV_CRAQ = {}, g.FIN_PRE, CRAQ
    # go-craq's `errors.New` package variables: each package's fact (its `Base.lean`) is their
    # `errors.newVar`s (as the lab's `PkgState.lean`)
    _CRAQ_ERRS = {'store': ['ErrNotFound', 'ErrDirtyItem'],
                  'node': ['errNoSuccessor', 'errNoTail', 'errNotTail', 'errTailVersion'],
                  'coordinator': ['ErrEmptyChain', 'errLastNode', 'errDisconnected', 'ErrVersions']}
    for _p, _xs in _CRAQ_ERRS.items():
        SPECIAL[f'{DSV_CRAQ}.{_p}'] = dict(
            doc=f'''Its fact (`Base.lean`): its error variables ({", ".join("`" + x + "`" for x in _xs)}, translated
`errors.New` calls) each hold `errors.New` of their message (`errors.newVar`). Its initializer
allocates them, initializes its imports and runs their translated initializers.''',
            imports=['Perennial.Proof.errors.NewVar'],
            alloc_types={x: 'GoInterface' for x in _xs},
            before=dict({x: ['try wp_auto', f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{x} ⟨#S{x}, #M{x}⟩']
                         for x in _xs}, **{'$end': ['try wp_auto']}),
            finish=[f'ipersist H{x}' for x in _xs] + FIN_PRE[:6] + ['imodintro',
                   'unfold _root_.Perennial.errors.newVar'] +
                   [l for x in _xs[:-1] for l in ['isplitr', f'· iexists _; iframe H{x} S{x} M{x}']] +
                   [f'iexists _; iframe H{_xs[-1]} S{_xs[-1]} M{_xs[-1]}'])
    return SPECIAL


# etc/dsv/kitgen.py (notes/dsv-kitgen.md): the machines' first-run boot's tables, `BootTable.lean`
# and `BootCmdsLinked.lean` (as dsv-epaxos's); the machines are the five clients and the six
# servers, each importing `craqnet` only (the orchestrator's boot is its generated initializer spec)
KITGEN = dict(
    name='craq',
    title='CRAQ',
    go_mains=False,
    lean_pkg=f'{CRAQ}.examples.craqnet',
    roles=[dict(cmd='client{id}', ids=list(range(5))), dict(cmd='server{id}', ids=list(range(1, 7)))],
    boot=dict(
        # the table: server1's chain (etc/gen-init.py's cmd/server1/PkgTable.lean)
        table='server1',
        owned=[f'{CRAQ}.examples.craqnet', f'{CRAQ}.transport.netrpc', 'net.rpc', 'net.http'],
        table_doc='''The package facts of the CRAQ kit's boot (notes/dsv-craq.md, the boot): generic in a program's
table `G` that gives every package of `craqnet`'s import closure its `isPkgInit` (`KitG G`), the
facts at `G` (`wf_*`) and, for the packages whose closure avoids the kit's owned packages
(`ownedPkgs`: `craqnet` and `transport/netrpc`, whose first initializations the boot proves, and
net/rpc's and net/http's, Net's first runs), at `gOff S G` for `S` a sub-list of `ownedPkgs` (`wfO_*`): the table in which
the packages of `S` are not initialized yet.''',
        cmds_doc='''The CRAQ kit's eleven client and server commands' boots (notes/dsv-craq.md, the boot): each
command's initialization from the machine's empty package state, its first, through `craqnet`'s
(`BootLinked.lean`, `boot_craqnet`), at the command's table (`getIsPkgInit`, its `PkgTable.lean`;
`kitG`).''',
        opens=['open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net',
               f'open {CRAQ} {CRAQ}.examples.craqnet',
               'open EtcdGrove (wp_package_init_first)'],
        attributes=['attribute [local instance] GooseGlobalGS.gooseInvGS'],
        variables='''variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : cmd.{n}.Assumptions] [π : NetProtoGS]
variable [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
variable [Threads30 (GF := GF)]''',
        returns="returns the machine's net/rpc boot resources.",
        q='rpcBootRes',
        post='        isPkgInit (PROP := IProp GF) pkg_id.{pkg}.cmd.{n} ∗ rpcBootRes',
    ),
)
