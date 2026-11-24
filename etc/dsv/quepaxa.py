"""The QuePaxa kit (notes/dsv-quepaxa.md): its etc/goose.py project and etc/gen-init.py
configuration (format: etc/dsv/README.md)."""
import os

# etc/goose.py's project dsv-quepaxa (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-quepaxa",
    # dsverify-lab's QuePaxa kit (notes/dsv-quepaxa.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's fork of QuePaxa (examples/quepaxa/fork/quepaxa at lab master 915f964, run
    # quepaxa-bump-1, fork 77b5258) with its kit ported onto examples/lib/remote,
    # `examples/dsverify/quepaxa` (a Go module of its own, module path the fork's, `raxos`). Into
    # the part `Dsverify/` (modules `Dsverify.*`), with remote and `net` the part `Net/`'s;
    # protobuf, lintest, porcupine, bufio and os the main tree's; grpc (from its model,
    # models/grpc), grpc/codes, grpc/status types and names only into the part (the main tree's
    # grpc imports the main tree's `net`); yaml.v2, go-redis, io/ioutil and encoding/gob names
    # only into the part (the lab's cut-down model of go-redis is not brought over). go-redis's
    # translation is project dsv-rabia's (v8.11.5, names and types only; it owns
    # `github_com/go_redis`): both kits' go.mod pin v8.11.5 (dsv-goredis), so the translation is
    # of the version that runs (notes/dsv-quepaxa.md, "go-redis").
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "quepaxa"),
    root="Dsverify",
    module_models={"google.golang.org/grpc": "models/grpc"},
    lean_roots=["raxos=Dsverify", "gopkg.in/yaml.v2=Dsverify",
                "github.com/go-redis/redis/v8=Dsverify", "io/ioutil=Dsverify",
                "encoding/gob=Dsverify", "google.golang.org/grpc=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "google.golang.org=", "bufio=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
    packages=["gopkg.in/yaml.v2", "io/ioutil", "encoding/gob",
              "google.golang.org/grpc", "google.golang.org/grpc/codes",
              "google.golang.org/grpc/status",
              "./common", "./configuration", "./proto", "./proto/client", "./replica/src",
              "./examples/quepaxanet", "./examples/quepaxanet/cmd/orch"]
             + ["./examples/quepaxanet/cmd/client%d" % c for c in range(6)]
             + ["./examples/quepaxanet/cmd/server%d" % s for s in range(1, 6)],
    owned=["raxos", os.path.join("gopkg_in", "yaml_v2"), os.path.join("io", "ioutil"),
           os.path.join("encoding", "gob"), os.path.join("google_golang_org", "grpc")],
    expand_comment_tabs=True,
)

# etc/gen-init.py: QuePaxa's packages, its kit's and its names-only libraries
QP = 'raxos'
QP_NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 6)]
PKGS = ['gopkg_in.yaml_v2', 'github_com.go_redis.redis.v8', 'io.ioutil', 'encoding.gob',
        'google_golang_org.grpc', 'google_golang_org.grpc.codes', 'google_golang_org.grpc.status',
        f'{QP}.common', f'{QP}.configuration', f'{QP}.proto', f'{QP}.proto.client',
        f'{QP}.replica.src', f'{QP}.examples.quepaxanet'] + \
    [f'{QP}.examples.quepaxanet.cmd.{n}' for n in QP_NODES]
PROGRAMS = {f'{QP}.examples.quepaxanet.cmd.{n}':
            f'Proof/{QP}/examples/quepaxanet/cmd/{n}/PkgTable.lean' for n in QP_NODES}
# the main tree's packages they import beside `NET_MAIN`'s (their `Init.lean` the main tree's where
# it generates the same, etc/gen-init.py's `shared_inits` (L1, 2026-11-24: all but `proto`'s, which
# the main tree takes from raft's); protobuf's facts: `Proof/google_golang_org/protobuf/PkgInit.lean`)
MAIN = ['bufio', 'google_golang_org.protobuf.proto',
        'google_golang_org.protobuf.reflect.protoreflect',
        'google_golang_org.protobuf.runtime.protoimpl', 'google_golang_org.protobuf.internal.impl',
        'google_golang_org.protobuf.internal.pragma']
# the packages whose `wp_initialize'` is a hypothesis (`Dsverify/Proof/<pkg>/Init.lean`'s class
# `InitHyp`): the names-only libraries, whose variables' initializers are untranslated, and math/rand
# (Perennial's translation leaves its initializers untranslated: the main tree's trust-boundary
# axiom `opaqueInitsOk`)
HYP_INITS = ['gopkg_in.yaml_v2', 'github_com.go_redis.redis.v8', 'io.ioutil', 'encoding.gob',
             'google_golang_org.grpc', 'google_golang_org.grpc.codes', 'math.rand']
# the part's own names-only translations of packages the main tree translates otherwise (grpc's):
# the main tree's configurations (`SPECIAL`) do not apply
OWN = {'google_golang_org.grpc', 'google_golang_org.grpc.codes', 'google_golang_org.grpc.status'}


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL = {}
    # (dsv-quepaxa) QuePaxa's replica: its translated gRPC service descriptor (the fact keeps nothing yet;
    # the lab's `srcState` is the descriptor's points-to, for the recorder's `RegisterService`)
    # (dsv-quepaxa) QuePaxa's replica: its translated gRPC service descriptor; the fact `srcState`
    # (`Dsverify/Proof/raxos/replica/src/Base.lean`, the lab's `PkgState.lean`) is the descriptor's
    # points-to, for the recorder's `RegisterService` (`descOk`)
    SPECIAL['raxos.replica.src'] = dict(
        doc='''Its fact (`srcState`, `Base.lean`): `Consensus_ServiceDesc` holds, read-only for good,
the descriptor of service `Consensus` (its three methods with their generated handlers, no
streams, its `HandlerType` the typed nil `(*ConsensusServer)(nil)`). Its initializer allocates
and sets the translated gRPC service descriptor (a `grpc.ServiceDesc` literal), initializes its
imports and runs the trusted initializers of protoc-gen-go's descriptor tables and `init` (models
in `TrustedCode/` that do nothing).''',
        alloc_types={'Consensus_ServiceDesc': 'google_golang_org.grpc.ServiceDesc'},
        before={'$inits': ['try wp_auto',
                           'wp_apply (wp_slice_literal (V := google_golang_org.grpc.MethodDesc) '
                           '(t := google_golang_org.grpc.MethodDesc.ty) '
                           '[⟨go!"ESP", functions _Consensus_ESP_Handler []⟩, '
                           '⟨go!"FetchBatches", functions _Consensus_FetchBatches_Handler []⟩, '
                           '⟨go!"InformDecision", functions _Consensus_InformDecision_Handler []⟩])',
                           'isplitr', '· ipureintro; rfl', 'iintro %ml ⟨Hml, -⟩',
                           'try wp_auto',
                           'wp_apply (wp_slice_literal (V := google_golang_org.grpc.StreamDesc) '
                           '(t := google_golang_org.grpc.StreamDesc.ty) [])',
                           'isplitr', '· ipureintro; rfl', 'iintro %sl ⟨-, -⟩',
                           'try wp_auto',
                           'ipersist HConsensus_ServiceDesc', 'ipersist Hml']},
        finish=['iframe Hown', 'imodintro', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
                'is_pkg_init_finish', 'unfold srcState', 'imodintro', 'iexists _',
                'iframe HConsensus_ServiceDesc', 'isplitr', '· ipureintro; exact ⟨rfl, rfl, rfl⟩',
                'iexact Hml'],
    )
    return SPECIAL
