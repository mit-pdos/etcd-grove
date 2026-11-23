"""The rabia kit (notes/dsv-rabia.md): its etc/goose.py project and etc/gen-init.py
configuration (format: etc/dsv/README.md)."""
import os

# etc/goose.py's project dsv-rabia (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-rabia",
    # dsverify-lab's rabia kit (notes/dsv-rabia.md; notes/dsverify-net-port-plan.md, phase 6):
    # the lab's Rabia fork (examples/rabia/fork/rabia at lab master 915f964, fork ef2a93b, run
    # rabia-r1wake-1) with its kit ported onto examples/lib/remote, `examples/dsverify/rabia`
    # (module `rabia`). Into the part `Dsverify/`, with remote and `net` the part `Net/`'s,
    # lintest, porcupine, bufio, container/heap and path the main tree's; zerolog, gogo/protobuf,
    # go-redis and os/signal names only into the part (no model here: notes/dsv-rabia.md).
    # go-redis is v8.11.5 (the fork pins v8.8.2), the version the QuePaxa kit builds with: this
    # project owns the one go-redis translation in `Dsverify/`, which both kits' theorems use
    # (issue #24).
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "rabia"),
    root="Dsverify",
    expand_comment_tabs=True,
    lean_roots=["rabia=Dsverify", "github.com/rs/zerolog=Dsverify",
                "github.com/gogo/protobuf=Dsverify", "github.com/go-redis/redis/v8=Dsverify",
                "os/signal=Dsverify",
                "github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall=",
                "bufio=", "container/heap=", "path="],
    packages=["github.com/rs/zerolog", "github.com/gogo/protobuf/proto",
              "github.com/gogo/protobuf/gogoproto", "github.com/go-redis/redis/v8",
              "github.com/go-redis/redis/v8/internal/proto", "os/signal", "./internal/config", "./internal/message", "./internal/queue", "./internal/ledger",
              "./internal/tcp", "./internal/logger", "./internal/system",
              "./roles/server/layers/network", "./roles/server/layers/consensus",
              "./roles/server/layers/proxy", "./roles/server", "./examples/rabianet",
              "./examples/rabianet/cmd/orch"]
             + ["./examples/rabianet/cmd/client%d" % c for c in range(6)]
             + ["./examples/rabianet/cmd/server%d" % s for s in range(1, 6)],
    owned=["rabia", os.path.join("github_com", "rs"), os.path.join("github_com", "gogo"),
           os.path.join("github_com", "go_redis"), os.path.join("os", "signal")],
)

# etc/gen-init.py: Rabia's packages, the names-only libraries the lab modelled, the kit and its
# programs
RABIA_NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 6)]
PKGS = [f'rabia.{p}' for p in ['internal.config', 'internal.message', 'internal.queue',
                               'internal.ledger', 'internal.tcp', 'internal.logger', 'internal.system',
                               'roles.server.layers.network', 'roles.server.layers.consensus',
                               'roles.server.layers.proxy', 'roles.server', 'examples.rabianet']] + \
    [f'rabia.examples.rabianet.cmd.{n}' for n in RABIA_NODES]
PROGRAMS = {f'rabia.examples.rabianet.cmd.{n}':
            f'Proof/rabia/examples/rabianet/cmd/{n}/PkgTable.lean' for n in RABIA_NODES}
# the main tree's packages the kit imports beside `NET_MAIN`'s (bufio, container/heap, path)
# (their `Init.lean` generated into the part, over `Net/`'s `PkgInitExt`, as `Net/`'s `NET_MAIN`; the
# instances of `container.heap` and `path`, which the main tree declares in etcd's packages, the
# part's own `Base.lean`; `internal.bytealg` is Perennial's)
MAIN = ['bufio', 'container.heap', 'path']
# the names-only libraries are external here, as dsv-vr's: their `wp_initialize'` is a hypothesis
# (`Dsverify/Proof/<pkg>/Init.lean`'s class `InitHyp`), which every generated theorem initializing
# them takes as an instance; math/rand too (Perennial leaves its initializers untranslated)
HYP_INITS = ['github_com.rs.zerolog', 'github_com.gogo.protobuf.proto',
             'github_com.gogo.protobuf.gogoproto', 'github_com.go_redis.redis.v8',
             'github_com.go_redis.redis.v8.internal.proto', 'os.signal', 'math.rand']


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals)."""
    SPECIAL, newvars_cfg, FIN_PRE = {}, g.newvars_cfg, g.FIN_PRE
    SPECIAL['rabia.internal.config'] = dict(
        doc='''Its fact (`Base.lean`): `Conf`'s invariant `confInv`, as initialized. Its initializer
allocates `Conf` and initializes its imports.''',
        alloc_types={'Conf': 'rabia.internal.config.Config'},
        finish=['imod (inv_alloc _root_.Perennial.rabia.internal.config.confN ⊤ '
                '(_root_.Perennial.rabia.internal.config.confInv (GF := GF))) $$ [HConf] with #Hcinv',
                '· inext; iunfold _root_.Perennial.rabia.internal.config.confInv; ileft; iexact HConf'] +
               FIN_PRE[:6])
    # rabia's `message` (message.pb.go's variables and two `init`s): the errors (`errors.New`, verb-less
    # `fmt.Errorf`), the `MsgType` maps, the file descriptor's slice, and gogo proto's `Register*` calls,
    # whose specs are the fields of the hypothesis `proto.Hyps` (names only here: notes/dsv-rabia.md),
    # carried by every package above (`vars`)
    _DSV_MSG = 'rabia.internal.message'
    _DSV_IMI = '_root_.Perennial.github_com.gogo.protobuf.proto.InternalMessageInfo'
    _DSV_PH = '_root_.Perennial.github_com.gogo.protobuf.proto.Hyps'
    SPECIAL[_DSV_MSG] = newvars_cfg({
        'alloc_types': {'MsgType_name': 'Loc', 'MsgType_value': 'Loc',
                        'fileDescriptor_33c57e4bae7b9afd': 'GoSlice', 'xxx_messageInfo_Msg': _DSV_IMI,
                        'xxx_messageInfo_ConsensusObj': _DSV_IMI, 'xxx_messageInfo_Command': _DSV_IMI},
        'before': {
            'MsgType_name': ['try wp_auto',
                             'wp_apply (wp_map_make1 (K := w32) (V := GoString)) as %mName Hm',
                             'repeat (wp_apply wp_mapInsert $$ Hm as Hm)'],
            'MsgType_value': ['try wp_auto',
                              'wp_apply (wp_map_make1 (K := GoString) (V := w32)) as %mVal Hm2',
                              'repeat (wp_apply wp_mapInsert $$ Hm2 as Hm2)'],
            'fileDescriptor_33c57e4bae7b9afd': [
                'try wp_auto', 'wp_apply wp_slice_literal (V := w8) _', 'isplitr',
                '· ipureintro; first | rfl | (with_unfolding_all rfl) | simp | decide',
                'iintro %fdp ⟨Hfds, _⟩'],
        },
        'after': {
            # (#24) the package state out of `Hown` for the `Register*` calls (`proto.Hyps`), and
            # `MsgType_value`'s points-to for `RegisterEnum` (consumed: called once, here)
            'init.«0»': ['iunfold EtcdGrove.ownInitLb at Hown',
                         'icases Hown with ⟨%σg, Hg, #Hok, %Hle⟩',
                         f'wp_apply ({_DSV_PH}.RegisterEnum (GF := GF)) $$ [$Hg $HMsgType_value] as Hg',
                         'try wp_auto',
                         f'wp_apply ({_DSV_PH}.RegisterType (GF := GF)) $$ [$Hg] as Hg',
                         'try wp_auto',
                         f'wp_apply ({_DSV_PH}.RegisterType (GF := GF)) $$ [$Hg] as Hg',
                         'try wp_auto',
                         f'wp_apply ({_DSV_PH}.RegisterType (GF := GF)) $$ [$Hg] as Hg',
                         'try wp_auto'],
            'init.«1»': [f'wp_apply ({_DSV_PH}.RegisterFile (GF := GF)) $$ [$Hg] as Hg',
                         'try wp_auto',
                         'ihave Hown : EtcdGrove.ownInitLb get_is_pkg_init σ0 $$ [Hg]',
                         '· iunfold EtcdGrove.ownInitLb; iexists σg; iframe Hg Hok; ipureintro; exact Hle'],
        },
        # (#24) gogo proto's `Register*` specs (`proto/Spec.lean`), a premise of their own
        'imports': ['Dsverify.Proof.github_com.gogo.protobuf.proto.Spec'],
        'vars': [f'[{_DSV_PH} GF]'],
        'rec_depth': 100000,
        'heavy': True,
        # its fact (`message/Base.lean`'s `msgFact`): the framing's two errors, non-`nil`
        'finish': ['ipersist HerrFrameTooLarge', 'ipersist HerrFrameTooLong'] + FIN_PRE[:6] +
                  ['iunfold _root_.Perennial.rabia.internal.message.msgFact',
                   'iexists _, _', 'iframe HerrFrameTooLarge HerrFrameTooLong',
                   'ipureintro', 'simp [interface.mkOk]'],
    }, ['errFrameTooLong', 'errFrameTooLarge', 'ErrInvalidLengthMessage', 'ErrIntOverflowMessage',
        'ErrUnexpectedEndOfGroupMessage'],
       errorf={'ErrInvalidLengthMessage': 'proto: negative length found during unmarshaling',
               'ErrIntOverflowMessage': 'proto: integer overflow',
               'ErrUnexpectedEndOfGroupMessage': 'proto: unexpected end of group'})
    return SPECIAL
