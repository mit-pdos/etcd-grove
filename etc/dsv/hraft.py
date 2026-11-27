"""The hraft kit (notes/dsv-hraft.md; the plan: mit-pdos/etcd-grove#48): its etc/goose.py project
and etc/gen-init.py configuration (format: etc/dsv/README.md). Stage S0: hashicorp/raft's package
and the snapshot store only, translated, with their generated initializers; no kit yet."""
import os

# etc/goose.py's project dsv-hraft (the fields of goose.py's `Project`)
GOOSE = dict(
    name="dsv-hraft",
    # dsverify-lab's hraft-4 verification fork of hashicorp/raft v1.8.0 (examples/hraft/fork/raft
    # at lab c39f136, fork commit 02f88d5 on v1.8.0 0f543c0), without the lab's in-process harness,
    # `examples/dsverify/hraft` (a Go module of its own, module path the fork's). Into the part
    # `Dsverify/`. The fork needs only the standard library and goose's `primitive`.
    repo=None,
    rev=None,
    local=os.path.join("examples", "dsverify", "hraft"),
    root="Dsverify",
    lean_roots=["github.com/hashicorp/raft=Dsverify"],
    packages=[".", "./examples/snapstore"],
    owned=[os.path.join("github_com", "hashicorp")],
)

# etc/gen-init.py: raft's package and the snapshot store (no commands yet: S1 adds the kit)
HRAFT = 'github_com.hashicorp.raft'
PKGS = [HRAFT, f'{HRAFT}.examples.snapstore']
PROGRAMS = {}
HYP_INITS = []

# raft's `errors.New` package variables, with their messages (api.go, kept.go, replication.go,
# encoding.go), and snapstore's
RAFT_ERRS = dict(
    ErrLeader="node is the leader",
    ErrNotLeader="node is not the leader",
    ErrNotVoter="node is not a voter",
    ErrLeadershipLost="leadership lost while committing log",
    ErrAbortedByRestore="snapshot restored while committing log",
    ErrRaftShutdown="raft is already shutdown",
    ErrEnqueueTimeout="timed out enqueuing operation",
    ErrNothingNewToSnapshot="nothing new to snapshot",
    ErrUnsupportedProtocol="operation not supported with current protocol version",
    ErrCantBootstrap="bootstrap only works on new clusters",
    ErrLeadershipTransferInProgress="leadership transfer in progress",
    ErrIncompatibleLogStore="log store does not implement some required methods or malformed",
    ErrTransportShutdown="transport shutdown",
    ErrPipelineShutdown="append pipeline closed",
    ErrLogNotFound="log not found",
    ErrPipelineReplicationNotSupported="pipeline replication not supported",
    errShortBuffer="encoding: short buffer",
)
SNAP_ERRS = dict(ErrNoSnapshot="snapstore: no such snapshot", ErrClosed="snapstore: sink closed")


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals). The facts (each
    package's `Base.lean`) are its `errors.New` variables' `errors.newVar`s, as craq's; raft's
    other variables (the three stable-store keys, `nextObserverID`) are allocated and initialized
    but not in the fact yet (S2 gives the fact the lab's `pkgGlobals`)."""
    SPECIAL, FIN_PRE = {}, g.FIN_PRE

    def errs_cfg(xs, extra_alloc):
        return dict(
            doc=f'''Its fact (`Base.lean`): its error variables ({", ".join("`" + x + "`" for x in xs)}, translated
`errors.New` calls) each hold `errors.New` of their message (`errors.newVar`). Its initializer
allocates its variables, initializes its imports and runs their translated initializers.''',
            imports=['Perennial.Proof.errors.NewVar'],
            alloc_types=dict({x: 'GoInterface' for x in xs}, **extra_alloc),
            before=dict({x: ['try wp_auto', f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{x} ⟨#S{x}, #M{x}⟩']
                         for x in xs}, **{'$end': ['try wp_auto']}),
            finish=[f'ipersist H{x}' for x in xs] + FIN_PRE[:6] + ['imodintro',
                   'unfold _root_.Perennial.errors.newVar'] +
                   [l for x in xs[:-1] for l in ['isplitr', f'· iexists _; iframe H{x} S{x} M{x}']] +
                   [f'iexists _; iframe H{xs[-1]} S{xs[-1]} M{xs[-1]}'])

    SPECIAL[HRAFT] = errs_cfg(list(RAFT_ERRS), {'keyCurrentTerm': 'GoSlice', 'keyLastVoteTerm': 'GoSlice',
                                                'keyLastVoteCand': 'GoSlice', 'nextObserverID': 'w64'})
    # in Go's order: inmem_store.go's `var _ CommitTrackingLogStore = &InmemCommitTrackingStore{}` (an
    # allocation), before kept.go's errors; progress.go's `var _ ReadCloserWrapper = &countingReadCloser{}`,
    # then raft.go's three keys (string-to-bytes conversions, named `-`: the fact does not read them)
    b = SPECIAL[HRAFT]['before']
    b['ErrTransportShutdown'] = ['try wp_auto', 'wp_alloc_anon'] + b['ErrTransportShutdown']
    b['keyCurrentTerm'] = ['try wp_auto', 'wp_alloc_anon', 'try wp_auto'] + [
        l for k in ('CurrentTerm', 'LastVoteTerm', 'LastVoteCand')
        for l in [f'wp_apply wp_string_to_bytes go!"{k}" as %_ ⟨-, -⟩', 'try wp_auto']]
    SPECIAL[f'{HRAFT}.examples.snapstore'] = errs_cfg(list(SNAP_ERRS), {})
    return SPECIAL
