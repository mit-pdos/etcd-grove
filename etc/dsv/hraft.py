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


# raft's three stable-store keys (raft.go), with the bytes they hold
RAFT_KEYS = dict(keyCurrentTerm="CurrentTerm", keyLastVoteTerm="LastVoteTerm", keyLastVoteCand="LastVoteCand")
# `RaftErr`'s constructors (`Base.lean`), in `RaftErr.all`'s order, with their variables
RAFT_ERR_CODES = dict(
    leader="ErrLeader", notLeader="ErrNotLeader", notVoter="ErrNotVoter",
    leadershipLost="ErrLeadershipLost", abortedByRestore="ErrAbortedByRestore",
    raftShutdown="ErrRaftShutdown", enqueueTimeout="ErrEnqueueTimeout",
    nothingNewToSnapshot="ErrNothingNewToSnapshot", unsupportedProtocol="ErrUnsupportedProtocol",
    cantBootstrap="ErrCantBootstrap", leadershipTransferInProgress="ErrLeadershipTransferInProgress",
    incompatibleLogStore="ErrIncompatibleLogStore", shortBuffer="errShortBuffer",
    transportShutdown="ErrTransportShutdown", pipelineShutdown="ErrPipelineShutdown",
    logNotFound="ErrLogNotFound", pipelineReplicationNotSupported="ErrPipelineReplicationNotSupported")


def raft_cfg(FIN_PRE):
    """raft's configuration: its fact is the lab's `pkgGlobals` (`Base.lean`): the error variables
    pairwise distinct (`errVals`), the keys' read-only bytes, `nextObserverID`'s invariant. The
    proof is the lab's `initialize.lean` (dsverify-lab examples/hraft/proof 241f27e), its lemmas in
    `InitLemmas.lean`: each `errors.New` by `wp_New_excl`, which keeps three quarters of the new
    `errorString`'s field (`exclS`), whence the variables' values are pairwise distinct
    (`exclS_nodup`)."""
    errs = list(RAFT_ERRS)
    assert sorted(errs) == sorted(RAFT_ERR_CODES.values())
    before = {x: ['try wp_auto', f'wp_apply wp_New_excl as %x{x} ⟨#S{x}, #E{x}, X{x}⟩'] for x in errs}
    # inmem_store.go's `var _ CommitTrackingLogStore = &InmemCommitTrackingStore{}` (an allocation)
    before['ErrTransportShutdown'] = ['try wp_auto', 'wp_alloc_anon'] + before['ErrTransportShutdown']
    # progress.go's `var _ ReadCloserWrapper = &countingReadCloser{}`, then raft.go's three keys
    before['keyCurrentTerm'] = ['try wp_auto', 'wp_alloc_anon', 'try wp_auto'] + [
        l for k, b in RAFT_KEYS.items()
        for l in [f'wp_apply wp_string_to_bytes go!"{b}" as %s{k} ⟨S{k}, -⟩', 'try wp_auto']]
    before['$end'] = ['try wp_auto']
    codes = list(RAFT_ERR_CODES.items())
    finish = [f'ipersist H{x}' for x in errs] + \
        [l for k in RAFT_KEYS for l in [f'ipersist S{k}', f'ipersist H{k}']] + [
        'imod inv_alloc nextObserverIDN ⊤ (∃ n : w64, globalAddr nextObserverID ↦ n) $$ [HnextObserverID]',
        '  with #Hobs',
        '· inext; iexists _; iexact HnextObserverID',
        'let g : RaftErr → Loc := fun c =>',
        '  match c with'] + [f'    | .{c} => x{x}' for c, x in codes] + [
        'ihave %Hnd := exclS_nodup g RaftErr.all $$ [' + ' '.join(f'X{x}' for _, x in codes) + ']',
        '· simp only [RaftErr.all, g]',
        '  iframe',
        '  iapply BigSepL.bigSepL_nil.2',
        '  iempintro',
        'have Hinj : Function.Injective',
        '    (fun c => interface.mkOk (go.GoType.PointerType errors.errorString.ty) #(g c)) := by',
        '  intro a b h',
        '  have h1 : g a = g b := by',
        '    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h',
        '    exact go.intoVal_inj h.2',
        '  have hall : ∀ c, c ∈ RaftErr.all := by intro c; cases c <;> simp [RaftErr.all]',
        '  exact nodup_map_inj g Hnd (hall a) (hall b) h1'] + FIN_PRE[:6] + [
        'imodintro',
        'unfold pkgGlobals',
        'isplitr',
        '· iexists (fun c => interface.mkOk (go.GoType.PointerType errors.errorString.ty) #(g c))',
        '  unfold errVals',
        '  isplitr',
        '  · ipureintro; exact Hinj',
        '  iapply (bigSepL_all _).2',
        '  simp only [g, RaftErr.var, RaftErr.msg]',
        '  iframe #'] + [
        l for _, x in codes[:-1]
        for l in ['  isplitr', f'  · iunfold errors.newVar; iexists _; iframe H{x} S{x} E{x}']] + [
        f'  iunfold errors.newVar; iexists _; iframe H{codes[-1][1]} S{codes[-1][1]} E{codes[-1][1]}'] + [
        l for k in RAFT_KEYS for l in ['isplitr', f'· iexists s{k}; iframe #']] + ['iexact Hobs']
    return dict(
        doc='''Its fact (`pkgGlobals`, `Base.lean`, the lab's): its error variables (translated `errors.New`
calls) hold pairwise distinct errors, each `errors.newVar` of its message (`errVals`), the three
stable-store keys read-only bytes, and `nextObserverID` an invariant. Its initializer allocates its
variables, initializes its imports and runs their translated initializers; the proof is the lab's
`initialize.lean` (its lemmas: `InitLemmas.lean`).''',
        imports=['Perennial.Proof.errors.NewVar', 'Dsverify.Proof.github_com.hashicorp.raft.InitLemmas'],
        alloc_types=dict({x: 'GoInterface' for x in errs}, **{k: 'GoSlice' for k in RAFT_KEYS},
                         nextObserverID='w64'),
        before=before,
        finish=finish)


def special(g):
    """Configurations of the kit's packages (`g`: etc/gen-init.py's globals). raft's fact is the
    lab's `pkgGlobals` (`raft_cfg`); snapstore's is its `errors.New` variables' `errors.newVar`s,
    as craq's."""
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

    SPECIAL[HRAFT] = raft_cfg(FIN_PRE)
    # snapstore's fact is the lab's `isInit` (its conjuncts named): unfolded before the conjuncts
    SPECIAL[f'{HRAFT}.examples.snapstore'] = errs_cfg(list(SNAP_ERRS), {})
    fin = SPECIAL[f'{HRAFT}.examples.snapstore']['finish']
    i = fin.index('unfold _root_.Perennial.errors.newVar')
    fin[i:i] = ['unfold isInit']
    return SPECIAL
