#!/usr/bin/env python3
"""Generate the package initialization proofs `Proof/<pkg>/Init.lean` (item 8).

Each file proves `<pkg>.wp_initialize'`: running the package's Goose `initialize'` from
`ownInitializing` gives its `isPkgInit`. The proof follows the translation's `initialize'` in
execution order (the `GlobalAlloc`s of the translated variables, the imports' `initialize'`, the
variables' initializers); an untranslated initializer (`X.init`, an axiom of the translation)
gets a trust-boundary axiom of the file: `opaqueInitsOk` (it runs), `errorsNewVarsInit` (it is
`errors.New(msg)`) or `<X>_init` (what a fact reads of it); then its `func init()`s, `init.<k>` (as
gc names them): a translated one is stepped into, an untranslated one (no `FuncUnfold`) gets the
trust-boundary axiom `initFuncsOk` (it returns). The packages are the import closure
of `ROOTS`, but Perennial's (with a `Link`), raft's (`Proof/go_etcd_io/raft/v3/Init.lean`), the
B-tree's (`initialize.lean`) and `NOT_YET`; a package whose fact is not `True` or whose
initializer runs translated code needs an entry in `SPECIAL` (the per-package doc, axioms, the
hand-written steps `before` an item, `$inits` (before the `init` functions) and `$end`, those
`after` a translated `init` function's call, and the `finish`).

Each theorem is proved in a form that keeps what is initialized (decision D19e,
`Proof/runtime/PkgInit.lean`): `wp_initialize'_lb` (from `ownInitLb g σ0`, for every `σ0`) or,
for a package whose import closure contains `PRE_RES` packages, `wp_initialize'_res` (from
`ownInitResL g L`, `Proof/runtime/PkgInitRes.lean`: for each `(q, R)` of `L`, `R` held unless `q`
is initialized; mustreg, 2026-11-20, until then one `(q, R)`, `ownInitRes g q R`);
`wp_initialize'` (Perennial's form, with the rights to register the closure's metric names,
`namesFree initNames`, for the latter) follows. The other packages' (Perennial's, raft's, the B-tree's) `_lb` forms
come from their `wp_initialize'` by `EtcdGrove.initLb_of_spec` (Perennial's
`initLb_of_initSpec`), over the initializers registered as `ExternalInit` in the generated
`Proof/runtime/PkgInitExt.lean` (Perennial's packages: one module for every tree) and, for the
others, in a tree's own registrations module (`EXT_LOCAL_MOD`: the main tree's
`Proof/runtime/PkgInitExtRaft.lean`, raft's, protobuf's `proto` and the B-tree's; `Dsverify/`'s
`PkgInitDsv.lean`; L1, 2026-11-24).

The parts `Net/` and `Dsverify/` import the main tree's `Init.lean` of every package for which the
main tree generates the same file (`shared_inits`): one per Go package. The parallel trees
`RaftWitness/` and `RaftNoAx/` get copies of the files they import that reached raft until L1
(`PARTS`: `PART_INITS`), and of `PkgInitExtRaft` over their raft, at `<part>/<path>`.
The part `PorcupineDag/` (porcupine PR #46) gets its own package's `Init.lean`, from its own
translation, and `Closures.lean`, the func literals its package fact names (`DAG_*`).

  etc/gen-init.py            regenerate every file
  etc/gen-init.py --check    exit 1 if a file differs from what would be generated
  etc/gen-init.py PKG...     regenerate these packages (Lean names, `go_etcd_io.etcd.pkg.v3.wait`)
"""
import glob, json, os, re, sys, types

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
# Perennial's checkout: the shared package's, or `$PERENNIAL_DIR` (a checkout at the manifest's pin, as
# `lake build --packages=<file>` builds against, when the shared one lags behind it)
PERENNIAL_CODE = os.path.join(os.environ.get('PERENNIAL_DIR', '.lake/packages/perennial'),
                              'Perennial', 'Code')
if not os.path.isdir(PERENNIAL_CODE):
    sys.exit(f'gen-init: no Perennial translations at {PERENNIAL_CODE}: fetch the pinned '
             'dependencies first (`lake env true`), or set PERENNIAL_DIR')

ROOTS = ['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc',
         # the auth plan's A3c (2026-10-24): the Lock and Election services' servers
         'go_etcd_io.etcd.server.v3.etcdserver.api.v3lock',
         'go_etcd_io.etcd.server.v3.etcdserver.api.v3election', 'go_etcd_io.etcd.server.v3.etcdserver',
         'go_etcd_io.etcd.client.v3', 'go_etcd_io.etcd.server.v3.etcdserver.read',
         'github_com.mit_pdos.etcd_grove.examples.etcd.putget',
         # putget_safe (2026-11-23, notes/putget-dist-plan.md): the member and client machines' package
         'github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget',
         # M2 (2026-10-27, notes/m2-plan.md): putget with the auto-compactor on
         'github_com.mit_pdos.etcd_grove.examples.etcd.compacted',
         # the client's `kv.Compact` (2026-11-01): putgetc under compaction pressure
         'github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch',
         # the closed lease example (2026-11-02, notes/lease-ex-plan.md)
         'github_com.mit_pdos.etcd_grove.examples.etcd.lease',
         # the closed lease-grant example (2026-11-02, notes/lease-grant-plan.md)
         'github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant',
         # the closed lease-expiry example (2026-11-04, notes/lease-expiry-plan.md, Part E)
         'github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry',
         # the multi-member lease example (2026-11-06, notes/lease-mono3-plan.md)
         'github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup',
         'github_com.mit_pdos.etcd_grove.examples.etcd.putget3',
         # the clusterN Scope (2026-11-15): putget3 with any number of members
         'github_com.mit_pdos.etcd_grove.examples.etcd.putgetN',
         # leaseN (2026-11-16, notes/leaseN-plan.md): the lease examples with any number of members
         'github_com.mit_pdos.etcd_grove.examples.etcd.leaseN',
         'github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN',
         # txnlinfaultsN (2026-11-15, notes/txnlinfaultsN-plan.md): partition with any number of members
         'github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN',
         # the restart plan (2026-11-02, notes/restart-plan.md): putget3 with a member restarted
         'github_com.mit_pdos.etcd_grove.examples.etcd.restart',
         # restartN (2026-11-15, notes/restartN-plan.md): restart3 with any number of members
         'github_com.mit_pdos.etcd_grove.examples.etcd.restartN',
         # restart S7 (2026-11-14, notes/restart-s7-scope.md): one member stopped and restarted
         'github_com.mit_pdos.etcd_grove.examples.etcd.restart1',
         'github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter',
         # (2026-11-22, notes/remote-port-plan.md) lintest's driver with an apply told the client id
         'github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient',
         # the scalable-proof experiment's log-applied register and its variants
         'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkv',
         'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvcompact',
         'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvsnap',
         'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw',
         'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvappend',
         # gokv's trusted_proph (kvraft's checker's prophecy; KvRaft copies its `Init.lean`), reached
         # from kvreconf's root until kvreconf's proofs retired (2026-11-24)
         'github_com.mit_pdos.gokv.trusted_proph',
         'github_com.mit_pdos.etcd_grove.examples.etcd.partition',
         'github_com.mit_pdos.etcd_grove.examples.etcd.txnlin',
         'github_com.mit_pdos.etcd_grove.examples.etcd.watch',
         'github_com.mit_pdos.etcd_grove.examples.etcd.cache',
         # the auth plan's E2b (2026-10-25): the authentication example
         'github_com.mit_pdos.etcd_grove.examples.etcd.auth',
         # the auth3 Scope's A1 (2026-11-14): authkv with three members
         'github_com.mit_pdos.etcd_grove.examples.etcd.auth3',
         # authN (2026-11-15, notes/authN-plan.md): auth3 with any number of members
         'github_com.mit_pdos.etcd_grove.examples.etcd.authN',
         # auth-lease S4 (2026-11-17, notes/auth-lease-s4-draft.md): authN's start with the lease rows
         'github_com.mit_pdos.etcd_grove.examples.etcd.authlease',
         # (2026-11-03) GetAny's logically atomic spec over a prophecy patch
         'github_com.mit_pdos.etcd_grove.examples.goose.prophkv',
         'go_etcd_io.etcd.client.v3.kubernetes',
         'github_com.mit_pdos.etcd_grove.examples.k8s.etcd3',
         # K4 of notes/k8s-compactor-plan.md (2026-11-04): Kubernetes' compactor example
         'github_com.mit_pdos.etcd_grove.examples.k8s.compactor',
         # (2026-11-20, notes/k8s-unified-scope.md) the one closed Kubernetes theorem's program: the two
         # drivers at once; no package variable, its fact `True` (`Base.lean`), so no `SPECIAL`
         'github_com.mit_pdos.etcd_grove.examples.k8s.all',
         # (2026-11-21, notes/etcd-unified-scope.md) the one closed etcd theorem's program: eleven
         # drivers at once; no package variable, its fact `True` (`Base.lean`), so no `SPECIAL`
         'github_com.mit_pdos.etcd_grove.examples.etcd.all',
         # KEP-6404 (2026-10-26): the watch cache and its store
         'k8s_io.apiserver.pkg.storage.cacher',
         # client-go's leaf libraries (2026-10-26, notes/k8s-clientgo-goose.md; `util/flowcontrol`
         # not yet: its `math/rand` instance is the gRPC server's, `Proof/k8s_io/client_go/Base.lean`)
         'k8s_io.client_go.util.workqueue', 'k8s_io.client_go.util.consistency',
         'k8s_io.client_go.util.retry', 'k8s_io.client_go.listers.apps.v1',
         'k8s_io.client_go.listers.core.v1',
         # the trace checker (2026-11-09, layer C of notes/trace-validation-plan.md): its fact says
         # what `Invariants` holds (`Violated`'s proof reads it)
         'github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft']
# (the closed trace-check program, `examples/raft/tracecheck`, was a root from 2026-11-11, S7 of
# notes/trace-validation-plan.md; it runs raft's `with_tla` build and is in the tree `RaftTla/`
# since the split of raft's two builds, so its `Init.lean` and `PkgTable.lean` are no longer
# generated here)
# (R10, 2026-11-07) mvcc's randomized tester (examples/mvccrand), for its closed theorem
ROOTS.append('github_com.mit_pdos.etcd_grove.examples.mvccrand')
# (F1 Draft, 2026-11-09) mvcc's full tester (examples/mvccfull): no package variables, its fact
# `True` (`Base.lean`), so no `SPECIAL`; its `PkgTable.lean` (`PROGRAMS`) is Prove's, for the closed
# theorem
ROOTS.append('github_com.mit_pdos.etcd_grove.examples.mvccfull')
# (2026-11-19) Kubernetes' conditional authorization's driver (examples/k8s/authz), for its closed
# theorem: it brings in `authorization/{authorizer,union}` (`SPECIAL` below), `authentication/user`
# and `util/validation` (names only, facts `True`, `authorizer/Base.lean`)
ROOTS.append('github_com.mit_pdos.etcd_grove.examples.k8s.authz')
# (fmt1-errno, 2026-11-24, #9 decision (B) 7127751995) the osfs examples (crashlog, walfs, bboltfs),
# whose closed theorems took their initializer as a hypothesis (`Hinit_wp`; bboltfs: its spec with
# `pkgFacts` as its post): now `os`'s path specs take `isPkgInit os`, and their `wp_initialize'` is
# generated (facts in their `PkgInit.lean`; bboltfs's `SPECIAL` below), with their package tables
ROOTS += ['github_com.mit_pdos.etcd_grove.examples.osfs.crashlog',
          'github_com.mit_pdos.etcd_grove.examples.osfs.walfs',
          'github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs']
# (WAL W4c, 2026-11-12, until 2026-11-15) the WAL robustness tester was a root here; it is the part
# `WalTester/`'s now (`wt_inits`), and the WAL reaches the closure through the server
# Packages of the closure still without a `wp_initialize'` (their facts are assumed: notes/STATUS.md,
# "Item 8: package initialization"); see also `ASSUMED`.
NOT_YET = set()
# Packages whose `wp_initialize'` is not proved: the packages importing them take their
# `initialize'.spec` (a `Spec/<pkg>/initialize.lean`) as a hypothesis `wp_<name>`.
# (2026-10-17: none; `read`'s was until its `MustRegister` had a spec, decision D16.)
ASSUMED = {}
# Packages whose initializer needs a resource besides `ownInitializing` (decision D16): its
# theorem's precondition is `ownInitializing get_is_pkg_init ∗ R`, and so is that of every package
# whose import closure contains it. They are proved in the `_res` form (decision D19e): `R` is held
# unless the package is initialized, so it is spent once, by the first initializer that runs the
# package, however many imports lead there.
# (mustreg, 2026-11-20) Every `PRE_RES` package's resource is the rights to register the metric
# names its translated `init()` registers (`prometheus.MustRegister`, D16): `namesFree` of its
# generated `regNames`; any number of them may be in a closure (`ownInitResL`'s list). The value:
# the registrations in `init()`'s order, `(x, collector, collectorName fact, (ns, sub, name))`
# (`reg_scalar`/`reg_vec` below build them from the metric's variable; filled in with the packages'
# configurations). Until then one package, read, its resource `EtcdGrove.read.readRegPerm`.
# (etcdstorage, 2026-11-20, the user's decision) auth, lease, backend and mvcc too: the closed
# theorems of mvccrand and mvccfull now take the premise `namesUnclaimed` (mustreg had left them out).
PRE_RES = {}
# (prom-registry, 2026-11-22) A `PRE_RES` package's IDs besides its names' (`regKeys`, `[]` by default):
# rights its initializer stores for a later registration of a collector of several descriptors (`v3rpc`:
# grpc-prometheus's server metrics, which `getServerMetrics` registers, their rights in `metricsP`). The
# entry's resource is `idToks γ (regNames.map descId ++ regKeys)` (`regRes`); `HK` in the initializer's
# steps.
REG_KEYS = {'go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc': 'EtcdGrove.grpc_prometheus.grpcKeys'}

def reg_scalar(x, ns, sub, name, c=None, n=None):
    """A registration of the metric `x` (a `GoInterface`: `c<x>`, its `collectorName` fact `N<x>`,
    from `metric_steps`)."""
    return (x, f'GoInterface.ok {c or "c" + x}', n or f'N{x}', (ns, sub, name))


def reg_vec(x, kind, ns, sub, name):
    """A registration of the metric vector `x` (a `*<kind>Vec` `v<x>`, `N<x>`: `vec_steps`)."""
    ty = f'_root_.Perennial.github_com.prometheus.client_golang.prometheus.{kind}Vec.ty'
    return (x, f'GoInterface.ok (interface.mk (go.GoType.PointerType {ty}) #v{x})', f'N{x}',
            (ns, sub, name))


def reg_steps(p, regs):
    """The steps registering `p`'s metrics `regs` (its `PRE_RES` entry) in its translated `init()`,
    from its rights `HR : idToks γ (regNames.map descId ++ regKeys)` (`$end`; prom-registry, route (b),
    2026-11-22: the rights keyed by ID, one `idToks γ [descId n]` per registration, taken from the
    front; until then `namesFree regNames`). Each registration is `prometheus.MustRegister`'s proof
    over `(*Registry).MustRegister`'s and `Register`'s, given the collector's `collectorName` (`#N<x>`,
    persistent) and prometheus's fact (an import's)."""
    L = []
    P = 'EtcdGrove.prometheus'
    for i, (x, c, n, (a, b, cc)) in enumerate(regs, 1):
        fq = f'({P}.fqName go!"{a}" go!"{b}" go!"{cc}")'
        if n.startswith('('):
            # a `NewGaugeFunc` gauge's `collectorName` is conditional on its name's validity (`N<x> :
            # ⌜nameOk ...⌝ → collectorName ...`): decided here
            L += [f'ihave #G{x} := (BI.pure_imp_elim (φ := {P}.nameOk {fq}) (by decide)) $$ N{x}']
            n = f'G{x}'
        L += [f'icases ({P}.idToks_names_cons (GF := GF) _ _ _ _).1 $$ HR with ⟨HR{i}, HR⟩',
              f'wp_apply wp_slice_literal (l := [{c}])', 'isplitr', '· ipureintro; rfl',
              f'iintro %s{i} ⟨S{i}, -⟩', 'try wp_auto',
              f'wp_apply ({P}.MustRegister.wp_proof ({P}.Registry.MustRegister.wp_proof'
              f' {P}.Registry.Register.wp_proof))',
              f'    _ _ _ {fq} (by decide +kernel) $$ [S{i} HR{i}] as S{i}',
              f'· iframe S{i} HR{i} {n}', '  try iframe #', '  try iPkgInit']
    return L


def register(cfg, p, regs):
    """`p` registers the metrics `regs` in its translated `init()` (`PRE_RES`, `reg_steps`): its
    metrics' constructor steps (`metric_steps`, `vec_steps`) keep their `collectorName` facts."""
    PRE_RES[p] = regs
    b = cfg.setdefault('before', {})
    for (x, _, n, _) in regs:
        if x not in b:
            continue
        for i, l in enumerate(b[x]):
            for a, z in [(f'⟨#C{x}, -⟩', f'⟨#C{x}, #{n}⟩'), (f'⟨#C{x}, #D{x}, -⟩', f'⟨#C{x}, #D{x}, #{n}⟩'),
                         (f'⟨#R{x}, -⟩', f'⟨#R{x}, #{n}⟩'), (f'⟨#L{x}, -⟩', f'⟨#L{x}, #{n}⟩')]:
                l = l.replace(a, z)
            b[x][i] = l
    b['$end'] = b.get('$end', []) + reg_steps(p, regs)


# Perennial packages without Perennial's `wp_initialize'` (names-only there): generated here.
PERENNIAL_HERE = {'runtime', 'internal.runtime.atomic', 'internal.runtime.sys'}
# (Go model overlays, 2026-11-24) the overlay-added `internal/gomodel` of the standard-library models
# is Perennial's at the pin (`Perennial.Proof.internal.gomodel.Link`: its `isPkgInit`, `wp_initialize'`).
# The `IsPkgInit` instances of `PERENNIAL_HERE` packages that are Perennial's (2026-11-03: `runtime`
# and its imports, which bbolt imports and whose `wp_initialize'` Perennial does not prove).
PERENNIAL_INST = {'runtime': 'Perennial.Proof.runtime.Base',
                  'internal.runtime.atomic': 'Perennial.Proof.internal.runtime.atomic.Base',
                  'internal.runtime.sys': 'Perennial.Proof.internal.runtime.sys.Base'}


def inventory(code='Code'):
    """Every translated package: its file, imports, untranslated initializers, translated vars
    (of the translation under `code`: `Code`, or a part's `<root>/Code`)."""
    out = {}
    files = sorted(glob.glob(code + '/**/*.lean', recursive=True)) + \
        sorted(glob.glob(PERENNIAL_CODE + '/**/*.lean', recursive=True))
    for f in files:
        t = open(f).read()
        m = re.search(r"instance info' : PkgInfo pkg_id\.(\S+) where", t)
        if not m:
            continue
        # a package this repository translates itself (`os`, project bboltfs's, 2026-11-03) is not
        # Perennial's, which no module here imports
        if m.group(1) in out and f.startswith(PERENNIAL_CODE):
            continue
        i = t.find("noncomputable def initialize'")
        body = t[i:t.find("\n\n", i)]
        out[m.group(1)] = dict(
            file=f, perennial=f.startswith(PERENNIAL_CODE),
            imports=re.findall(r"\(Val _root_\.Perennial\.(\S+)\.initialize'\)", body))
    return out


def instances(proof='Proof/'):
    """Where each package's `IsPkgInit` instance is (first in path order) and its fact (in the
    proofs under `proof`: `Proof/`, or a part's `<root>/Proof/`)."""
    loc = {}
    for f in sorted(glob.glob(proof + '**/*.lean', recursive=True)):
        t = open(f).read()
        for m in re.finditer(r"IsPkgInit \(IProp GF\) pkg_id\.(\S+?) :=\s*\n?\s*define_is_pkg_init\s+(\S+)", t):
            loc.setdefault(m.group(1).replace('«attribute»', 'attribute'), []).append(
                (f[len(proof):-len('.lean')], m.group(2)))
    return loc


inv = inventory()
inst = instances()
# (prom-registry, route (b), Option 4, 2026-11-22) Packages whose `IsPkgInit` instance is hand-written (not
# `define_is_pkg_init X`, which `instances()` finds): its module and fact. prometheus's fact takes a
# parameter (`IsPkgInitParam`, the run's registry ghost name `PromRegGS`).
INST_HAND = {'github_com.prometheus.client_golang.prometheus':
             ('github_com/prometheus/client_golang/prometheus/PkgInit', 'promInit')}
for _p, _m in INST_HAND.items():
    inst.setdefault(_p, [_m])
# The section variable of the parameter, in every generated file whose closure has prometheus (its
# `vars`/`table_vars`): the initializers' and tables' well-formedness instances take it.
PROMREG_VAR = '[promreg_gs : EtcdGrove.prometheus.PromRegGS GF]'
# (net-swap, etcd-dist D2, 2026-11-22) the main tree's `net` is the part `Net/`'s translation (over the
# net extension; `etc/goose.py`'s `net=Net`), with its `IsPkgInit` instance in `Net/Proof/net/Base.lean`
# (`isInit`); its `Init.lean` is generated here over the main tree's imports (`Net/`'s own imports the
# part's copies of `os`'s initializers). `@` marks a full module name.
inv['net'] = inventory('Net/Code')['net']
inst['net'] = [('@Net.Proof.net.Base', 'isInit')]
# (#24 J3, 2026-11-23) the encoding/json model's same-package methods in membership
# (`json_model_gen.go`, `etc/goose.py`'s overlay) call `models.lab/jsoncodec`, the part `Net/`'s
# translation (`models.lab=Net`), with its `IsPkgInit` instance in
# `Net/Proof/models_lab/jsoncodec/Base.lean` (`True`); its main-tree `Init.lean` is generated here
# over the main tree's imports, as `net`'s (and as #37's `models_lab.pbcodec`).
inv['models_lab.jsoncodec'] = inventory('Net/Code')['models_lab.jsoncodec']
inst['models_lab.jsoncodec'] = [('@Net.Proof.models_lab.jsoncodec.Base', 'iprop(True)')]

# Per-package configuration of the packages with facts or translated initializers.
SPECIAL = {}

# (prove-errinits, 2026-11-19) translated `errors.New` / verb-less `fmt.Errorf` package variables:
# the steps of the initializer of `x`, Perennial's `errors.wp_New_errorString` (`%x<x> #M<x>`) or, with
# the message cell, `EtcdGrove.wp_New_errorString_cell` (`%x<x> ⟨#M<x>, #C<x>⟩`); a `fmt.Errorf`
# without `%` goes through `EtcdGrove.fmt.wp_Errorf_noPct` (Perennial's `fmt.wp_Errorf`: Go's `Errorf`
# without verbs returns `errors.New(format)`; fmtmodel, 2026-11-20: until then it unfolded the model).
NEWVAR_IMPORTS = ['Perennial.Proof.errors.NewVar']
NEWVAR_CELL_IMPORTS = ['Proof.errors.NewVarCell']

def newvar_steps(x, cell=False, errorf=None):
    # `errorf`: the format of a `fmt.Errorf(format)` call (no argument); the step into `Errorf`'s
    # model is true of Go only for a format without `%` (no verb, so no `%w`: Go's `Errorf` returns
    # `errors.New(format)`, as the model does; `etc/errorf-wrap-check.py`)
    if errorf is not None:
        assert '%' not in errorf, (x, errorf)
    if errorf is not None:
        # (fmtmodel, 2026-11-20) through Perennial's `fmt.wp_Errorf` (`EtcdGrove.fmt.wp_Errorf_noPct`)
        pat = f'⟨#M{x}, #C{x}⟩' if cell else f'⟨#M{x}, -⟩'
        return ['try wp_auto',
                f'-- `fmt.Errorf({json.dumps(errorf)})`: no verb, Go returns `errors.New` of the format',
                f'wp_apply (EtcdGrove.fmt.wp_Errorf_noPct _ _ (by decide)) $$ [] as %x{x} {pat}',
                '· iframe #; iapply ownSlice_nil']
    pre = ['try wp_auto']
    if cell:
        return pre + [f'wp_apply EtcdGrove.wp_New_errorString_cell as %x{x} ⟨#M{x}, #C{x}⟩']
    return pre + [f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{x} ⟨#_, #M{x}⟩']

def newvars_cfg(cfg, names, cell=False, errorf={}):
    """Add the translated `errors.New` variables `names` to the package config `cfg` (those in
    `errorf`, a map to their formats, are `fmt.Errorf` calls without arguments or `%`)."""
    cfg.setdefault('alloc_types', {}).update({x: 'GoInterface' for x in names})
    cfg.setdefault('before', {}).update(
        {x: newvar_steps(x, cell, errorf.get(x)) for x in names})
    imps = cfg.setdefault('imports', [])
    imps += [m for m in NEWVAR_IMPORTS + (NEWVAR_CELL_IMPORTS if cell else []) +
             (['Proof.fmt.OutLemmas'] if errorf else []) if m not in imps]
    return cfg

_ETCD_ERRMSGS = dict(ErrUnknownMethod="etcdserver: unknown method",
        ErrStopped="etcdserver: server stopped",
        ErrCanceled="etcdserver: request cancelled",
        ErrTimeout="etcdserver: request timed out",
        ErrTimeoutDueToLeaderFail="etcdserver: request timed out, possibly due to previous leader failure",
        ErrTimeoutDueToConnectionLost="etcdserver: request timed out, possibly due to connection lost",
        ErrTimeoutLeaderTransfer="etcdserver: request timed out, leader transfer took too long",
        ErrTimeoutWaitAppliedIndex="etcdserver: request timed out, waiting for the applied index took too long",
        ErrLeaderChanged="etcdserver: leader changed",
        ErrNotEnoughStartedMembers="etcdserver: re-configuration failed due to not enough started members",
        ErrLearnerNotReady="etcdserver: can only promote a learner member which is in sync with leader",
        ErrNoLeader="etcdserver: no leader",
        ErrNotLeader="etcdserver: not leader",
        ErrRequestTooLarge="etcdserver: request is too large",
        ErrNoSpace="etcdserver: no space",
        ErrTooManyRequests="etcdserver: too many requests",
        ErrUnhealthy="etcdserver: unhealthy cluster",
        ErrCorrupt="etcdserver: corrupt cluster",
        ErrBadLeaderTransferee="etcdserver: bad leader transferee",
        ErrClusterVersionUnavailable="etcdserver: cluster version not found during downgrade",
        ErrWrongDowngradeVersionFormat="etcdserver: wrong downgrade target version format",
        ErrKeyNotFound="etcdserver: key not found")
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.errors'] = newvars_cfg(dict(
    doc='''Its fact (`errorsInit`, `errors/Base.lean`): `ErrNoSpace` holds a pointer error. Its
initializer allocates its variables and runs their translated initializers, `errors.New` calls
(`errors.go`; until 2026-11-19 the trust-boundary axiom `errorsNewVarsInit`).''',
    finish=['ipersist HErrNoSpace', 'iframe Hown', 'imodintro', 'isplitr',
            '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish', 'try (isplitl []; · (imodintro; itrivial))', 'imodintro', 'iexists _',
            'iframe HErrNoSpace', 'ipureintro', 'exact ⟨_, _, rfl, rfl⟩'],
), list(_ETCD_ERRMSGS), cell=True)


def raft_subpath(seg, tag):
    """(2026-10-24, rafthttp stage 6d) `X = path.Join(RaftPrefix, seg)` (`http.go`): the slice
    literal, `path.Join`'s proof (over `path.Clean`'s and `lazybuf`'s), its model's value."""
    es = f'[go!"/raft", go!"{seg}"]'
    return ['try wp_auto',
            f'wp_apply (wp_slice_literal (l := {es})); isplitr; (· ipureintro; rfl); iintro %pj{tag} ⟨Sj{tag}, -⟩',
            'try wp_auto',
            'wp_apply (EtcdGrove.path.Join.wp_proof (EtcdGrove.path.Clean.wp_proof '
            'EtcdGrove.path.lazybuf.index.wp_proof EtcdGrove.path.lazybuf.append.wp_proof '
            f'EtcdGrove.path.lazybuf.string.wp_proof)) _ {es} _ (by decide) $$ [$Sj{tag}] as %rj{tag} ⟨%Hj{tag}, -⟩',
            f'subst Hj{tag}',
            f'rw [show EtcdGrove.path.joinModel {es} = go!"/raft/{seg}" from by decide]',
            'try wp_auto']

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'] = dict(
    doc='''Its fact (`rafthttpInit`, `etcdserver/BaseApply.lean`): `ErrExceedSizeLimit` holds a non-nil
error, `linkHeartbeatMessage` a heartbeat message without unknown fields, read-only for good. Its
initializer runs its variables' initializers: (prove-errinits, 2026-11-19) its errors' are translated,
`errors.New` calls and verb-less `fmt.Errorf` calls (`msg_codec.go`, `http.go`, `peer.go`,
`stream.go`; `fmt.Errorf`'s trusted model is `errors.New(format)`), until then the trust-boundary axiom
`errorsNewVarsInit`; (prove-misc, 2026-11-20) `linkHeartbeatSize = proto.Size(&linkHeartbeatMessage)`
(`stream.go`) is translated, over `proto.SizePb`'s spec at the registered `raftpb.Message` (until then
the trust-boundary axiom `linkHeartbeatSize_init`).
(const-inits, 2026-11-19) The timeouts and intervals (`snapResponseReadTimeout`, `ConnWriteTimeout`,
`proberInterval`, `statusMonitoringInterval`, `statusErrorInterval`), `errMemberNotFound`
(`fmt.Errorf`, its proof) and `supportedStream` (a map literal of slice literals) are translated
and set (until then the trust-boundary axioms `<X>_init` and `opaqueInitsOk`).
`RaftPrefix` (`"/raft"`), its subpaths `ProbingPrefix`, `RaftStreamPrefix` and `RaftSnapshotPrefix`
(`path.Join`, proved), `ConnReadTimeout` (`DefaultConnReadTimeout`, five seconds), `readBytesLimit`
(512 MiB) and (raft-entsize, route H1, 2026-11-10) `linkHeartbeatMessage`
(`raftpb.Message{Type: raftpb.MsgHeartbeat.Enum()}`, `stream.go`: `Enum`'s proof inlined, the
literal frozen by `hbMsg_init`) are translated and set. (metric-vecs, 2026-11-19) So are its metric
vectors (`metrics.go`: `sentBytes`, `activePeers`, `rttSec`, the snapshot metrics, ...), over
prometheus's `New<Kind>Vec` specs, each with its label names (`vecLabels`; until then the
trust-boundary axioms `<X>_init`).''',
    alloc_types={'RaftPrefix': 'GoString', 'ConnReadTimeout': 'w64', 'readBytesLimit': 'w64',
                 'ProbingPrefix': 'GoString', 'RaftStreamPrefix': 'GoString',
                 'RaftSnapshotPrefix': 'GoString',
                 'linkHeartbeatMessage': '_root_.Perennial.go_etcd_io.raft.v3.raftpb.Message',
                 'snapResponseReadTimeout': 'w64', 'errMemberNotFound': 'GoInterface',
                 'ConnWriteTimeout': 'w64', 'proberInterval': 'w64', 'statusMonitoringInterval': 'w64',
                 'statusErrorInterval': 'w64', 'supportedStream': 'Loc', 'linkHeartbeatSize': 'w64'},
    # `ConnReadTimeout = DefaultConnReadTimeout`: the constant's value, for the store to step;
    # (2026-10-24, rafthttp stage 6d) the three subpaths of `RaftPrefix`: `path.Join` (proved)
    before={'ConnReadTimeout': ['simp only [DefaultConnReadTimeout]', 'try wp_auto'],
            'ConnWriteTimeout': ['simp only [DefaultConnWriteTimeout]', 'try wp_auto'],
            'ProbingPrefix': raft_subpath('probing', 'P'),
            'RaftStreamPrefix': raft_subpath('stream', 'S'),
            'RaftSnapshotPrefix': raft_subpath('snapshot', 'N'),
            # (const-inits, 2026-11-19) the stream types each version supports (`stream.go`): a
            # `map[string][]streamType` literal of 13 slice literals, each slice made then inserted
            'supportedStream': ['try wp_auto',
                'wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) go.string (go.GoType.SliceType streamType.ty)) as %mss Hss',
                'try wp_auto'] + [l for i in range(13) for l in [
                f'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sss{i} ⟨Sss{i}, -⟩',
                'try wp_auto',
                'wp_apply (wp_mapInsert (K := GoString) (V := GoSlice) go.string) $$ Hss as Hss', 'try wp_auto']],
            # (const-inits, 2026-11-19) `errMemberNotFound = fmt.Errorf("member not found")`, translated
            'errMemberNotFound': ['wp_apply (_root_.Perennial.fmt.wp_Errorf_argsWf go!"member not found" slice.nil [] _root_.Perennial.fmt.ArgsWf.nil) $$ [] as %emnf -',
                                  '· iframe #; iapply ownSlice_nil', 'try wp_auto'],
            # (raft-entsize, route H1, 2026-11-10) `Message{Type: MsgHeartbeat.Enum()}`, translated:
            # `Enum`'s proof, the literal stored, frozen at its content `hbC` (`hbMsg_init`)
            'linkHeartbeatMessage': ['try wp_auto',
                'haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩',
                'wp_apply (show EtcdGrove.raftpb.MessageType.Enum.spec (GF := GF) (hG := hG) from by '
                'intro x; wp_start; wp_auto; iapply HΦ; iframe) (W32 8) as %phb Hphb',
                'try wp_auto',
                'imod (EtcdGrove.hbMsg_init _ _ ⊤) $$ [HlinkHeartbeatMessage Hphb] with #HlinkHeartbeatMessage',
                '· iframe HlinkHeartbeatMessage Hphb'],
            # (prove-misc, 2026-11-20) `proto.Size(&linkHeartbeatMessage)`: `SizePb` at the registered
            # `raftpb.Message`, the heartbeat read-only at a content of bounded size (`hbMsg_msgRoC`)
            'linkHeartbeatSize': ['try wp_auto',
                'icases (EtcdGrove.hbMsg_msgRoC _) $$ [HlinkHeartbeatMessage] with ⟨%chb, #Hchb, %Hchb⟩',
                '· iexact HlinkHeartbeatMessage',
                'have wpShb := EtcdGrove.proto.SizePb.wp_proof (GF := GF) (hG := hG) EtcdGrove.pbMessageC EtcdGrove.pbMessageC_reg (globalAddr linkHeartbeatMessage) chb',
                'simp only [EtcdGrove.pbMessageC_ty, EtcdGrove.pbMessageC_roC, EtcdGrove.pbMessageC_size] at wpShb',
                'wp_apply wpShb $$ [$Hchb] as %nlinkHeartbeatSize %HnlinkHeartbeatSize',
                'have BlinkHeartbeatSize : 0 ≤ sint.Z nlinkHeartbeatSize ∧ sint.Z nlinkHeartbeatSize < 2 ^ 50 := by',
                '  have hlt := EtcdGrove.msgSize_lt_of_ok chb Hchb.2.2.2',
                '  have he := HnlinkHeartbeatSize (by omega)',
                '  omega',
                'try wp_auto']},
    # (const-inits, 2026-11-19) a lookup in a map literal finds one of its values
    pre=['/-- A lookup in `<[k := v]> m` finds `v` or one of `m`\'s values. -/',
         'theorem EtcdGrove.lookup_insert_some {K V : Type} [DecidableEq K] (m : GMap K V) (k k\' : K) (v w : V)',
         '    (h : (<[k := v]> m) !! k\' = some w) : w = v ∨ m !! k\' = some w := by',
         '  rw [GMap.lookup_insert_eq_iff] at h',
         '  by_cases hk : k = k\' <;> simp [hk] at h <;> simp [h]', ''],
    imports=['Proof.path.Join', 'Proof.path.Clean', 'Proof.path.lazybuf__index',
             'Proof.path.lazybuf__append', 'Proof.path.lazybuf__string',
             'Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum',
             'Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2',
             'Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PerTypeMessage',
             'Proof.google_golang_org.protobuf.proto.SizePb'],
    finish=['ipersist HErrExceedSizeLimit', 'ipersist HerrIncompatibleVersion',
            'ipersist HErrClusterIDMismatch', 'ipersist HerrStopped', 'ipersist HerrMemberRemoved',
            'ipersist HRaftPrefix', 'ipersist HProbingPrefix', 'ipersist HRaftStreamPrefix',
            'ipersist HRaftSnapshotPrefix', 'ipersist HConnReadTimeout', 'ipersist HConnWriteTimeout',
            'ipersist HlinkHeartbeatSize',
            'ipersist HreadBytesLimit', 'ipersist HerrUnsupportedStreamType',
            'ipersist HsupportedStream', 'ipersist HsnapResponseReadTimeout', 'ipersist HerrMemberNotFound',
            'ipersist Hss'] + [f'ipersist Sss{i}' for i in range(13)] + [
            'iframe Hown', 'imodintro', 'isplitr',
            '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish',
            'try (isplitl []; · (imodintro; itrivial))', 'imodintro', 'isplitr',
            '· simp only [EtcdGrove.errorsNewVar]; iframe #',
            'isplitr', '· iexact HlinkHeartbeatMessage',
            'isplitr', '· iexact HRaftPrefix',
            'isplitr', '· iexact HProbingPrefix', 'isplitr', '· iexact HRaftStreamPrefix',
            'isplitr', '· iexact HRaftSnapshotPrefix',
            'simp only [EtcdGrove.errorsNewVar, EtcdGrove.errVarCells, EtcdGrove.errVarCell]',
            'iframe #',
            # `supportedStream`'s slices: each entry one of the 13 literals
            'isplitl []', '· ipureintro; exact BlinkHeartbeatSize',
            'imodintro', 'iintro %k %sl %Hk',
            'repeat\' (rcases EtcdGrove.lookup_insert_some _ _ _ _ _ Hk with rfl | Hk)',
            'all_goals (first | (iexists _; iassumption) | simp at Hk)'],
)


FIN_PRE = ['iframe Hown', 'imodintro', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
           'is_pkg_init_finish', 'try (isplitl []; · (imodintro; itrivial))', 'imodintro']

# (phase 7 S5, 2026-11-24) net/url's character-class table `table` (`encoding_table.go`), translated:
# an array literal of 86 keyed constants (what `shouldEscape`/`ishex` read, for the ServeMux's
# `EscapedPath`/`PathUnescape`); its value is `encTableList` (`Proof/net/url/Escape.lean`: Go's
# generator's reference functions), by evaluation
SPECIAL['net.url'] = dict(
    doc='''Its fact (`urlInit`, `url/PkgInit.lean`): `table` holds `encTableList`, the entries
`gen_encoding_table.go` computes, read-only for good. Its initializer allocates `table`, initializes
`strings` and stores the table's literal (phase 7 S5, 2026-11-24: translated, with `shouldEscape`,
`unescape`, `escape`, `EscapedPath`).''',
    alloc_types={'table': 'GoArray w8 256'},
    before={'table': ['try wp_auto']},
    finish=['ipersist Htable'] + FIN_PRE + ['unfold urlInit', 'iexists _; iframe Htable',
            'ipureintro', 'set_option maxRecDepth 100000 in decide'],
)


# (2026-11-19) Kubernetes' conditional authorization (KEP-5681, project k8s-authz)
SPECIAL['k8s_io.apiserver.pkg.authorization.authorizer'] = dict(
    doc='''Its fact (`authorizerInit`, `authorizer/Base.lean`): `ErrorConditionEvaluationNotSupported`
holds some error, read-only for good. Its initializer allocates it, initializes its imports and runs
its translated initializers: the interface assertions `var _ Condition = GenericCondition{}` and
`var _ Authorizer = AuthorizerFunc(nil)` (conversions to interfaces) and `errors.New(...)`
(Perennial's `errors.wp_New`, `interfaces.go`).''',
    imports=['Perennial.Proof.errors.Link'],
    alloc_types={'ErrorConditionEvaluationNotSupported': 'GoInterface'},
    before={'$end': ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New as %xE -',
                     'try wp_auto']},
    finish=['ipersist HErrorConditionEvaluationNotSupported'] + FIN_PRE[:6] +
           ['imodintro', 'unfold authorizerInit',
            'iexists _; iexact HErrorConditionEvaluationNotSupported'],
)
# (prove-k8s4, 2026-11-21) apimachinery's `fields`: its two variables with their initializers
SPECIAL['k8s_io.apimachinery.pkg.fields'] = dict(
    doc='''Its fact is `True`. Its initializer allocates its variables, initializes its imports and runs their
translated initializers (`selector.go`): `valueEscaper = strings.NewReplacer(...)` of three pairs
(Perennial's `strings.wp_NewReplacer`, translated since Perennial 60800ea5e) and `termOperators`, a slice
literal of the operator constants (prove-k8s4, 2026-11-21; until then the trust-boundary axiom
`opaqueInitsOk`).''',
    alloc_types={'valueEscaper': 'Loc', 'termOperators': 'GoSlice'},
    before={'$end': ['try wp_auto',
        'wp_apply (wp_slice_literal (l := [go!"\\\\", go!"\\\\\\\\", go!",", go!"\\\\,", go!"=", go!"\\\\="]));'
        ' isplitr; (· ipureintro; rfl); iintro %pEsc ⟨SEsc, -⟩',
        'try wp_auto',
        'wp_apply (_root_.Perennial.strings.wp_NewReplacer _',
        '    [go!"\\\\", go!"\\\\\\\\", go!",", go!"\\\\,", go!"=", go!"\\\\="] _ (by decide)) $$ [SEsc] as %r ⟨-, -⟩',
        '· iframe SEsc',
        'try wp_auto',
        'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pOps ⟨-, -⟩',
        'try wp_auto']},
)
# (2026-11-19) apimachinery's `util/validation/field` (names only but `NewPath`,
# `ErrorList.ToAggregate` and `(*Error).Error`'s code, translated with bodies)
SPECIAL['k8s_io.apimachinery.pkg.util.validation.field'] = dict(
    doc='''Its fact (`fieldInit`, `storage/etcd3/Base.lean`): `omitValue`'s address is not `nil`
(`(*Error).ErrorBody` loads it). Its initializer allocates it (the allocation gives its points-to,
hence the address), initializes its imports, and runs its translated initializers: `omitValue`'s
(`OmitValueType{}`, `errors.go`) and `var _ error = &Error{}` (an allocation; prove-smallinits,
2026-11-20: until then `opaqueInitsOk`).''',
    alloc_types={'omitValue': 'k8s_io.apimachinery.pkg.util.validation.field.OmitValueType'},
    before={'$end': ['try wp_auto', 'repeat (wp_alloc_anon; try wp_auto)']},
    finish=['ihave %Hnn := typedPointsto_not_null _ _ _ $$ HomitValue'] + FIN_PRE[:6] +
           ['try (imodintro; ipureintro; exact Hnn)'],
)
SPECIAL['k8s_io.apiserver.pkg.authorization.union'] = dict(
    doc='''Its fact is `True`. Its initializer initializes its imports and runs its translated
initializer, the interface assertion `var _ = authorizer.Authorizer(unionAuthzHandler{})` (a
conversion to an interface, `union.go`).''',
    before={'$end': ['try wp_auto']},
)

# bbolt (project bbolt, translated with bodies, 2026-11-03; facts in
# `Proof/go_etcd_io/bbolt/PkgInit.lean`)
_BBOLT_ERRS = ['ErrDatabaseNotOpen', 'ErrInvalid', 'ErrInvalidMapping', 'ErrVersionMismatch', 'ErrChecksum', 'ErrTimeout', 'ErrTxNotWritable', 'ErrTxClosed', 'ErrDatabaseReadOnly', 'ErrFreePagesNotLoaded', 'ErrBucketNotFound', 'ErrBucketExists', 'ErrBucketNameRequired', 'ErrKeyRequired', 'ErrKeyTooLarge', 'ErrValueTooLarge', 'ErrMaxSizeReached', 'ErrIncompatibleValue', 'ErrSameBuckets', 'ErrDifferentDB']
_BBOLT_VARS = [x for x in _BBOLT_ERRS if x != 'ErrBucketNotFound']
# (maintainer 16) `bboltErrorsVars` ends with `ErrBucketNotFound`'s `bboltErrVar` (its `fmtErrorOk`,
# for `DeleteBucket`'s deferred log line)
_BBOLT_VARSX = _BBOLT_VARS + ['ErrBucketNotFound']
SPECIAL['go_etcd_io.bbolt.errors'] = dict(
    doc='''Its fact (`bboltErrorsInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `ErrBucketNotFound`
holds an `errors.New` error, a leaf pointer error without an `Is` method
(`EtcdGrove.ErrorStringLeaf`, of the method set goose emits). Its initializer allocates its
variables and runs their translated initializers, `errors.New` calls (`errors/errors.go`;
Perennial's `errors.wp_New_errorString`); the other variables' errors are `*errorString` pointer errors and
`fmtErrorOk` (`EtcdGrove.errorString_fmtErrorOk`, `Proof/errors/ErrorStringOk.lean`).''',
    imports=['Perennial.Proof.errors.NewVar', 'Proof.errors.NewVar', 'Proof.errors.ErrorStringOk'],
    alloc_types={x: 'GoInterface' for x in _BBOLT_ERRS},
    vars=['[_root_.Perennial.errors.Assumptions]'],
    before=dict({x: ['try wp_auto', f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{x} ⟨#_, #M{x}⟩']
                 for x in _BBOLT_ERRS}, **{'$end': ['try wp_auto']}),
    finish=[f'ipersist H{x}' for x in _BBOLT_ERRS] + FIN_PRE + ['iexists _', 'iframe HErrBucketNotFound',
            'isplitr', '· ipureintro',
            '  exact ⟨⟨_, _, rfl, rfl⟩, EtcdGrove.ErrorStringLeaf.leaf _, EtcdGrove.ErrorStringLeaf.noIs⟩',
            'unfold go_etcd_io.bbolt.errors.bboltErrorsVars go_etcd_io.bbolt.errors.bboltErrVar'] +
           # (batch 30) each other variable: an `errors.New` pointer error, `fmtErrorOk` by
           # `EtcdGrove.errorString_fmtErrorOk` of its method spec `M{x}`
           [l for x in _BBOLT_VARSX[:-1] for l in ['isplitr', f'· iexists _; iframe H{x}; isplitr',
                                                   '  · ipureintro; exact ⟨⟨_, _, rfl, rfl⟩, rfl⟩',
                                                   f'  iapply EtcdGrove.errorString_fmtErrorOk; iexact M{x}']] +
           [f'iexists _; iframe H{_BBOLT_VARSX[-1]}; isplitr', '· ipureintro; exact ⟨⟨_, _, rfl, rfl⟩, rfl⟩',
            f'iapply EtcdGrove.errorString_fmtErrorOk; iexact M{_BBOLT_VARSX[-1]}'],
)

SPECIAL['go_etcd_io.bbolt.internal.common'] = dict(
    doc='''Its fact (`bboltCommonInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `DefaultPageSize` holds
4096, for good. Its initializer allocates `DefaultPageSize`, initializes its imports and
runs its translated initializer, `DefaultPageSize = os.Getpagesize()` (`types.go`), whose callee is
names-only in Perennial: the trust-boundary axiom `os.Getpagesize.wp_proof` (4096 on linux/amd64).''',
    imports=['Proof.os.Getpagesize'],
    alloc_types={'DefaultPageSize': 'w64'},
    before={'DefaultPageSize': ['try wp_auto', 'wp_apply EtcdGrove.os.Getpagesize.wp_proof'],
            '$end': ['try wp_auto']},
    finish=['ipersist HDefaultPageSize'] + FIN_PRE[:6]
)

# the deprecated aliases of bbolt's root package (`errors.go`)
_BBOLT_ROOT_ERRS = ['ErrDatabaseNotOpen', 'ErrInvalid', 'ErrInvalidMapping', 'ErrVersionMismatch',
                    'ErrChecksum', 'ErrTimeout', 'ErrTxNotWritable', 'ErrTxClosed',
                    'ErrDatabaseReadOnly', 'ErrFreePagesNotLoaded', 'ErrBucketNotFound',
                    'ErrBucketExists', 'ErrBucketNameRequired', 'ErrKeyRequired', 'ErrKeyTooLarge',
                    'ErrValueTooLarge', 'ErrIncompatibleValue']
# (2026-11-04) the trust-boundary assumption that the program runs on linux/amd64: `runtime.GOOS`
# and `runtime.GOARCH` (constants, axiom `val`s of Perennial's names-only `runtime`) are `"linux"`
# and `"amd64"`. Stated here, in
# `runtime`'s initialization, since it is a fact of the platform the program starts on; `runtime`'s
# `IsPkgInit` instance is Perennial's (its fact: `buildVersion` holds some string), so the fact is surfaced through bbolt's, the one
# package that branches on `GOOS` (`Proof/go_etcd_io/bbolt/PkgInit.lean`, `bboltRootInit`).
SPECIAL['runtime'] = dict(
    doc='''Its fact (Perennial's `runtime.isInit`, `Perennial/Proof/runtime/Base.lean`): `buildVersion`,
which `Version` returns, holds some string, read-only for good. Its initializer runs the trusted
model of `buildVersion`'s initialization (Perennial's `TrustedCode/runtime.lean`: it allocates the
variable and stores an arbitrary string, the linker's; Perennial's `runtime.wp_buildVersion_init`,
whose cell is made persistent here), initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return. (Until Perennial
`160fcf12a`, 2026-11-23, its fact was `True` and `buildVersion` untranslated.)

And the trust-boundary assumptions `GOOS_linux` and `GOARCH_amd64`: the program runs on
linux/amd64 (`runtime.GOOS` and `runtime.GOARCH`, constants that goose leaves axiom `val`s, are
`"linux"` and `"amd64"`), as the repository's other platform facts
assume linux/amd64 (`os.Getpagesize` returns 4096, `Spec/os/Getpagesize.lean`; the Linux file
extension `fsExt`). `runtime`'s `IsPkgInit` instance is Perennial's, whose fact says nothing of
`GOOS`/`GOARCH`, so the
packages that read `GOOS`/`GOARCH` state them in their own facts from these axioms (bbolt's root package,
`bboltRootInit`).''',
    # (pin bump 160fcf12a, 2026-11-23) Perennial's trusted model of `buildVersion`'s initialization
    trusted={'buildVersion': ['wp_apply _root_.Perennial.runtime.wp_buildVersion_init as Hbv']},
    # (Perennial 612f4641b) the model stores the fixed `buildVersionValue`
    finish=['ipersist Hbv'] + FIN_PRE[:6],
    pre=['namespace runtime', '',
         '/-- **The trust boundary: the program runs on Linux.** `runtime.GOOS` is the constant',
         '`"linux"` (Go\'s `GOOS` of the build; goose translates `runtime` names-only, so it is an',
         'axiom `val` with no value). Satisfiable: `GOOS` is an uninterpreted constant. -/',
         'axiom GOOS_linux [GooseExts] [GoGlobalContext] :',
         '    _root_.Perennial.runtime.GOOS = #(go!"linux")', '',
         '/-- **The trust boundary: the program runs on amd64.** `runtime.GOARCH` is the constant',
         '`"amd64"` (Go\'s `GOARCH` of the build; an axiom `val` with no value, as `GOOS`). Satisfiable:',
         '`GOARCH` is an uninterpreted constant. -/',
         'axiom GOARCH_amd64 [GooseExts] [GoGlobalContext] :',
         '    _root_.Perennial.runtime.GOARCH = #(go!"amd64")', '',
         'end runtime', ''],
)

# (2026-11-19) `ErrLength` translated (an `errors.New` call; until then `opaqueInitsOk`)
SPECIAL['encoding.hex'] = dict(
    doc='''Its fact is `True`. Its initializer allocates `ErrLength`, initializes its imports and runs
its translated initializer (`hex.go`: `errors.New("encoding/hex: odd length hex string")`; Perennial's
`errors.wp_New_errorString`).''',
    imports=['Perennial.Proof.errors.NewVar'],
    alloc_types={'ErrLength': 'GoInterface'},
    before={'ErrLength': ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New_errorString as %_ ⟨#_, #_⟩',
                          'try wp_auto']},
    finish=FIN_PRE[:6],
)

SPECIAL['go_etcd_io.bbolt'] = dict(
    doc='''Its fact (`bboltRootInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `runtime.GOOS` is
`"linux"` and `runtime.GOARCH` `"amd64"` (the trust-boundary axioms `runtime.GOOS_linux` and
`runtime.GOARCH_amd64` of `runtime`'s `Init.lean`; bbolt compares `GOOS` with `"windows"` in
`DB.grow`, `DB.mmap` and `DB.allocate`, and its loggers format both). Its initializer allocates its variables, initializes its imports and
runs their translated initializers: `trySolo` (an `errors.New` call, `db.go`; Perennial's
`errors.wp_New_errorString`), the deprecated aliases of
`errors`' variables (loads of them), `discardLogger` (`&nopLogger{}`, the fork's no-op logger,
which the fact records: a `*nopLogger`), and `DefaultOptions` (`&Options{...}`, an allocation;
translated since 2026-11-17, `Code/go_etcd_io/bbolt.toml`).''',
    imports=['Perennial.Proof.errors.NewVar'],
    alloc_types=dict({x: 'GoInterface' for x in _BBOLT_ROOT_ERRS}, trySolo='GoInterface',
                     discardLogger='GoInterface', DefaultOptions='Loc'),
    before={'trySolo': ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New_errorString as %xS ⟨#_, #MS⟩'],
            # the deprecated aliases load `errors`' variables: its fact's `bboltErrorsVars`
            'ErrDatabaseNotOpen': ['try wp_auto',
                'ihave #Hev : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []',
                '· iapply isPkgInit_access $$ {Hd:go_etcd_io.bbolt.errors}',
                'unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars go_etcd_io.bbolt.errors.bboltErrVar',
                'icases Hev with ⟨%_, #HvErrBucketNotFound, %_, ' + ', '.join(f'⟨%v{x}, #Hv{x}, %_, #-⟩' for x in _BBOLT_VARS) + ', -⟩'],
            # `&Options{...}`: a literal of the translated struct, allocated (2026-11-17)
            'DefaultOptions': ['try wp_auto'],
            # `&nopLogger{}`: an allocation (of a zero-size struct), which `wp_auto` leaves
            'discardLogger': ['try wp_auto', 'wp_alloc lg as Hlg', 'try wp_auto'],
            '$end': ['try wp_auto']},
    # (batch 34) the fact's `discardLogger` clause: the store of `&nopLogger{}`, persisted
    finish=['ipersist HdiscardLogger', 'iframe Hown', 'is_pkg_init_finish',
            'isplitr', '· ipureintro; exact isPanic_intoVal _', 'imodintro', 'imodintro', 'isplitr',
            '· ipureintro; exact ⟨runtime.GOOS_linux, runtime.GOARCH_amd64⟩',
            'iexists _', 'iexact HdiscardLogger'],
)

# (2026-11-03) `os` is this repository's (project bboltfs's), for every project: names only (its
# variables' initializers untranslated); until then Perennial's, raft's `Init.lean` by hand.
class _AnyType(dict):
    """`alloc_types` that leaves every variable's type to Lean (`V := _`)."""
    def get(self, k, d=None):
        return '_'


_ALLOC_ANY = _AnyType()

# (#24 J2, 2026-11-23) the encoding/json model's codec registry with its bodies: `codecMu` and
# `codec`, zero (the registry's mutex and its nil `*Codec`), left to the program: a deployment that
# registers a codec takes `codecMu`'s mutex and `codecUnset` (half of `codec` at nil) from its boot,
# as net/rpc's (`Proof/encoding/json/Registry.lean`).
SPECIAL['encoding.json'] = dict(
    doc='''Its fact is `True`. Its initializer allocates the codec registry's variables (`codecMu`, `codec`:
zero) and initializes its imports (`sync`, `io`); a program that registers a codec takes the
registry's mutex and the codec's nil cell from its boot (`Registry.lean`: `codecInv`, `codecUnset`).''',
    alloc_types=_ALLOC_ANY,
)

SPECIAL['os'] = dict(
    doc='''Its fact (`Proof/os/PkgInit.lean`): `Stderr` holds a fixed `*File`, which raft's
initializer loads (`defaultLogger`). `os` is this repository's translation (project bboltfs's): its
initializer initializes its imports and runs its variables' translated initializers (`errors.New`
errors, io/fs's and internal/poll's error variables, `sync.OnceValue`, function values) and the
trusted models of the standard streams' (`TrustedCode/os.lean`: `Stdin`, `Stdout` nothing, `Stderr`
an arbitrary in-range address with no cell, not reserved, `GoPrealloc`), then its translated `init`
function, which calls the trusted model of
`runtime_args` (an arbitrary `[]string`). (Until 2026-11-07 the trust-boundary axioms
`opaqueInitsOk`, `Stderr_init`, `initFuncsOk`; until 2026-11-03, over Perennial's `os`, in raft's
`Init.lean`.)''',
    imports=['Proof.os.Models', 'Perennial.Proof.sync.Link', 'Perennial.Proof.errors.NewVar'],
    alloc_types=_ALLOC_ANY,
    before={'dirBufPool': [
        'ihave #FS : (iprop((∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrInvalid) e DFrac.discard) ∗ (∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrPermission) e DFrac.discard) ∗ (∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrExist) e DFrac.discard) ∗ (∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrNotExist) e DFrac.discard) ∗ (∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrClosed) e DFrac.discard)) : IProp GF) $$ []',
        '· iapply isPkgInit_access $$ {Hd:io.fs}',
        'icases FS with ⟨⟨%fe1, #F1⟩, ⟨%fe2, #F2⟩, ⟨%fe3, #F3⟩, ⟨%fe4, #F4⟩, ⟨%fe5, #F5⟩⟩',
        'ihave #PL : (iprop((∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.internal.poll.ErrNoDeadline) e DFrac.discard) ∗ (∃ x : Loc, typedPointsto (globalAddr _root_.Perennial.internal.poll.ErrDeadlineExceeded) (interface.mkOk (go.GoType.PointerType _root_.Perennial.internal.poll.DeadlineExceededError.ty) #x) DFrac.discard) ∗ (∃ x : Loc, typedPointsto (globalAddr _root_.Perennial.internal.poll.ErrFileClosing) (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) : IProp GF) $$ []',
        '· iapply isPkgInit_access $$ {Hd:internal.poll}',
        'icases PL with ⟨⟨%pe1, #P1⟩, ⟨%pe2, #P2⟩, ⟨%pe3, #P3⟩⟩',
        'repeat (first',
        '  | wp_apply _root_.Perennial.errors.wp_New_errorString as %_ ⟨#_, #_⟩',
        '  | (wp_func_call; wp_call)',
        '  | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)',
        '  | wp_auto)']},
    trusted={'Stdin': ['try wp_call'], 'Stdout': ['try wp_call'],
             'Stderr': ['wp_apply wp_Stderr_init as ⟨%stderr, HStderr⟩',
                        'repeat (first',
                        '  | wp_apply _root_.Perennial.errors.wp_New_errorString as %_ ⟨#_, #_⟩',
                        '  | (set_option maxRecDepth 20000 in',
                        '     wp_apply _root_.Perennial.sync.wp_OnceValue as %_ -)',
                        '  | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)',
                        '  | wp_auto)']},
    after={'init.«0»': [
        'repeat (first',
        '  | wp_apply _root_.Perennial.errors.wp_New_errorString as %_ ⟨#_, #_⟩',
        '  | (set_option maxRecDepth 20000 in wp_apply _root_.Perennial.sync.wp_OnceValue as %_ -)',
        # (featuregate-3, 2026-11-23) named: the fact keeps `Args`' slice, read-only
        '  | (wp_func_call; wp_apply wp_runtime_args_impl as %argsl ⟨%argsxs, Hargs, -⟩)',
        '  | wp_auto)']},
    finish=['ipersist HStderr', 'iframe Hown', 'imodintro', 'isplitr',
            '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish'],
)

# (fmt1-errno, 2026-11-24) minibolt (examples/osfs/bboltfs): its three `errors.New` variables, non-nil
SPECIAL['github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs'] = newvars_cfg(dict(
    doc='''Its fact (`bboltfsInit`, `PkgInit.lean`): `errFailed`, `errPageSize` and `errMapTooLarge` hold
non-nil errors, read-only for good. Its initializer allocates its variables (those and `envErrors`, zero),
initializes its imports and runs its variables' translated initializers (`errors.New` calls).''',
    alloc_types={'envErrors': 'w64'},
    finish=['ipersist HerrFailed', 'ipersist HerrPageSize', 'ipersist HerrMapTooLarge'] + FIN_PRE + [
            'unfold bboltfsInit', 'iexists _, _, _', 'iframe HerrFailed HerrPageSize HerrMapTooLarge',
            'ipureintro', 'exact ⟨nofun, nofun, nofun⟩'],
), ['errPageSize', 'errFailed', 'errMapTooLarge'])

# (2026-11-07) this repository's `syscall`, `io/fs`, `internal/poll` and `internal/syscall/unix`
# (project bboltfs's) translate their variables' initializers, as Perennial's (fix-semantics Case
# 33): the steps of Perennial's own proofs (`Perennial/Proof/{syscall,io/fs,internal/poll}/
# initialize.lean`).
SPECIAL['syscall'] = dict(
    doc='''Its fact is `True` (`Proof/syscall/PkgInit.lean`). Its initializer initializes `sync`
and runs its variables' translated initializers (`envs = runtime_envs()`, whose trusted model is an
arbitrary `[]string`; `copyenv = sync.OnceFunc(...)`, constants, a map, `sync.Pool` and `mmapper`
literals), then its `init` function, whose trusted model does nothing (`TrustedCode/syscall.lean`:
the RLIMIT_NOFILE raise, unobservable to what Perennial models).''',
    imports=['Proof.syscall.Models', 'Perennial.Proof.sync.Link'],
    alloc_types=_ALLOC_ANY,
    before={'$inits': [
        'wp_func_call',
        'unfold runtime_envs.impl',
        'wp_apply syscall.wp_arbitraryStrings as %envsl ⟨%xs, Henvsl, Henvscap⟩',
        'set_option maxRecDepth 20000 in',
        'wp_apply _root_.Perennial.sync.wp_OnceFunc as %cpe -',
        'try unfold EAGAIN EINVAL ENOENT',
        'repeat (first',
        '  | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)',
        '  | wp_auto)',
        'wp_apply wp_map_make1 (K := Loc) (V := GoSlice) as %mref Hm',
        'try wp_auto']},
    heavy=True,
    finish=['ipersist Herrors', 'iframe Hown', 'imodintro', 'isplitr',
            '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish',
            # the error table's fact (`errorsOk`): each entry, a literal, within `errnoMsgMax`
            'try imodintro', 'unfold syscall.errorsOk', 'iexists _', 'iframe Herrors', 'ipureintro',
            'dsimp only',
            'repeat (refine syscall.forall_mem_set_of _ _ (by simp [syscall.errnoMsgMax]) ?_)',
            'intro s hs', 'rw [List.eq_of_mem_replicate hs]', 'decide'],
)

SPECIAL['io.fs'] = dict(
    doc='''Its fact (`Proof/os/PkgInit.lean`): its five error variables, which `os`'s initializer
copies, hold some error for good. Its initializer copies internal/oserror's errors into them
(`errInvalid()`, ...) and makes `SkipDir` and `SkipAll` (`errors.New`).''',
    imports=['Perennial.Proof.internal.oserror.Link', 'Perennial.Proof.errors.NewVar'],
    alloc_types=_ALLOC_ANY,
    before={'$end': [
        'ihave #Hos := _root_.Perennial.internal.oserror.isInit_access $$ {Hd:internal.oserror}',
        'icases Hos with ⟨#VIn, #VPe, #VEx, #VNE, #VCl⟩',
        'iunfold _root_.Perennial.errors.newVar at VIn VPe VEx VNE VCl',
        'icases VIn with ⟨%xIn, #OIn, #_, #EIn⟩',
        'icases VPe with ⟨%xPe, #OPe, #_, #EPe⟩',
        'icases VEx with ⟨%xEx, #OEx, #_, #EEx⟩',
        'icases VNE with ⟨%xNE, #ONE, #_, #ENE⟩',
        'icases VCl with ⟨%xCl, #OCl, #_, #ECl⟩',
        'wp_func_call', 'wp_call', 'wp_auto', 'ipersist HErrInvalid',
        'wp_func_call', 'wp_call', 'wp_auto', 'ipersist HErrPermission',
        'wp_func_call', 'wp_call', 'wp_auto', 'ipersist HErrExist',
        'wp_func_call', 'wp_call', 'wp_auto', 'ipersist HErrNotExist',
        'wp_func_call', 'wp_call', 'wp_auto', 'ipersist HErrClosed',
        'wp_apply _root_.Perennial.errors.wp_New_errorString as %xSD ⟨#_, #ESD⟩',
        'wp_apply _root_.Perennial.errors.wp_New_errorString as %xSA ⟨#_, #ESA⟩']},
    finish=['iframe Hown', 'is_pkg_init_finish'],
)

SPECIAL['internal.syscall.unix'] = dict(alloc_types=_ALLOC_ANY)

# (2026-11-24, rand-retire) `math.rand` is Perennial's (47ec64a9d translates its global generator and
# proves its `wp_initialize'`, fact `isInit`); from 2026-11-23 to then its fact was `True` here and its
# `Init.lean` generated.

# (2026-11-14, the WAL over fsExt: `wal.Create` returns `os.ErrExist`, non-nil) `io/fs` and `os` record
# `ErrExist`'s error non-nil (`Proof/os/PkgInit.lean`; the part `LinuxFs/`'s until 2026-11-15, now the
# main tree's: `SPECIAL['os']`, `SPECIAL['io.fs']` below).
# (2026-11-14, `wal.Exist`'s `errors.Is(err, os.ErrNotExist)`) `os` also records
# `ErrNotExist`'s error (some error, for good).
# (2026-11-14, `WAL.Close` of a nil `dirFile`: the nil-receiver `(*File).Close` returns `os.ErrInvalid`,
# `Spec/os/File__CloseNil.lean`) `os` also records `ErrInvalid`'s error.
_lfs_fs_ex = '(∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrExist) e DFrac.discard)'
_lfs_fs_ex_nn = ('(∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr '
                 '_root_.Perennial.io.fs.ErrExist) e DFrac.discard)')
# (2026-11-14, the closed-file `(*os.File).Close` returns `&PathError{"close", name, ErrClosed}`,
# `Spec/os/File__CloseClosed.lean`) `io/fs` and `os` record `ErrClosed`'s error as
# one `fmt` formats (`fmtErrorOk`: internal/oserror's `errors.New`, `errorString_fmtErrorOk`).
# (2026-11-14, `wal-vsnap4`: `ValidSnapshotEntries`' `errors.Is(err, os.ErrNotExist)` on errors with `errIsTerm`,
# a pointer target) `io/fs` and `os` record `ErrNotExist`'s error as an `*errorString`
# (internal/oserror's `errors.New`).
_lfs_fs_ne = '(∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrNotExist) e DFrac.discard)'
# (2026-11-22, `errors.IsPathErrnoNotExist.spec`: `syscall.Errno.Is` compares its target with internal/oserror's
# `ErrNotExist`) and as internal/oserror's `ErrNotExist` error, which they copy.
_lfs_fs_ne_ptr = ('(∃ x : Loc, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrNotExist) (interface.mkOk '
                  '(go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗ '
                  'typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist) (interface.mkOk '
                  '(go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)')
_lfs_fs_cl = '(∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrClosed) e DFrac.discard)'
_lfs_fs_cl_ok = ('(∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗ typedPointsto (globalAddr '
                 '_root_.Perennial.io.fs.ErrClosed) e DFrac.discard)')
LFS_IOFS = dict(SPECIAL['io.fs'])
LFS_IOFS['doc'] = SPECIAL['io.fs']['doc'].replace('hold some error for good.',
    'hold some error for good, `ErrExist` a non-nil one, `ErrNotExist` an `*errorString`, `ErrClosed` one `fmt`\nformats.')
LFS_IOFS['imports'] = SPECIAL['io.fs']['imports'] + ['Proof.errors.ErrorStringOk']
# (`is_pkg_init_finish` proves the pure conjunct and frames `ErrClosed`'s `fmtErrorOk`)
LFS_IOFS['finish'] = ['ihave #HClOk := EtcdGrove.errorString_fmtErrorOk xCl _ $$ ECl'] + SPECIAL['io.fs']['finish']
LFS_OS = dict(SPECIAL['os'])
LFS_OS['doc'] = SPECIAL['os']['doc'].replace("which raft's\ninitializer loads (`defaultLogger`).",
    "which raft's\ninitializer loads (`defaultLogger`), `ErrExist` a non-nil error, `ErrNotExist` an\n`*errorString`, `ErrInvalid` some error, `ErrClosed` one `fmt` formats (io/fs's), `checkWrapErr`\n`false`, `Args` some `[]string`, read-only.")
LFS_OS['before'] = {'dirBufPool': [l.replace(_lfs_fs_ex, _lfs_fs_ex_nn).replace('⟨%fe3, #F3⟩', '⟨%fe3, %hfe3, #F3⟩')
                                    .replace(_lfs_fs_cl, _lfs_fs_cl_ok).replace(_lfs_fs_ne, _lfs_fs_ne_ptr).replace('⟨%fe5, #F5⟩', '⟨%fe5, #F5ok, #F5⟩')
                                    .replace('⟨%fe4, #F4⟩', '⟨%fe4, #F4, #F4o⟩')
                                   for l in SPECIAL['os']['before']['dirBufPool']]}
# (2026-11-22, `io.CopyFiles.spec`'s proof: `(*File).wrapErr` of an error reads `checkWrapErr`, a translated
# `var` that only os's tests set) `os` also records `checkWrapErr` false, for good.
# (featuregate-3, 2026-11-23: `flag`'s `init` reads `os.Args[0]`) and `Args`' slice, read-only for good.
LFS_OS['finish'] = ['ipersist HStderr', 'ipersist HErrExist', 'ipersist HErrNotExist', 'ipersist HErrInvalid',
                    'ipersist HErrClosed', 'ipersist HcheckWrapErr',
                    # (featuregate-3, 2026-11-23) `Args`' slice, read-only for good (`flag`'s `init`)
                    'ipersist HArgs', 'ipersist Hargs', 'iframe Hown', 'imodintro', 'isplitr',
                    '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish']

# (WAL leaf specs, 2026-11-13) the part's bufio, internal/filepathlite and path/filepath: their
# translated `errors.New` variables; fact `True` (`PkgInit.lean`).
_BUFIO_ERRS = ['ErrInvalidUnreadByte', 'ErrInvalidUnreadRune', 'ErrBufferFull', 'ErrNegativeCount',
               'errNegativeRead', 'errNegativeWrite', 'ErrTooLong', 'ErrNegativeAdvance',
               'ErrAdvanceTooFar', 'ErrBadReadCount', 'ErrFinalToken']
SPECIAL['bufio'] = dict(
    imports=['Perennial.Proof.errors.NewVar'],
    alloc_types=_ALLOC_ANY,
    # (#23, 2026-11-22: keyed `errorRune` until it was skipped, goose `[[skip]]`; it ran last)
    before={'$end': ['try wp_auto'] + [f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{i} ⟨#_, #E{i}⟩'
                     for i in range(len(_BUFIO_ERRS))]},
    finish=['iframe Hown', 'is_pkg_init_finish'],
)
# (featuregate-3, 2026-11-23) `flag` (project etcd's, `Code/flag.toml`: featuregate imports it): its
# translated `errors.New` variables and `Usage` (a function literal), then `init.0`, which reads
# `os.Args` (`os`'s fact: some read-only `[]string`) and makes `CommandLine` (`NewFlagSet`, translated);
# fact `True` (`Proof/flag/PkgInit.lean`).
SPECIAL['flag'] = dict(
    doc='''Its fact is `True` (`Proof/flag/PkgInit.lean`). Its initializer initializes its imports, allocates
its variables, runs their translated initializers (`ErrHelp`, `errParse`, `errRange`: `errors.New`;
`Usage`: a function literal) and its translated `init` function, which reads `os.Args` (`os`'s fact:
some `[]string`, read-only) and sets `CommandLine` to `NewFlagSet(os.Args[0], ExitOnError)`, or
`NewFlagSet("", ExitOnError)` when `os.Args` is empty, then its `Usage` field (featuregate-3,
2026-11-23).''',
    imports=['Perennial.Proof.errors.NewVar'],
    alloc_types=_ALLOC_ANY,
    before={'ErrHelp': ['try wp_auto'] + [f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{i} ⟨#_, #E{i}⟩'
                                          for i in range(3)] + ['try wp_auto']},
    after={'init.«0»': [
        'ihave #HA := _root_.Perennial.os.args_of_pkgInit $$ {Hd:os}',
        'icases HA with ⟨%argsl, %argsxs, #HArgs, #Hargs⟩',
        'ihave %Hlen := ownSlice_len _ _ _ $$ Hargs',
        'try wp_auto',
        'wp_if_destruct',
        # `os.Args` empty: `NewFlagSet("", ExitOnError)` (inlined), then `CommandLine.Usage = ...`
        '· try wp_auto',
        '  wp_func_call',
        '  wp_call',
        '  try unfold ExitOnError',
        '  wp_auto',
        '  iframe Hown',
        '  is_pkg_init_finish',
        # non-empty: `os.Args[0]`, read from `os`'s fact
        '· try wp_auto',
        '  have hpos : 0 < sint.Z argsl.len := by',
        '    have h0 : sint.Z argsl.len ≠ 0 := fun h => Hif (by word)',
        '    omega',
        '  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z argsl.len := ⟨by decide, by word⟩',
        '  have hxl : 0 < argsxs.length := by word',
        '  (try simp only [hb, _root_.and_self, ↓reduceIte])',
        "  wp_apply wp_load_slice_index argsl (sint.Z (W64 0)) argsxs DFrac.discard (argsxs[0]'hxl)",
        '    hb.1 $$ [Hargs] as -',
        '  · iframe #; ipureintro; simp [List.getElem?_eq_getElem hxl]',
        '  wp_func_call',
        '  wp_call',
        '  try unfold ExitOnError',
        '  wp_auto',
        '  iframe Hown',
        '  is_pkg_init_finish']},
    # (each branch above finishes)
    finish=[],
)
# (#23, 2026-11-22: path.filepath's keyed `SkipDir` until it, `SkipAll` and `lstat`, which ran after
# `ErrBadPattern`, were skipped, goose `[[skip]]`)
# (#23, 2026-11-22) k8s api/meta's `errNotList`, `errNotObject` (`fmt.Errorf` without a verb, read by the
# proved `Accessor`/`ListAccessor`, so goose cannot skip them) translated, until then `opaqueInitsOk`
newvars_cfg(SPECIAL.setdefault('k8s_io.apimachinery.pkg.api.«meta»', {}), ['errNotList', 'errNotObject'],
            errorf=dict(errNotList="object does not implement the List interfaces",
                        errNotObject="object does not implement the Object interfaces"))
# (#23, 2026-11-22) the cacher's `consistency.PanicOnCacheInconsistency = false` (read by the proved
# snapshotter, so goose cannot skip it) translated, until then `opaqueInitsOk`
# (k8s-inits-2, 2026-11-24, #32) and its `init` (`checker.go:50`) translated and proved, until then
# `initFuncsOk`
_GETENV_PARSEBOOL = ['wp_apply EtcdGrove.os.Getenv.wp_proof as %_ -', 'try wp_auto',
                     'wp_apply EtcdGrove.strconv.ParseBool.wp_proof as %_ %_ -', 'try wp_auto']
SPECIAL['k8s_io.apiserver.pkg.storage.cacher.consistency'] = dict(
    doc='''Its fact is `True` (its readers, the watch cache's snapshotter and `checkSnapshotResourceVersion`,
are proved only where they do not reach the load). Its initializer allocates
`PanicOnCacheInconsistency`, initializes its imports, runs the variable's translated initializer
(`false`) and its translated `init` (`checker.go:50`), which stores in it whether
`KUBE_WATCHCACHE_CONSISTENCY_CHECKER` parses as true (`os.Getenv`: the trust-boundary axiom
`os.Getenv.wp_proof`; `strconv.ParseBool.wp_proof`, proved over Perennial's translation). (Until
2026-11-24 the `init` was names-only, the trust-boundary axiom `initFuncsOk`.)''',
    alloc_types=_ALLOC_ANY,
    imports=['Proof.os.Getenv', 'Proof.strconv.ParseBool'],
    before={'$inits': ['try wp_auto']},
    after={'init.«0»': _GETENV_PARSEBOOL},
)
# (#23, 2026-11-22) k8s util/validation's `IsQualifiedName = content.IsLabelKey` (read by the translated
# `v1helper.IsExtendedResourceName`, so goose cannot skip it) translated, until then `opaqueInitsOk`
SPECIAL['k8s_io.apimachinery.pkg.util.validation'] = dict(
    alloc_types=_ALLOC_ANY,
    before={'$end': ['try wp_auto']},
)
# (#23, 2026-11-22) k8s utils/buffer's `ErrInvalidSize` (`errors.New`, read by the translated
# `NewTypedRingFixed`, so goose cannot skip it) translated, until then `opaqueInitsOk`
for _p, _k in [('internal.filepathlite', '$end'), ('path.filepath', '$end'), ('k8s_io.utils.buffer', '$end')]:
    SPECIAL[_p] = dict(
        imports=['Perennial.Proof.errors.NewVar'],
        alloc_types=_ALLOC_ANY,
        before={_k: ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New_errorString as %x0 ⟨#_, #E0⟩']},
        finish=['iframe Hown', 'is_pkg_init_finish'],
    )

# (WAL W6, 2026-11-13) the part's `pkg/v3/ioutil` (the page writer): `defaultBufferBytes`, a
# translated `var` (`128 * 1024`), read-only for good (`PkgInit.lean`)
LFS_SPECIAL = {}  # the part's packages whose main-tree namesake has another configuration
LFS_SPECIAL['go_etcd_io.etcd.pkg.v3.ioutil'] = dict(
    doc='''Its fact (`ioutilInit`, `PkgInit.lean`): `defaultBufferBytes` holds `128 * 1024`, read-only for
good. Its initializer stores that value and runs the translated initializers of its other variables,
`ErrShortRead` and `ErrExpectEOF` (`readcloser.go`: `fmt.Errorf` without verbs, whose trusted model is
`errors.New(format)`; until 2026-11-19 untranslated, `opaqueInitsOk`).''',
    alloc_types={'defaultBufferBytes': 'w64'},
    finish=['ipersist HdefaultBufferBytes'] + FIN_PRE[:-2],
)
newvars_cfg(LFS_SPECIAL['go_etcd_io.etcd.pkg.v3.ioutil'], ['ErrShortRead', 'ErrExpectEOF'],
            errorf={'ErrShortRead': 'ioutil: short read', 'ErrExpectEOF': 'ioutil: expect EOF'})
# (WAL package init, 2026-11-13) the part's `walpb`: `ErrCRCMismatch`, a translated `errors.New`
LFS_SPECIAL['go_etcd_io.etcd.server.v3.storage.wal.walpb'] = dict(
    doc='''Its fact (`walpbInit`, `PkgInit.lean`): `ErrCRCMismatch` holds for good an error whose `Error()`
returns (`errOk`) and on which `errors.Is` returns for every pointer target (`errIsTerm`: an `*errorString`
leaf, `errIsTerm_errorString`), an `*errorString` whose field holds its message (2026-11-22, `WalDecEnvSupply`'s
proof: it differs from `io.EOF`). Its initializer stores that error (a translated `errors.New` call, record.go;
Perennial's `errors.wp_New_errorString`), initializes its imports and runs the untranslated
initializers of its protobuf descriptors and its `init` function, which the trust-boundary axioms
`opaqueInitsOk` and `initFuncsOk` say run without panicking.''',
    imports=['Perennial.Proof.errors.NewVar', 'Proof.errors.ErrIsTerm', 'Proof.errors.ErrorStringOk'],
    alloc_types={'ErrCRCMismatch': 'GoInterface'},
    before={'ErrCRCMismatch': ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New_errorString as %xC ⟨#ECc, #EC⟩',
                               'try wp_auto']},
    finish=['ipersist HErrCRCMismatch', 'ihave #TC := EtcdGrove.errIsTerm_errorString xC $$ {Hd:errors}'] +
           FIN_PRE[:6] + [
        'imodintro', 'unfold EtcdGrove.walpb.walpbInit', 'iexists _',
        'iframe HErrCRCMismatch TC', 'isplitl', '· iapply EtcdGrove.errorString_errOk', '  iexact EC',
        'iexists xC', 'iframe ECc', 'ipureintro', 'rfl'],
)
# (WAL package init, 2026-11-13) the part's `fileutil`: the lock functions, chosen by its `init`'s
# `F_OFD_GETLK` probe (`syscall.FcntlFlock.wp_getlk`: any errno, so either), `wrlck`, `ErrLocked`
LFS_SPECIAL['go_etcd_io.etcd.client.pkg.v3.fileutil'] = dict(
    doc='''Its fact (`fileutilInit`, `PkgInit.lean`): the lock functions `linuxLockFile`/`linuxTryLockFile`
(both OFD's or both `flock`'s), the write-lock description `wrlck` and `ErrLocked` (an error whose
`Error()` returns), read-only for good. Its initializer stores `ErrLocked` (a translated `errors.New`),
`wrlck` (a struct literal) and the `flock` functions, initializes its imports and runs its translated
`init` function (lock_linux.go), which probes OFD locks with `F_OFD_GETLK` on fd 0 and switches both
functions to OFD's on success: the probe's errno is any (`syscall.FcntlFlock.wp_getlk`), so either
outcome.''',
    imports=['Perennial.Proof.errors.NewVar', 'Proof.syscall.FileOps', 'Proof.errors.ErrorStringOk'],
    vars=['[ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]'],
    alloc_types={'linuxLockFile': 'GoFunc', 'linuxTryLockFile': 'GoFunc', 'wrlck': 'syscall.Flock_t',
                 'ErrLocked': 'GoInterface'},
    before={'ErrLocked': ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New_errorString as %xL ⟨#_, #EL⟩',
                          'try wp_auto']},
    after={'init.«0»': [
        "wp_apply (_root_.Perennial.EtcdGrove.syscall.FcntlFlock.wp_getlk _ _ _) $$ getlk as %e ⟨%v', Hv, %hv⟩",
        'try wp_auto', 'ipersist Hwrlck', 'ipersist HErrLocked',
        'ihave #Hrest : (∃ e : GoInterfaceOk, globalAddr ErrLocked ↦□ GoInterface.ok e ∗ EtcdGrove.errOk e) ∗',
        '    (∃ w : syscall.Flock_t, globalAddr wrlck ↦□ w ∗',
        "      ⌜w.Type' = W16 1 ∧ w.Whence' = W16 0 ∧ w.Start' = W64 0 ∧ w.Len' = W64 0 ∧",
        "        w.Pid' = W32 0⌝) $$ []",
        '· isplitl []', '  · iexists _', '    iframe HErrLocked',
        '    iapply EtcdGrove.errorString_errOk', '    iexact EL',
        '  · iexists _', '    iframe Hwrlck', '    ipureintro', '    exact ⟨rfl, rfl, rfl, rfl, rfl⟩',
        'by_cases he : e = 0'] +
        [l for ofd, eq, simps in
         [('true', 'interface.nil', '↓reduceIte'),
          ('false', 'interface.mkOk syscall.Errno.ty #e', '↓reduceIte, Bool.false_eq_true')]
         for l in [f'· rw [show errnoErr e = {eq} from by unfold errnoErr; simp only [he, ↓reduceIte]]',
                   '  wp_auto', '  ipersist HlinuxLockFile', '  ipersist HlinuxTryLockFile'] +
                  ['  ' + x for x in FIN_PRE[:6]] +
                  ['  imodintro', '  unfold EtcdGrove.fileutil.fileutilInit', '  icases Hrest with ⟨Hr1, Hr2⟩',
                   '  iframe Hr1 Hr2', f'  iexists {ofd}',
                   f'  simp only [EtcdGrove.fileutil.lockFn, EtcdGrove.fileutil.tryLockFn, {simps}]',
                   '  iframe HlinuxLockFile HlinuxTryLockFile']]},
    # (the `init` function's steps close the proof, in both branches)
    finish=[],
)
# (WAL package init, 2026-11-13) the part's WAL: the CRC table, the metrics, the segment size, the
# error variables
_WAL_NEW_ERRS = [('errBadWALName', 'BW'), ('ErrMetadataConflict', 'MC'), ('ErrFileNotFound', 'FN'),
                 ('ErrSnapshotMismatch', 'SM'), ('ErrSnapshotNotFound', 'SN'),
                 ('ErrSliceOutOfRange', 'SO'), ('ErrDecoderNotFound', 'DN'), ('ErrSaveBatchTooLarge', 'BL')]
_WAL_METRICS = ['walFsyncSec', 'walWriteSec', 'walWriteBytes']
_WAL_ERRS = ['errBadWALName', 'ErrMetadataConflict', 'ErrFileNotFound', 'ErrCRCMismatch',
             'ErrSnapshotMismatch', 'ErrSnapshotNotFound', 'ErrSliceOutOfRange', 'ErrDecoderNotFound',
             'ErrSaveBatchTooLarge']


def _walErrVar(x, tag):
    """The fact's clause of the error variable `x`, from `errors.New`'s `E<tag>`."""
    return [f'ihave #V{x} : (EtcdGrove.wal.errVar {x} : IProp GF) $$ []',
            '· unfold EtcdGrove.wal.errVar', '  iexists _', f'  iframe H{x}', '  isplitl []',
            '  · iapply EtcdGrove.errorString_errOk', f'    iexact E{tag}',
            f'  · iapply EtcdGrove.errIsTerm_errorString x{tag}; iexact {{Hd:errors}}']


# (metric-inits, 2026-11-19) a metric whose initializer is translated: `prometheus.New<Kind>` of an
# options literal (a histogram's buckets `ExponentialBuckets(start, 2, n)`), over prometheus's
# constructor specs; the steps before its store (`before`, keyed by the variable)
PROM_CTORS = [f'Proof.github_com.prometheus.client_golang.prometheus.{f}'
              for f in ['NewCounter', 'NewGauge', 'NewHistogram', 'ExponentialBuckets',
                        # (prove-ps2-metrics, 2026-11-22) `NewGauge` returns `isGauge`; the methods'
                        # triples come from their proofs, through these laws
                        'MetricLaws', 'gauge__Set', 'gauge__Add', 'gauge__Inc', 'gauge__Dec']]

_PM = 'EtcdGrove.prometheus'
def gauge_rep(c, h):
    """After `NewGauge` (`#R<h> : isGauge <c>`): `#C<h> : metric.gaugeSpec <c>` and
    `#D<h> : metric.gaugeSetSpec <c>`, from the methods' proofs (prove-ps2-metrics, 2026-11-22)."""
    a = f'{_PM}.gauge.Add.wp_proof'
    return [f'ihave #C{h} : ({_PM}.metric.gaugeSpec {c} : IProp GF) $$ []',
            f'· iapply {_PM}.metric.gaugeSpec_of_isGauge ({_PM}.gauge.Inc.wp_proof {a}) ({_PM}.gauge.Dec.wp_proof {a}) {a}',
            # (prom-registry) prometheus's fact at the run's registry name: `isPkgInitSome`
            '  all_goals first | iassumption | iPkgInit',
            f'ihave #D{h} : ({_PM}.metric.gaugeSetSpec {c} : IProp GF) $$ []',
            f'· iapply {_PM}.metric.gaugeSetSpec_of_isGauge {_PM}.gauge.Set.wp_proof',
            '  all_goals first | iassumption | iPkgInit']

def metric_steps(x, kind):
    P = 'EtcdGrove.prometheus'
    if kind == 'counter':
        return [f'wp_apply {P}.NewCounter.wp_proof _ _ _ _ _ rfl (by decide) as %c{x} ⟨#C{x}, -⟩',
                'try wp_auto']
    if kind == 'gauge':
        return ([f'wp_apply {P}.NewGauge.wp_proof _ _ _ _ _ rfl (by decide) as %c{x} ⟨#R{x}, -⟩'] +
                gauge_rep(f'c{x}', x) + ['try wp_auto'])
    assert kind == 'hist'
    return [f'wp_apply {P}.ExponentialBuckets.wp_proof _ _ _ (by rfl) (by decide) as %b{x} B{x}',
            'try wp_auto',
            f'wp_apply {P}.NewHistogram.wp_proof _ _ _ _ _ _ _ _ (by rfl) ({P}.expBuckets_ok (by decide))'
            f' (by decide) $$ B{x} as %c{x} ⟨#C{x}, -⟩',
            'try wp_auto']

# (prove-initmisc, 2026-11-20) the `NewGaugeFunc` gauges (mvcc's, auth's)
def gaugefunc_steps(x):
    """`x = prometheus.NewGaugeFunc(opts, func() float64 {...})`, over `NewGaugeFunc`'s spec."""
    return ['try wp_auto',
            f'wp_apply EtcdGrove.prometheus.NewGaugeFunc.wp_proof _ _ _ _ _ _ rfl as %c{x} #N{x}',
            'try wp_auto']

_MV = 'go_etcd_io.etcd.server.v3.storage.mvcc'

def metric_conv(x, kind, tgt):
    """After `metric_steps`: `#E<x> : <tgt> c<x>`, a package's own (weaker or equal) predicate, from
    the constructor's mvcc predicates (`#C<x>`; a gauge's `gaugeSetSpec` `#D<x>`)."""
    if kind == 'counter':
        get = [f'  icases C{x} with ⟨#K, -, -⟩'], 'K', 'counterSpec', 'C'
    elif kind == 'hist':
        get = [], f'C{x}', 'histSpec', 'C'
    elif tgt.endswith('gaugeAddSpec'):
        get = [f'  icases C{x} with ⟨-, -, #K⟩'], 'K', 'gaugeSpec', 'C'
    else:
        get = [], f'D{x}', 'gaugeSetSpec', 'D'
    pre, h, src, hn = get
    return ([f'ihave #E{x} : ({tgt} c{x} : IProp GF) $$ []',
             f'· iunfold EtcdGrove.prometheus.metric.{src} at {hn}{x}'] + pre +
            [f'  unfold {tgt}', f'  iexact {h}'])

def metric_steps_to(x, kind, tgt):
    return metric_steps(x, kind) + metric_conv(x, kind, tgt)

def _walMetric(x, spec):
    return dict(doc=f'/-- `{x} = prometheus.New...(...)` (`metrics.go`): a metric whose method returns. -/',
                post=f'∃ h : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok h ∗ EtcdGrove.wal.{spec} h',
                pat='⟨%h@, H@, #S@⟩')


LFS_SPECIAL['go_etcd_io.etcd.server.v3.storage.wal'] = dict(
    doc='''Its fact (`walInit`, `PkgInit.lean`): `crcTable` holds the Castagnoli table (`walCrcTable`), the
metrics `walFsyncSec`, `walWriteSec` (histograms) and `walWriteBytes` (a gauge) hold metrics whose
`Observe`/`Add` return (`wal.metricsInit`), `SegmentSizeBytes` holds `64000000`, `MaxSaveBatchBytes`
`2^42` (fix 0009), every error
variable an error whose `Error()` returns and on which `errors.Is` returns (`wal.errVar`), and `openWALFilesFn` the function
`openWALFiles`, read-only for good. Its initializer
allocates its variables, initializes its imports and runs their initializers: the metrics'
translated `prometheus` constructors (metrics.go, over prometheus's `NewHistogram`, `ExponentialBuckets`
and `NewGauge` specs; until 2026-11-19 the trust-boundary axioms `<X>_init`), the
translated `errors.New` calls, `ErrCRCMismatch = walpb.ErrCRCMismatch` (`walpbInit`), `crcTable =
crc32.MakeTable(crc32.Castagnoli)` (`hash.crc32.MakeTable.wp_proof`), and its untranslated `init`
function (`prometheus.MustRegister` of the metrics), which the trust-boundary axiom `initFuncsOk`
says returns.''',
    imports=['Perennial.Proof.errors.NewVar', 'Proof.hash.crc32.MakeTable', 'Proof.errors.ErrIsTerm', 'Proof.errors.ErrorStringOk'] + PROM_CTORS,
    alloc_types=dict({x: 'GoInterface' for x in _WAL_ERRS + _WAL_METRICS}, crcTable='Loc', openWALFilesFn='GoFunc',
                     SegmentSizeBytes='w64', MaxSaveBatchBytes='w64'),
    before=dict({x: metric_steps_to(x, k, f'EtcdGrove.wal.{t}') for x, k, t in
                 [('walFsyncSec', 'hist', 'histSpec'), ('walWriteSec', 'hist', 'histSpec'),
                  ('walWriteBytes', 'gauge', 'gaugeAddSpec')]},
                **{x: ['try wp_auto', f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{t} ⟨#_, #E{t}⟩',
                     'try wp_auto'] for x, t in _WAL_NEW_ERRS},
                ErrCRCMismatch=['try wp_auto',
                    'ihave #Hpb : (EtcdGrove.walpb.walpbInit : IProp GF) $$ []',
                    '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.server.v3.storage.wal.walpb}',
                    'icases Hpb with ⟨%eC, #HpbC, #HpbOk, #HpbT, -⟩', 'try wp_auto'],
                crcTable=['try wp_auto',
                          'rw [show (W32 2197175160) = _root_.Perennial.hash.crc32.castagnoliPoly from rfl]',
                          'wp_apply _root_.Perennial.EtcdGrove.hash.crc32.MakeTable.wp_proof as %tab #Htab',
                          'try wp_auto']),
    finish=[f'ipersist H{x}' for x in _WAL_ERRS + ['crcTable', 'SegmentSizeBytes', 'MaxSaveBatchBytes', 'walFsyncSec',
                                                    'walWriteSec', 'walWriteBytes', 'openWALFilesFn']] +
           [l for x, t in _WAL_NEW_ERRS for l in _walErrVar(x, t)] +
           ['ihave #VErrCRCMismatch : (EtcdGrove.wal.errVar ErrCRCMismatch : IProp GF) $$ []',
            '· unfold EtcdGrove.wal.errVar', '  iexists _', '  iframe HErrCRCMismatch HpbOk HpbT'] +
           FIN_PRE[:6] +
           ['imodintro', 'unfold EtcdGrove.wal.walInit EtcdGrove.WalFs.walCrcTable EtcdGrove.wal.metricsInit',
            'iframe #'],
)
# (prove-etcdint3, 2026-11-21) `hash/crc32`'s initializer translated (until then the trust-boundary
# axiom `opaqueInitsOk` of its three variables): `IEEETable = simpleMakeTable(IEEE)`, over its proved
# spec, and the two `sync.OnceFunc`s (closures not run at initialization)
# (crc32-hooks2, 2026-11-22, etcd-grove#14) `castagnoliInitOnce`'s triple and `haveCastagnoli`'s
# invariant (`PkgInit.lean`): the once's function sets up the Castagnoli state, the fast path or
# the slicing-by-8 one
_CRC32_ONCE = [
    'ipersist HcastagnoliInitOnce',
    'ihave Hhc : _root_.Perennial.sync.atomic.ownBool (GF := GF) (globalAddr haveCastagnoli) (DFrac.own 1) false $$ [HhaveCastagnoli]',
    '· rw [_root_.Perennial.sync.atomic.ownBool_unseal]',
    '  unfold _root_.Perennial.sync.atomic.ownBoolDef',
    "  have e : (zero_val _root_.Perennial.sync.atomic.Bool') =",
    "      ({ «_#0'» := zero_val _, v' := _root_.Perennial.sync.atomic.b32w false } :",
    "        _root_.Perennial.sync.atomic.Bool') := rfl",
    '  rw [← e]; iexact HhaveCastagnoli',
    'imod inv_alloc hash.crc32.crc32N ⊤ hash.crc32.haveInv $$ [Hhc] with #Hinv',
    '· inext; iunfold hash.crc32.haveInv; iexists false; iframe',
    '  simp only [Bool.false_eq_true, ↓reduceIte]; itrivial',
    'imod HcastagnoliOnce $$ %iprop(globalAddr castagnoliTable ↦ zero_val Loc ∗',
    '    globalAddr castagnoliTable8 ↦ zero_val Loc ∗ globalAddr updateCastagnoli ↦ zero_val GoFunc)',
    '    %hash.crc32.castagnoliReady %⊤ [] [HcastagnoliTable HcastagnoliTable8 HupdateCastagnoli] [] with #HcastOnce',
    '· iintro !> #HQ; imodintro; iexact HQ',
    '· iframe',
    '· iintro !> %Φ ⟨HT, HT8, HU⟩ HΦ',
    '  wp_auto',
    '  rw [show (W32 2197175160) = _root_.Perennial.hash.crc32.castagnoliPoly from rfl]',
    '  wp_apply (_root_.Perennial.EtcdGrove.hash.crc32.simpleMakeTable.wp_proof',
    '    _root_.Perennial.EtcdGrove.hash.crc32.simplePopulateTable.wp_proof) as %t Ht',
    '  try wp_auto',
    '  ipersist HT',
    '  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Ht with #Ht',
    '  wp_apply _root_.Perennial.EtcdGrove.hash.crc32.archAvailableCastagnoli.wp_proof as %avail -',
    '  cases avail',
    '  · -- no fast path: the slicing-by-8 table and its closure',
    '    try simp only [Bool.false_eq_true, ↓reduceIte]',
    '    try wp_auto',
    '    rw [show (W32 2197175160) = _root_.Perennial.hash.crc32.castagnoliPoly from rfl]',
    '    wp_apply (_root_.Perennial.EtcdGrove.hash.crc32.slicingMakeTable.wp_proof',
    '      _root_.Perennial.EtcdGrove.hash.crc32.simplePopulateTable.wp_proof) as %t8 Ht8',
    '    try wp_auto',
    '    ipersist HT8',
    '    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Ht8 with #Ht8',
    '    try wp_auto',
    '    ipersist HU',
    '    wp_apply_core _root_.Perennial.sync.atomic.Bool.wp_Store $$ [] [-]',
    '    · iexact Hd4',
    '    iinv Hinv with Hi Hclose',
    '    iapply fupd_mask_intro Std.LawfulSet.empty_subset',
    '    iintro Hmask',
    '    inext',
    '    iunfold hash.crc32.haveInv at Hi',
    '    icases Hi with ⟨%v, Hb, -⟩',
    '    iexists v',
    '    iframe Hb',
    '    iintro Hb',
    '    imod Hmask with _',
    '    imod Hclose $$ [Hb] with _',
    '    · inext; iunfold hash.crc32.haveInv; iexists true; iframe Hb; simp only [↓reduceIte]',
    '      isplitl []',
    '      · iunfold hash.crc32.castagnoliReady; iexists t; iframe HT; unfold castagnoliTableArr; iexact Ht',
    '      iexists _; iframe HU',
    '      iunfold hash.crc32.updSpec',
    '      iintro %c %s %bs %dq !> %Ψ Hs HΨ',
    '      wp_auto',
    '      wp_apply (_root_.Perennial.EtcdGrove.hash.crc32.slicingUpdate.wp_proof',
    '        _root_.Perennial.EtcdGrove.hash.crc32.simpleUpdate.wp_proof',
    '        _root_.Perennial.EtcdGrove.byteorder.LEUint32.wp_proof) $$ [Hs] as Hs',
    '      · iframe Hs; iexact Ht8',
    '      try wp_auto',
    '      rw [show _root_.Perennial.hash.crc32.crcUpdate (_root_.Perennial.hash.crc32.crcTableOf',
    '        _root_.Perennial.hash.crc32.castagnoliPoly) c bs = _root_.Perennial.hash.crc32.crc32c c bs from rfl]',
    '      iapply HΨ $$ Hs',
    '    imodintro',
    '    try wp_auto',
    '    iapply HΦ',
    '    iunfold hash.crc32.castagnoliReady; iexists t; iframe HT; unfold castagnoliTableArr; iexact Ht',
    '  · -- the fast path: `archInitCastagnoli()`, `updateCastagnoli = archUpdateCastagnoli`',
    '    try simp only [↓reduceIte]',
    '    try wp_auto',
    '    wp_apply _root_.Perennial.EtcdGrove.hash.crc32.archInitCastagnoli.wp_proof',
    '    try wp_auto',
    '    ipersist HU',
    '    ihave #Hus : (hash.crc32.updSpec (GF := GF) (functions archUpdateCastagnoli [])) $$ []',
    '    · iunfold hash.crc32.updSpec',
    '      iintro %c %s %bs %dq !> %Ψ Hs HΨ',
    '      wp_apply (_root_.Perennial.EtcdGrove.hash.crc32.archUpdateCastagnoli.wp_proof',
    '        (_root_.Perennial.EtcdGrove.hash.crc32.simpleMakeTable.wp_proof',
    '          _root_.Perennial.EtcdGrove.hash.crc32.simplePopulateTable.wp_proof)',
    '        _root_.Perennial.EtcdGrove.hash.crc32.simpleUpdate.wp_proof) $$ [Hs] as Hs',
    '      · iexact Hs',
    '      iapply HΨ $$ Hs',
    '    wp_apply_core _root_.Perennial.sync.atomic.Bool.wp_Store $$ [] [-]',
    '    · iexact Hd4',
    '    iinv Hinv with Hi Hclose',
    '    iapply fupd_mask_intro Std.LawfulSet.empty_subset',
    '    iintro Hmask',
    '    inext',
    '    iunfold hash.crc32.haveInv at Hi',
    '    icases Hi with ⟨%v, Hb, -⟩',
    '    iexists v',
    '    iframe Hb',
    '    iintro Hb',
    '    imod Hmask with _',
    '    imod Hclose $$ [Hb] with _',
    '    · inext; iunfold hash.crc32.haveInv; iexists true; iframe Hb; simp only [↓reduceIte]',
    '      isplitl []',
    '      · iunfold hash.crc32.castagnoliReady; iexists t; iframe HT; unfold castagnoliTableArr; iexact Ht',
    '      iexists _; iframe #',
    '    imodintro',
    '    try wp_auto',
    '    iapply HΦ',
    '    iunfold hash.crc32.castagnoliReady; iexists t; iframe HT; unfold castagnoliTableArr; iexact Ht',
]
_CRC32_FIN = [
    'unfold hash.crc32.crc32Init',
    'isplitl []',
    '· unfold hash.crc32.ieeeTableArr',
    '  iexists _',
    '  iframe HIEEETable',
    '  iexact HtI',
    'iframe Hinv',
    'iexists _',
    'iframe HcastagnoliInitOnce',
    'iexact HcastOnce',
]
SPECIAL['hash.crc32'] = dict(
    doc='''Its fact (`crc32Init`, `PkgInit.lean`): `IEEETable` holds, read-only, a pointer to the IEEE
table, read-only; `castagnoliInitOnce` a function every call of which returns with the Castagnoli
table set up (`castagnoliReady`); and `haveInv`, the invariant of `haveCastagnoli` (once true, the
table is set up and `updateCastagnoli` holds a function computing CRC-32C). Its initializer allocates
its variables, initializes its imports and runs their translated initializers: `simpleMakeTable(IEEE)`
(`crc32.go:101`, over its spec) and the two `sync.OnceFunc(func() {...})` (`castagnoliInitOnce`,
`ieeeInitOnce`: Perennial's `sync.wp_OnceFunc`; their functions run only when called). The proof
allocates `haveInv` and gives `castagnoliInitOnce`'s function its triple: it sets `castagnoliTable`
(`simpleMakeTable`), then either the fast path (`archInitCastagnoli`, `archUpdateCastagnoli`: the
trusted hooks) or the slicing-by-8 table and its closure (`slicingMakeTable`, `slicingUpdate`), and
stores `true` in `haveCastagnoli`. (prove-etcdint3, 2026-11-21: until then untranslated, the
trust-boundary axiom `opaqueInitsOk`, and its fact `True`; crc32-hooks2, 2026-11-22, etcd-grove#14:
the Castagnoli state and once.)''',
    imports=['Proof.hash.crc32.simpleMakeTable', 'Proof.hash.crc32.simplePopulateTable',
             'Proof.hash.crc32.simpleUpdate', 'Proof.hash.crc32.slicingMakeTable',
             'Proof.hash.crc32.slicingUpdate', 'Proof.hash.crc32.archAvailableCastagnoli',
             'Proof.hash.crc32.archInitCastagnoli', 'Proof.hash.crc32.archUpdateCastagnoli',
             'Proof.internal.byteorder.LEUint32'],
    alloc_types=dict(IEEETable='Loc', castagnoliInitOnce='GoFunc', ieeeInitOnce='GoFunc',
                     castagnoliTable='Loc', castagnoliTable8='Loc', updateCastagnoli='GoFunc',
                     haveCastagnoli="_root_.Perennial.sync.atomic.Bool'", ieeeTable8='Loc', updateIEEE='GoFunc'),
    before=dict(
        IEEETable=['try wp_auto',
                   'rw [show (W32 3988292384) = _root_.Perennial.hash.crc32.ieeePoly from rfl]',
                   'wp_apply (_root_.Perennial.EtcdGrove.hash.crc32.simpleMakeTable.wp_proof _root_.Perennial.EtcdGrove.hash.crc32.simplePopulateTable.wp_proof) as %tI HtI',
                   'try wp_auto'],
        castagnoliInitOnce=['try wp_auto', 'wp_apply _root_.Perennial.sync.wp_OnceFunc as %castagnoliOnce HcastagnoliOnce', 'try wp_auto'],
        ieeeInitOnce=['try wp_auto', 'wp_apply _root_.Perennial.sync.wp_OnceFunc as %_ -', 'try wp_auto'],
        **{'$end': ['try wp_auto']}),
    finish=['ipersist HIEEETable',
            'imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HtI with #HtI'] +
           _CRC32_ONCE + FIN_PRE[:6] + ['imodintro'] + _CRC32_FIN,
)
# (WAL package init, 2026-11-13) the part's raft root package (names-only): `emptyState`, a
# translated `&pb.HardState{}`; (W4c U4, 2026-11-14) in its fact (`rootInit`, `PkgInit.lean`), as the
# main tree's (`Proof/go_etcd_io/raft/v3/Init.lean`'s steps): its cells (all `nil`) frozen, its hidden
# fields in the `protobuf` invariant
# (W4c U2, 2026-11-14) the part's `examples/lib/durable`: `mu`, a mutex guarding nothing
LFS_SPECIAL['github_com.mit_pdos.etcd_grove.examples.lib.durable'] = dict(
    doc='''Its fact (`durable.durableInit`, `PkgInit.lean`): `mu` is a mutex guarding nothing (the calls are
serialized in the proofs by the file's handle). Its initializer allocates `mu` and initializes its
imports.''',
    alloc_types={'mu': '_root_.Perennial.sync.Mutex'},
    finish=['imod sync.init_Mutex iprop(True) ⊤ (globalAddr mu) $$ Hmu [] with #HM', '· inext; itrivial'] +
           FIN_PRE[:6],
)
LFS_SPECIAL['io.fs'] = LFS_IOFS
LFS_SPECIAL['os'] = LFS_OS
# (2026-11-15, the WAL in the main tree: notes/wal-lean-integration.md) the part `LinuxFs/`'s
# configurations are the main tree's (its raft root, names-only, went: the WAL imports the main raft);
# `examples/lib/durable` with bodies is the part `WalTester/`'s (`WT_SPECIAL`, `wt_inits`)
WT_SPECIAL = {'github_com.mit_pdos.etcd_grove.examples.lib.durable':
              LFS_SPECIAL.pop('github_com.mit_pdos.etcd_grove.examples.lib.durable')}
SPECIAL.update(LFS_SPECIAL)

SPECIAL['internal.poll'] = dict(
    doc='''Its fact (`PkgInit.lean`): `ErrNoDeadline`, which `os`'s initializer copies, holds some
error for good, `ErrDeadlineExceeded` (copied too) an `*DeadlineExceededError`, and
`ErrFileClosing`, which `(*os.File).wrapErr` compares with, an `*errorString` (`errors.New`). Its initializer runs its variables' translated
initializers (`sync.OnceValue(...)`, `errors.New` errors, function values, a `sync.Pool`
literal).''',
    imports=['Perennial.Proof.sync.Link', 'Perennial.Proof.errors.NewVar'],
    alloc_types=_ALLOC_ANY,
    before={'$end': [
        'set_option maxRecDepth 20000 in',
        'wp_apply _root_.Perennial.sync.wp_OnceValue as %cfr -',
        'wp_apply _root_.Perennial.errors.wp_New_errorString as %xFC ⟨#_, #EFC⟩',
        'wp_apply _root_.Perennial.errors.wp_New_errorString as %xND ⟨#_, #END⟩',
        'ipersist HErrFileClosing',
        'ipersist HErrNoDeadline',
        'wp_alloc_anon',
        'wp_auto',
        'ipersist HErrDeadlineExceeded',
        'wp_apply _root_.Perennial.errors.wp_New_errorString as %xNP ⟨#_, #ENP⟩']},
    finish=['iframe Hown', 'is_pkg_init_finish'],
)

# (v3, 2026-11-14) the part `Net/`'s `net` (project net, the net extension's): `errTimeout`
# and `ErrClosed` translated, `errClosed` a trusted model that allocates its variable
# (`Net/TrustedCode/net.lean`); the rest trusted initializers that do nothing.
NET_SPECIAL = {}
NET_SPECIAL['net'] = dict(
    doc='''Its fact (`Base.lean`'s `isInit`): `ErrClosed` and `errClosed` hold `poll.ErrNetClosing`,
`errTimeout` a `*timeoutError`. Its initializer initializes its imports, allocates `errTimeout` and
`ErrClosed` and runs their translated initializers (`&timeoutError{}`, `errClosed`), runs the
trusted model of `errClosed`'s (which allocates it and stores `poll.ErrNetClosing`'s value) and the
trusted initializers of its other variables (models in `TrustedCode/` that do nothing).''',
    alloc_types=_ALLOC_ANY,
    before={'errTimeout': ['(try wp_auto)', 'wp_alloc_anon', 'wp_auto']},
    trusted={'errClosed': ['wp_call',
                           'rw [show (go!"net.errClosed" : GoString) = errClosed by rfl]',
                           'wp_apply wp_GlobalAlloc (V := _) errClosed _ as HerrClosed',
                           '(try wp_auto)'],
             },
    finish=['ipersist HerrTimeout', 'ipersist HerrClosed', 'ipersist HErrClosed', 'iframe Hown',
            'imodintro', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
            'is_pkg_init_finish', 'unfold isInit closedErr', 'imodintro',
            'iframe HErrClosed HerrClosed', 'iexists _', 'iexact HerrTimeout'],
)

# (net-swap, 2026-11-22) the main tree's `net` is `Net/`'s: the same initializer proof
SPECIAL['net'] = NET_SPECIAL['net']

# (2026-10-24, the auth plan's A3c: the Lock and Election servers bring the client's concurrency
# package into the closure) its five error variables, translated `errors.New` calls
_CC = [('ErrElectionNotLeader', 'N'), ('ErrElectionNoLeader', 'O'), ('ErrLocked', 'L'),
       ('ErrSessionExpired', 'S'), ('ErrLockReleased', 'R')]
_CCF = ['ErrLocked', 'ErrSessionExpired', 'ErrLockReleased', 'ErrElectionNotLeader',
        'ErrElectionNoLeader']

SPECIAL['go_etcd_io.etcd.client.v3.concurrency'] = dict(
    doc='''Its fact (`concurrencyInit`, `Base.lean`): `Mutex`'s three errors and `Election`'s two each
hold a fixed non-nil error. Its initializer allocates them, initializes its imports and runs their
translated initializers (`errors.New` calls, `mutex.go`, `election.go`; Perennial's
`context.wp_New_errorString`).''',
    imports=['Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar'],
    alloc_types={x: 'GoInterface' for x, _ in _CC},
    before={'$end': ['try wp_auto'] + [l for _, t in _CC for l in [
        f'wp_apply _root_.Perennial.context.wp_New_errorString as %x{t} ⟨-, #M{t}⟩', 'try wp_auto']]},
    finish=[f'ipersist H{x}' for x, _ in _CC] + FIN_PRE[:6] + ['imodintro', 'unfold concurrencyInit'] +
           [l for x in _CCF[:-1] for l in ['isplitr', f'· iexists _; iexact H{x}']] +
           [f'iexists _; iexact H{_CCF[-1]}'],
)

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3election'] = dict(
    doc='''Its fact (`v3electionInit`, `etcdserver/api/v3election/Base.lean`; the auth plan's A3c,
2026-10-24): `ErrMissingLeaderKey` holds a fixed non-nil error. Its initializer allocates it,
initializes its imports and runs its translated initializer (an `errors.New` call, `election.go`;
Perennial's `context.wp_New_errorString`).''',
    imports=['Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar'],
    alloc_types={'ErrMissingLeaderKey': 'GoInterface'},
    before={'$end': ['try wp_auto',
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xM ⟨-, #MM⟩', 'try wp_auto']},
    finish=['ipersist HErrMissingLeaderKey'] + FIN_PRE[:6] +
           ['imodintro', 'unfold v3electionInit', 'iexists _; iexact HErrMissingLeaderKey'],
)

# (2026-10-24, the auth plan's S4e) the permission type's name maps, translated: the store's
# `RoleGrantPermission` looks the granted type's name up for its log line
SPECIAL['go_etcd_io.etcd.api.v3.authpb'] = dict(
    doc='''Its fact (`authpbInit`, `cache/v3/Base.lean`): `Permission_Type_name` holds a map, read-only
for good, whose entries are the permission types' names (`0` `READ`, `1` `WRITE`, `2`
`READWRITE`). Its initializer allocates and sets the two translated name maps
(`Permission_Type_name`, `Permission_Type_value`: `map[int32]string`/`map[string]int32` literals,
`auth.pb.go`), initializes its imports and runs its other variables' untranslated initializers (the
generated protobuf descriptors), which the trust-boundary axiom `opaqueInitsOk` says run.''',
    alloc_types={'Permission_Type_name': 'Loc', 'Permission_Type_value': 'Loc'},
    before={
        'Permission_Type_name': [
            'try wp_auto',
            'wp_apply (wp_map_make1 (K := w32) (V := GoString) go.int32 go.string) as %mn Hmn',
            'try wp_auto',
            'repeat (wp_apply (wp_mapInsert (K := w32) (V := GoString) go.int32) $$ Hmn as Hmn; try wp_auto)'],
        'Permission_Type_value': [
            'try wp_auto',
            'wp_apply (wp_map_make1 (K := GoString) (V := w32) go.string go.int32) as %mv Hmv',
            'try wp_auto',
            'repeat (wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hmv as Hmv; try wp_auto)']},
    finish=['ipersist HPermission_Type_name', 'ipersist Hmn'] + [
        'iframe Hown', 'imodintro', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
        'is_pkg_init_finish', 'try (isplitl []; · (imodintro; itrivial))', 'imodintro',
        'unfold go_etcd_io.etcd.cache.v3.authpbInit',
        'iexists _, _', 'iframe #', 'ipureintro', 'simp (config := {decide := true})'],
)

# (etcd-small-3, 2026-11-23, etcd-grove#39) `mvccpb`: `Event_EventType_name`, which
# `Event_EventType.String`'s trusted model reads (until then skipped; the fact `True`)
SPECIAL['go_etcd_io.etcd.api.v3.mvccpb'] = dict(
    doc='''Its fact (`mvccpbInit`, `cache/v3/Base.lean`; etcd-grove#39, 2026-11-23, `True` until then):
`Event_EventType_name` holds a map with `mvccpb.eventTypeNames` (`0` `PUT`, `1` `DELETE`), both
read-only for good: `Event_EventType.String`'s trusted model reads it. Its initializer allocates and
sets the translated name map (a `map[int32]string` literal, `kv.pb.go`), initializes its imports and
runs its trusted `init` (a no-op model).''',
    alloc_types={'Event_EventType_name': 'Loc'},
    before={
        'Event_EventType_name': [
            'try wp_auto',
            'wp_apply (wp_map_make1 (K := w32) (V := GoString) go.int32 go.string) as %mn Hmn',
            'try wp_auto',
            'repeat (wp_apply (wp_mapInsert (K := w32) (V := GoString) go.int32) $$ Hmn as Hmn; try wp_auto)']},
    finish=['ipersist HEvent_EventType_name', 'ipersist Hmn'] + [
        'iframe Hown', 'imodintro', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
        'is_pkg_init_finish', 'try (isplitl []; · (imodintro; itrivial))', 'imodintro',
        'unfold go_etcd_io.etcd.cache.v3.mvccpbInit go_etcd_io.etcd.cache.v3.mvccpb.eventTypeNames',
        'iexists _', 'iframe #'],
)

# (prove-grpc3, 2026-11-21) grpc's `resolver`, in the closure since `internal/resolver`'s `New` is
# translated (it imports `resolver/manual`): its two package variables, translated.
SPECIAL['google_golang_org.grpc.resolver'] = dict(
    doc='''Its fact is `True`. Its initializer allocates its two variables and runs their translated
initializers (`m = make(map[string]Builder)`, `defaultScheme = "passthrough"`, `resolver.go:38-43`),
after initializing its imports (`serviceconfig`, `attributes`: types only).''',
    alloc_types={'m': 'Loc', 'defaultScheme': 'GoString'},
    before={
        'm': ['try wp_auto',
              'wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string '
              'google_golang_org.grpc.resolver.Builder.ty) as %mb Hmb',
              'try wp_auto'],
        'defaultScheme': ['try wp_auto']},
)

_VERS = ['V3_0', 'V3_1', 'V3_2', 'V3_3', 'V3_4', 'V3_5', 'V3_6', 'V3_7', 'V3_8', 'V3_9', 'V4_0']
_SEMVER_NEW = ('EtcdGrove.semver.New.wp_proof (EtcdGrove.semver.Version.String.wp_proof '
               '_root_.Perennial.bytes.Buffer.wp_Write _root_.Perennial.bytes.Buffer.wp_String '
               '_root_.Perennial.fmt.wp_Fprintf)')
def semver_new_steps(x):
    """`x = *semver.New(...)`: `semver.New`'s spec (a read-only version), then the load."""
    return ['try wp_auto',
            f'wp_apply ({_SEMVER_NEW}) as %p{x} ⟨%N{x}, %o{x}, #P{x}⟩',
            'try wp_auto']
SPECIAL['go_etcd_io.etcd.api.v3.version'] = dict(
    doc='''Its fact (`api/v3/version/PkgInit.lean`): `Version` holds `"3.8.0-alpha.0"`, `V3_6`, `V3_7` and `V3_8`
fixed values and `MinClusterVersion` `"3.0.0"`. Its initializer allocates and sets its translated string
variables (`version.go`: `MinClusterVersion`, `Version`, `APIVersion`, `GitSHA`; translated since
2026-11-19, until then the trust-boundary axioms `Version_init` and `MinClusterVersion_init`), its `semver`
versions (`V3_0 = *semver.New(3, 0, 0, "", "")`, ...: `semver.New`'s spec, proved over the real code) and
`AllVersions` (a slice literal of them; prove-initleft, 2026-11-21: until then the trust-boundary axioms
`V3_6_init` and `opaqueInitsOk`), and runs its translated `init` function (prove-ps2-initfuncs,
2026-11-22; until then the trust-boundary axiom `initFuncsOk`): `APIVersion` set to
`fmt.Sprintf("%d.%d", ver.Major(), ver.Minor())` of `semver.NewVersion(Version)` when that parses
(`NewVersion`'s spec, the trust boundary; `Major`/`Minor` proved), left as it was otherwise.''',
    alloc_types=dict({x: 'GoString' for x in ['MinClusterVersion', 'Version', 'APIVersion', 'GitSHA']},
                     **{x: 'github_com.Masterminds.semver.v3.Version' for x in _VERS}, AllVersions='GoSlice'),
    before=dict({x: semver_new_steps(x) for x in _VERS},
                AllVersions=['try wp_auto',
                             'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sav ⟨Sav, -⟩',
                             'try wp_auto']),
    imports=['Proof.github_com.Masterminds.semver.v3.New',
             'Proof.github_com.Masterminds.semver.v3.Version__String',
             'Perennial.Proof.bytes.Link',
             'Proof.github_com.Masterminds.semver.v3.NewVersion',
             'Proof.github_com.Masterminds.semver.v3.Version__Major',
             'Proof.github_com.Masterminds.semver.v3.Version__Minor',
             'Proof.fmt.SprintfPure'],
    # (prove-ps2-initfuncs, 2026-11-22) `init()` (`version.go`): `APIVersion` from `NewVersion(Version)`
    after={'init.«0»': [
        'wp_apply EtcdGrove.semver.NewVersion.wp_proof as %pv %err Hr',
        'try wp_auto',
        'wp_bind (If _ _ _)',
        'iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ s : GoString, globalAddr APIVersion ↦ s)))',
        'isplitl [Hr HAPIVersion ver]',
        '· icases Hr with (⟨%Hok, %x, #Hx, -⟩ | %Hbad)',
        '  · obtain ⟨-, -, Herr⟩ := Hok',
        '    subst Herr',
        '    wp_auto',
        '    wp_apply EtcdGrove.semver.Version.Major.wp_proof $$ [$Hx] as -',
        '    wp_apply EtcdGrove.semver.Version.Minor.wp_proof $$ [$Hx] as -',
        '    wp_apply (wp_slice_literal (l := [_, _]))',
        '    try (isplitr; (ipureintro; rfl))',
        '    iintro %sla ⟨Hargs, -⟩',
        '    try wp_auto',
        '    wp_apply (EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%d.%d"',
        '      [.dir none _root_.Perennial.fmt.verb_d, .lit go!".", .dir none _root_.Perennial.fmt.verb_d] _ _ _ _ (by fmt_encode) (by fmt_fits)',
        '      (.int _ _ _ _ (.uint64 _) (.int _ _ _ _ (.uint64 _) .nil))) $$ [$Hargs] as %str -',
        '    try wp_auto',
        '    isplitr',
        '    · ipureintro; rfl',
        '    iexists _; iexact HAPIVersion',
        '  · obtain ⟨-, Herr⟩ := Hbad',
        '    cases err with',
        '    | nil => exact absurd rfl Herr',
        '    | ok i =>',
        '      simp only',
        '      try wp_auto',
        '      isplitr',
        '      · ipureintro; rfl',
        '      iexists _; iexact HAPIVersion',
        'iintro %v ⟨%Hv, %s, HAPIVersion⟩',
        'subst Hv',
        'try wp_auto']},
    finish=['ipersist HVersion', 'ipersist HV3_6', 'ipersist HMinClusterVersion',
            'ipersist HV3_7', 'ipersist HV3_8'] + FIN_PRE[:6],
)

# (the lease-renew plan, 2026-11-01) names only: `LeaseRenew` reads `LeasePrefix`
SPECIAL['go_etcd_io.etcd.server.v3.lease.leasehttp'] = dict(
    doc='''Its fact (`lease/leasehttp/Base.lean`): `LeasePrefix` holds some string. Its initializer
sets the translated `LeasePrefix` (`"/leases"`) and `LeaseInternalPrefix` (`http.go`; until
2026-11-19 the trust-boundary axiom `LeasePrefix_init`), and (prove-errinits, 2026-11-19) its other
variables, `applyTimeout` (`time.Second`) and `ErrLeaseHTTPTimeout` (`errors.New`), translated (until
then `opaqueInitsOk`).''',
    alloc_types={'LeasePrefix': 'GoString', 'LeaseInternalPrefix': 'GoString', 'applyTimeout': 'w64'},
    finish=['ipersist HLeasePrefix'] + FIN_PRE[:6],
)
newvars_cfg(SPECIAL['go_etcd_io.etcd.server.v3.lease.leasehttp'], ['ErrLeaseHTTPTimeout'])

# (prove-errinits, 2026-11-19) packages whose fact is `True`, with their `errors.New` / `fmt.Errorf`
# variables translated (until then `opaqueInitsOk`)
SPECIAL['go_etcd_io.etcd.client.pkg.v3.transport'] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its one variable,
`ErrNotTCP`, and runs its translated initializer (`limit_listen.go`: an `errors.New` call; until
2026-11-19 untranslated, `opaqueInitsOk`).'''), ['ErrNotTCP'])
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.version'] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and
runs their translated initializers (`errors.go`: `errors.New` calls; until 2026-11-19 untranslated,
`opaqueInitsOk`).'''), ['ErrInvalidDowngradeTargetVersion', 'ErrDowngradeInProcess', 'ErrNoInflightDowngrade'])
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery'] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and
runs their translated initializers (`discovery.go`: `errors.New` calls, and the retry bounds
`nRetries = uint(math.MaxUint32)` and `maxExponentialRetries = uint(8)`; until 2026-11-19
untranslated, `opaqueInitsOk`).''',
    alloc_types={'nRetries': 'w64', 'maxExponentialRetries': 'w64'}),
    ['ErrInvalidURL', 'ErrBadSizeKey', 'ErrSizeNotFound', 'ErrFullCluster', 'ErrTooManyRetries'])

# The k8s etcd3 store's packages (stage 6g, 2026-10-23): their facts are in
# `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean`.
_K3 = 'k8s_io.apiserver.pkg.storage.etcd3'
SPECIAL[_K3 + '.metrics'] = dict(
    doc='''Its fact (`metricsInit`, `storage/etcd3/Base.lean`): `ErrTransactionConflict` holds an
`errors.New("transaction conflict")` error (`EtcdGrove.errorsNewVar`). Its initializer runs its
variables' initializers (`metrics.go`): the one the fact reads translated (an `errors.New` call,
`metrics.go:42` at the apiserver pin `9c4ec15b8038`; until 2026-11-19 the trust-boundary axiom
`errorsNewVarsInit`), the others untranslated (`opaqueInitsOk`).''',
    # (premise fixes 3, 2026-11-10, decided by etcd-grove-81) `errors.New`, as Go has it (it was a
    # custom axiom giving some error): `txnError`'s result is then one grpc's `status` accepts
    # (`statusErrOk`), which `metrics.RecordEtcdRequest` needs
    finish=['ipersist HErrTransactionConflict'] + FIN_PRE + [
            'unfold k8s_io.apiserver.pkg.storage.etcd3.metricsInit EtcdGrove.errorsNewVar',
            'iexists _', 'iframe HErrTransactionConflict', 'iexact MErrTransactionConflict'],
)
newvars_cfg(SPECIAL[_K3 + '.metrics'], ['ErrTransactionConflict'])

# KEP-6404 (2026-10-26): the watch cache's metrics; their facts are in
# `Proof/k8s_io/apiserver/pkg/storage/cacher/Base.lean`.
SPECIAL['k8s_io.apiserver.pkg.storage.cacher.metrics'] = dict(
    doc='''Its fact (`cacherMetricsInit`, `storage/cacher/Base.lean`): `WatchCacheReadWait` holds a
histogram vector of the labels `group` and `resource`. Its initializer runs its variables'
untranslated initializers (`metrics.go`); the trust-boundary axiom `WatchCacheReadWait_init` states
the one the fact reads (`compbasemetrics.NewHistogramVec(..., []string{"group", "resource"})`),
`opaqueInitsOk` the others.''',
    custom={'WatchCacheReadWait': dict(
        doc='/-- `WatchCacheReadWait = compbasemetrics.NewHistogramVec(..., []string{"group", "resource"})`\n(`metrics.go`): a `*HistogramVec` with those labels (`kmetrics.vecLabels`). -/',
        post='∃ v : Loc, globalAddr WatchCacheReadWait ↦ v ∗ ⌜EtcdGrove.kmetrics.vecLabels v [go!"group", go!"resource"]⌝',
        pat='⟨%v@, H@, %L@⟩')},
    finish=['ipersist HWatchCacheReadWait'] + FIN_PRE[:7] + [
            'imodintro', 'iexists _', 'iframe HWatchCacheReadWait', 'ipureintro',
            'exact LWatchCacheReadWait'],
)

SPECIAL['k8s_io.apiserver.pkg.util.feature'] = dict(
    doc='''Its fact (`featureInit`, `storage/etcd3/Base.lean`): `DefaultMutableFeatureGate` and
`DefaultFeatureGate` hold the same feature gate. Its initializer allocates `DefaultFeatureGate`,
initializes its import (`component-base/featuregate`, names-only), runs `DefaultMutableFeatureGate`'s
untranslated initializer (`feature_gate.go`), which the trust-boundary axiom
`DefaultMutableFeatureGate_init` (`featuregate.NewFeatureGate()`: a gate) states, and
`DefaultFeatureGate`'s translated one (`DefaultFeatureGate = DefaultMutableFeatureGate`, a conversion
between interface types, which keeps the gate). (Sweep repairs 1, B5, 2026-11-08: until then
`DefaultFeatureGate_init` gave a gate whose `Enabled` answered any `bool` for any feature, false of an
unregistered one, and `DefaultMutableFeatureGate` was `opaqueInitsOk`'s, unlinked; the gate's specs
are now `features`' registration's, `features.init_0_ok`. Until 2026-11-23, #36, `DefaultFeatureGate`'s
initializer was untranslated, the trust-boundary axiom `DefaultFeatureGate_init`.)''',
    alloc_types={'DefaultFeatureGate': 'GoInterface'},
    custom={
        'DefaultMutableFeatureGate': dict(
            doc='/-- `DefaultMutableFeatureGate = featuregate.NewFeatureGate()` (`feature_gate.go`): a feature gate, no Kubernetes feature registered yet (`features`\' `init` registers them, `features.init_0_ok`). -/',
            post='∃ g : GoInterfaceOk, globalAddr DefaultMutableFeatureGate ↦ GoInterface.ok g',
            pat='⟨%g@, H@⟩')},
    before={'DefaultFeatureGate': ['try wp_auto']},
    finish=['ipersist HDefaultMutableFeatureGate', 'ipersist HDefaultFeatureGate'] + FIN_PRE[:6] + [
            'imodintro', 'iexists _', 'iframe #'],
)

# (k8s 7e Freeze review, etcd-grove-81, 2026-11-10) pflag's opaque initializers: what they assumed
# (`CommandLine = NewFlagSet(os.Args[0], ExitOnError)` indexes `os.Args`) is now the reason of their
# goose `[[skip]]` entry (`Code/github_com/spf13/pflag.toml`; #23, 2026-11-22), not `opaqueInitsOk`'s.

# (k8s 7e-1, 2026-11-10, decided by etcd-grove-81) grpc's fact: `EnableTracing` holds `false`
SPECIAL['google_golang_org.grpc'] = dict(
    doc='''Its fact (`grpcInit`, `cache/v3/Base.lean`): `EnableTracing` holds `false` for good. Its
initializer initializes its imports, allocates `EnableTracing` (`var EnableTracing bool`,
`trace.go:33` at v1.84.0: translated, no initializer, so its cell holds `false`), runs the
untranslated initializers of its other variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated `init`
functions, which the trust-boundary axiom `initFuncsOk` says return. (Until 2026-11-19 the cell
came from the trust-boundary axiom `DefaultBackoffConfig_init`.) No translated code writes
`EnableTracing`; a program that writes it (etcd's `embed` at log level debug, grpc-proxy `--debug`)
gets no proof: it would need the cell, which `finish` makes persistent.''',
    alloc_types={'EnableTracing': 'Bool'},
    finish=['ipersist HEnableTracing'] + FIN_PRE[:6],
)

# (sweep repairs 1, B5, 2026-11-08) the default gate's registration: `features`' `init`
SPECIAL['k8s_io.apiserver.pkg.features'] = dict(
    doc='''Its fact (`featuresInit`, `storage/etcd3/Base.lean`): `DefaultFeatureGate` holds a gate with
the specs of `k8sfeature.featureGateOk` (`util/feature/Gate.lean`: `Enabled` of the queried
features, `Set` of one to its `k8sSetValue`). Its initializer initializes its import (`util/feature`, whose
fact gives the gate) and runs its variable's untranslated initializer (`opaqueInitsOk`) and its
untranslated `init` (`kube_features.go:347-350`, `DefaultMutableFeatureGate.AddVersioned(...)` and
`zpagesfeatures.AddFeatureGates(...)` under `runtime.Must`), whose trust-boundary axiom
`init_0_ok` says it registers the package's features with that gate.''',
    custom_initfn={'init.«0»': dict(
        name='init_0_ok',
        doc='/-- `init.«0»` (`kube_features.go:347-350`): registers the package\'s features (and component-base\'s zpages features) with the default gate `DefaultMutableFeatureGate` holds, under `runtime.Must`; after it the gate has the specs of `featureGateOk` (`util/feature/Gate.lean`). -/',
        binder='∀ g : GoInterfaceOk,',
        pre='globalAddr k8s_io.apiserver.pkg.util.feature.DefaultMutableFeatureGate ↦□ GoInterface.ok g',
        post='EtcdGrove.k8sfeature.featureGateOk g',
        apply=['ihave #Hfi : (_root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.featureInit : IProp GF) $$ []',
               '· iapply isPkgInit_access $$ {Hd:k8s_io.apiserver.pkg.util.feature}',
               'icases Hfi with ⟨%g0, #Hmg, #Hdg⟩',
               'wp_apply (init_0_ok g0) $$ [] as #Hgate',
               '· iframe #'])},
    finish=FIN_PRE[:6] + ['imodintro', 'iexists _', 'iframe #'],
)

SPECIAL['k8s_io.apiserver.pkg.storage.feature'] = dict(
    doc='''Its fact (`checkerInit`, `storage/etcd3/Base.lean`): `CheckClient` on
`DefaultFeatureSupportChecker`'s checker returns, stated as the call's own WP, the variable's load
included (the interface type is axiomatized, Goose's gap G1). Its initializer initializes its
imports and runs its variables' untranslated initializers (`feature_support_checker.go`); the
trust-boundary axiom `DefaultFeatureSupportChecker_init` states the one the fact reads
(`newDefaultFeatureSupportChecker()`, whose `CheckClient` starts, once per endpoint, a goroutine
polling the endpoint's `Status`, and returns), `opaqueInitsOk` the others.''',
    custom={'DefaultFeatureSupportChecker': dict(
        doc='/-- `DefaultFeatureSupportChecker = newDefaultFeatureSupportChecker()` (`feature_support_checker.go`): a checker whose `CheckClient` returns for a constructed client and its context (`checkClientOk`; sweep repairs 1, B5: until then for any arguments) (the variable never changes after). -/',
        post=f'_root_.Perennial.{_K3}.checkerInit (GF := GF)',
        pat='#H@')},
    finish=FIN_PRE[:6],
)

# (prove-b64clock, 2026-11-20) clockwork's `keyClock = contextKey("clock")`, translated (a string
# conversion, which `wp_auto` runs); `ErrFakeClockDeadlineExceeded`'s `fmt.Errorf("...: %w", ...)` stays
# untranslated (`opaqueInitsOk`): Perennial's `Errorf` model is faithful only for formats without verbs.
SPECIAL['github_com.jonboulle.clockwork'] = dict(alloc_types={'keyClock': 'GoString'})

SPECIAL['encoding.base64'] = dict(
    doc='''Its fact (`base64Init`, `encoding/base64/Base.lean`; the auth plan's E2x, 2026-10-26;
k8s 7e-2, 2026-11-09): `StdEncoding` and `RawURLEncoding` hold fixed `*Encoding`s whose
`EncodeToString` returns the standard encoding (`stdEnc`), resp. the URL encoding without padding
(`rawUrlEnc`), of its argument's bytes, stated as the method call's own WP.
Its initializer allocates its four variables and runs their translated initializers (`base64.go`,
translated with their bodies since 2026-11-20, prove-b64clock; until then the trust-boundary axioms
`StdEncoding_init`, `RawURLEncoding_init` and `opaqueInitsOk`): `NewEncoding` of the two alphabets
(`NewEncoding.wp_proof`; valid alphabets, `stdAlphabet_ok`, `urlAlphabet_ok`), and `WithPadding(NoPadding)`
of each (`Encoding.WithPadding.wp_proof`); the fact's parts from `EncodeToString`'s spec
(`stdEncInit_intro`, `rawUrlEncInit_intro`).''',
    imports=['Proof.encoding.base64.NewEncoding', 'Proof.encoding.base64.Encoding__WithPadding',
             'Proof.encoding.base64.Encoding__EncodeToString', 'Proof.encoding.base64.Encoding__EncodedLen',
             'Proof.encoding.base64.Encoding__Encode', 'Proof.encoding.base64.InitFacts',
             'Proof.encoding.base64.Encoding__DecodeString', 'Proof.encoding.base64.Encoding__DecodedLen',
             'Proof.encoding.base64.decodedLen', 'Proof.encoding.base64.Encoding__Decode',
             'Proof.encoding.base64.Encoding__decodeQuantum', 'Proof.encoding.base64.assemble32',
             'Proof.encoding.base64.assemble64', 'Proof.internal.byteorder.BEPutUint32',
             'Proof.internal.byteorder.BEPutUint64', 'Perennial.Proof.internal.byteorder.Link'],
    alloc_types={'StdEncoding': 'Loc', 'URLEncoding': 'Loc', 'RawStdEncoding': 'Loc', 'RawURLEncoding': 'Loc'},
    before={'$end': [
        'try wp_auto',
        'wp_apply (EtcdGrove.base64.NewEncoding.wp_proof _ (by exact EtcdGrove.base64.stdAlphabet_ok.1)',
        '    (by exact EtcdGrove.base64.stdAlphabet_ok.2.1) (by exact EtcdGrove.base64.stdAlphabet_ok.2.2.1)',
        '    (by exact EtcdGrove.base64.stdAlphabet_ok.2.2.2)) as %eS ⟨%encS, HeS, %hS⟩',
        'try wp_auto',
        'wp_apply (EtcdGrove.base64.NewEncoding.wp_proof _ (by exact EtcdGrove.base64.urlAlphabet_ok.1)',
        '    (by exact EtcdGrove.base64.urlAlphabet_ok.2.1) (by exact EtcdGrove.base64.urlAlphabet_ok.2.2.1)',
        '    (by exact EtcdGrove.base64.urlAlphabet_ok.2.2.2)) as %eU ⟨%encU, HeU, %hU⟩',
        'try wp_auto',
        'wp_apply (EtcdGrove.base64.Encoding.WithPadding.wp_proof eS encS _) $$ HeS as %eRS ⟨HeS, HeRS⟩',
        'try wp_auto',
        'wp_apply (EtcdGrove.base64.Encoding.WithPadding.wp_proof eU encU _) $$ HeU as %eRU ⟨HeU, HeRU⟩',
        'try wp_auto']},
    finish=['ipersist HStdEncoding', 'ipersist HRawURLEncoding', 'ipersist HeS', 'ipersist HeRU'] +
           FIN_PRE[:6] + ['try (isplitl []; · (imodintro; itrivial))', 'imodintro',
            'unfold _root_.Perennial.encoding.base64.base64Init', 'isplitl',
            '· iapply (EtcdGrove.base64.stdEncInit_intro (EtcdGrove.base64.Encoding.EncodeToString.wp_proof',
            '      EtcdGrove.base64.Encoding.EncodedLen.wp_proof EtcdGrove.base64.Encoding.Encode.wp_proof)',
            '    eS encS hS.1 hS.2.1) $$ HStdEncoding HeS',
            'isplitl',
            '· iapply (EtcdGrove.base64.rawUrlEncInit_intro (EtcdGrove.base64.Encoding.EncodeToString.wp_proof',
            '      EtcdGrove.base64.Encoding.EncodedLen.wp_proof EtcdGrove.base64.Encoding.Encode.wp_proof)',
            '    eRU { encU with padChar\' := W32 (-1) } hU.1 rfl) $$ HRawURLEncoding HeRU',
            # (prove-authcrypto, 2026-11-21) the decoder's part
            'iapply (EtcdGrove.base64.stdDecInit_intro (EtcdGrove.base64.Encoding.DecodeString.wp_proof',
            '    (EtcdGrove.base64.Encoding.DecodedLen.wp_proof EtcdGrove.base64.decodedLen.wp_proof)',
            '    (EtcdGrove.base64.Encoding.Decode.wp_proof (EtcdGrove.base64.Encoding.decodeQuantum.wp_proof)',
            '      EtcdGrove.base64.assemble32.wp_proof EtcdGrove.base64.assemble64.wp_proof',
            '      (EtcdGrove.byteorder.BEPutUint32.wp_proof _root_.Perennial.internal.byteorder.wp_BEPutUint32)',
            '      (EtcdGrove.byteorder.BEPutUint64.wp_proof _root_.Perennial.internal.byteorder.wp_BEPutUint64)))',
            '  eS encS hS.1 hS.2.1 (by rw [hS.1]; exact hS.2.2.1) hS.2.2.2) $$ HStdEncoding HeS'],
)

# (prove-authcrypto, 2026-11-21) bcrypt's variables translated (until then `opaqueInitsOk`):
# `bcEncoding = base64.NewEncoding(alphabet)` over `NewEncoding`'s spec (the alphabet's validity by
# `decide`), the three `errors.New` errors and the byte-slice literal `magicCipherData`
SPECIAL['golang_org.x.crypto.bcrypt'] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer allocates its variables, initializes its imports and runs
their translated initializers (`bcrypt.go`, `base64.go`; prove-authcrypto, 2026-11-21: until then the
trust-boundary axiom `opaqueInitsOk`): `bcEncoding = base64.NewEncoding(alphabet)`
(`NewEncoding.wp_proof`: the alphabet is 64 distinct symbols, neither `\\n` nor `\\r`), three
`errors.New` errors (Perennial's `errors.wp_New_errorString`) and the byte-slice literal
`magicCipherData`.''',
    imports=['Proof.encoding.base64.NewEncoding'],
    alloc_types={'bcEncoding': 'Loc', 'magicCipherData': 'GoSlice'},
    before={'bcEncoding': ['try wp_auto',
                           'wp_apply (EtcdGrove.base64.NewEncoding.wp_proof _ (by decide) (by decide) (by decide)',
                           '    (by decide)) as %eB -',
                           'try wp_auto'],
            'magicCipherData': ['try wp_auto',
                'wp_apply (wp_slice_literal (V := w8) (l := _)); isplitr; (· ipureintro; rfl); iintro %sMC ⟨SMC, -⟩',
                'try wp_auto'],
            '$end': ['try wp_auto']},
    finish=FIN_PRE[:6]), ['ErrMismatchedHashAndPassword', 'ErrHashTooShort', 'ErrPasswordTooLong'])

SPECIAL['k8s_io.apiserver.pkg.storage'] = dict(
    doc='''Its fact (`storageInit`, `storage/etcd3/Base.lean`): `RequestWatchProgress` and
`tooLargeResourceVersionCauseMsg` hold strings, and `Everything` holds, for good, a predicate with no
shard selector whose label and field selectors' `Empty()` is `true` (`everythingOk`, from the two
specs' posts; k8s 7f-5b H2).
Its initializer allocates its translated variables (`errors.go`, `feature.go`, `selection_predicate.go`:
six `errors.New` errors, the map `errCodeToMessage`, three strings, and `Everything`, a
`SelectionPredicate` of `labels.Everything()` and `fields.Everything()`, both proved:
`labels.Everything.wp_proof` (#25, 2026-11-21), `fields.Everything.wp_proof`), initializes
its imports and runs the translated initializers.''',
    imports=['Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar', 'Proof.k8s_io.apimachinery.pkg.labels.Everything',
             'Proof.k8s_io.apimachinery.pkg.fields.Everything'],
    alloc_types={'Everything': 'SelectionPredicate', 'RangeStream': 'GoString',
                 'RequestWatchProgress': 'GoString', 'tooLargeResourceVersionCauseMsg': 'GoString',
                 'errCodeToMessage': 'Loc', 'ErrStorageNotReady': 'GoInterface',
                 'ErrResourceVersionSetOnCreate': 'GoInterface',
                 'ErrUnrecognizedEncodedVersion': 'GoInterface', 'ErrGenericInvalidKey': 'GoInterface',
                 'ErrEmptyStartKey': 'GoInterface', 'ErrInvalidStartRV': 'GoInterface'},
    before={'$end': [
        'try wp_auto'] + ['wp_apply _root_.Perennial.errors.wp_New_errorString as %_ -', 'try wp_auto'] * 6 + [
        'wp_apply (wp_map_make1 (K := w64) (V := GoString) go.int go.string) as %mref Hmap',
        'try wp_auto',
        'repeat (wp_apply (wp_mapInsert (K := w64) (V := GoString) go.int) $$ Hmap as Hmap; try wp_auto)',
        'wp_apply EtcdGrove.labels.Everything.wp_proof as %_ ⟨%il, %Hil, -, #HlE⟩',
        'try wp_auto',
        'wp_apply EtcdGrove.fields.Everything.wp_proof as %_ ⟨%ifd, %Hif, #HfE⟩',
        'try wp_auto']},
    finish=['ipersist HRequestWatchProgress', 'ipersist HtooLargeResourceVersionCauseMsg',
            'ipersist HEverything'] +
           FIN_PRE[:7] + ['imodintro', 'iexists _, _, _', 'iframe #',
            'unfold _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.everythingOk',
            'isplitr', '· ipureintro; rfl',
            'isplitr', '· iexists il; iframe #; ipureintro; exact Hil',
            'iexists ifd; iframe #; ipureintro; exact Hif'],
)

# client-go's leaf libraries (2026-10-26, notes/k8s-clientgo-goose.md): their facts are `True`; their
# translated initializers are composite literals (no call), which `wp_auto` runs.
SPECIAL['k8s_io.client_go.tools.cache'] = dict(
    doc='''Its fact (`k8sCacheInit`, `Proof/k8s_io/apiserver/pkg/storage/cacher/Base.lean`; phase 4
of the DaemonSet plan, 2026-10-27): `ErrFIFOClosed` and `errorStopRequested` (untranslated
`errors.New` calls, `fifo.go`, `reflector.go`) hold some error each, for good: the trust-boundary
axioms `ErrFIFOClosed_init` and `errorStopRequested_init`. Its initializer allocates its translated
variables (`informer_metrics.go`: `globalInformerMetricsProvider`, a
`noopInformerMetricsProvider{}`, and the zero `setInformerMetricsProviderOnce`;
`mutation_detector.go`: `mutationDetectionEnabled`, `false`), initializes its imports, runs the
other variables' untranslated initializers, which the trust-boundary axiom `opaqueInitsOk` says run
without panicking, and the translated ones, and its translated `init` (`mutation_detector.go:35`),
which stores in `mutationDetectionEnabled` whether `KUBE_CACHE_MUTATION_DETECTOR` parses as true
(`os.Getenv`: the trust-boundary axiom `os.Getenv.wp_proof`; `strconv.ParseBool.wp_proof`). (Until
2026-11-24 the `init`, translated but in chunks, was the trust-boundary axiom `initFuncsOk`, and
`mutationDetectionEnabled`'s initializer untranslated.)''',
    alloc_types={'setInformerMetricsProviderOnce': '_root_.Perennial.sync.Once',
                 'globalInformerMetricsProvider': 'GoInterface', 'mutationDetectionEnabled': 'Bool'},
    imports=['Proof.os.Getenv', 'Proof.strconv.ParseBool'],
    # (k8s-inits-2, 2026-11-24, #32) the translated `init` (`mutation_detector.go:35`), until then
    # `initFuncsOk` (a translated `init` in chunks kept its axiom)
    after={'init.«0»': _GETENV_PARSEBOOL},
    custom={'ErrFIFOClosed': dict(
                doc='/-- `ErrFIFOClosed = errors.New("DeltaFIFO: manipulating with closed queue")` (`fifo.go`): an error. -/',
                post='∃ e : GoInterface, globalAddr ErrFIFOClosed ↦ e', pat='⟨%e@, H@⟩'),
            'errorStopRequested': dict(
                doc='/-- `errorStopRequested = errors.New("stop requested")` (`reflector.go`): an error. -/',
                post='∃ e : GoInterface, globalAddr errorStopRequested ↦ e', pat='⟨%e@, H@⟩')},
    before={'$end': ['try wp_auto']},
    finish=['ipersist HErrFIFOClosed', 'ipersist HerrorStopRequested'] + FIN_PRE[:7] + [
            'imodintro', 'iexists _, _', 'iframe #'],
)

SPECIAL['k8s_io.client_go.util.workqueue'] = dict(
    doc='''Its fact (`workqueueInit`, `Proof/k8s_io/client_go/Base.lean`; 2026-10-26, the queue's
proofs): `globalMetricsProvider` holds the no-op provider, read-only for good. Its initializer
allocates its variables (`metrics.go`: `globalMetricsProvider`, a `noopMetricsProvider{}`, and the
zero `setGlobalMetricsProviderOnce`), initializes its imports and runs the translated initializer.''',
    alloc_types={'setGlobalMetricsProviderOnce': '_root_.Perennial.sync.Once',
                 'globalMetricsProvider': 'GoInterface'},
    before={'$end': ['try wp_auto']},
    finish=['ipersist HglobalMetricsProvider'] + FIN_PRE[:6] + ['imodintro',
            'unfold _root_.Perennial.k8s_io.client_go.workqueueInit', 'iexact HglobalMetricsProvider'],
)

SPECIAL['k8s_io.client_go.util.retry'] = dict(
    doc='''Its fact is `True`. Its initializer allocates its variables (`util.go`: `DefaultRetry`,
`DefaultBackoff`, `wait.Backoff` literals), initializes its imports and runs the translated
initializers.''',
    alloc_types={x: '_root_.Perennial.k8s_io.apimachinery.pkg.util.wait.Backoff'
                 for x in ['DefaultRetry', 'DefaultBackoff']},
    before={'$end': ['try wp_auto']},
)

# the driver's error variables and the tags of their `errors.New` results
_K8E = [('errNotObj', 'NO'), ('errBadData', 'BD'), ('errBadRV', 'BR'),
        ('errDeleteRejected', 'DR'), ('errUpdateRejected', 'UR')]

def _errVarOk(x, t):
    """`errVarOk x msg` (the driver's `Base.lean`) of the `errors.New` result `x<t>` (`#M<t>`,
    its `errorString` `#C<t>`)."""
    return [f'iexists x{t}', f'iframe H{x} C{t}',
            'unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.errorStringSpec',
            'iintro !> %Φ HΦ', f'iapply M{t}', 'inext', 'iapply HΦ']

SPECIAL['github_com.mit_pdos.etcd_grove.examples.k8s.etcd3'] = dict(
    doc='''Its fact (`drvInit`, `Base.lean`): its error variables (`k8setcd3.go`: `errNotObj`,
`errBadData`, `errBadRV`, `errDeleteRejected`, `errUpdateRejected`, translated
`errors.New` calls) each hold a fixed `*errorString` whose `Error()` returns and which holds
its message, read-only (`wp_New_errorString_struct`). Its initializer allocates them, initializes
its imports and runs their translated initializers.''',
    imports=['Proof.errors.NewVarCell'],
    alloc_types={x: 'GoInterface' for x, _ in _K8E},
    before={'$end': ['try wp_auto'] + [l for _, t in _K8E for l in [
        f'wp_apply github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.wp_New_errorString_struct as %x{t} ⟨#M{t}, #C{t}⟩',
        'try wp_auto']]},
    finish=[f'ipersist H{x}' for x, _ in _K8E] + FIN_PRE[:6] + ['imodintro', 'unfold drvInit'] +
           [l for x, t in _K8E[:-1] for l in ['isplitr'] + ['· ' + m if j == 0 else '  ' + m
                                                     for j, m in enumerate(_errVarOk(x, t))]] +
           _errVarOk(*_K8E[-1]),
)

SPECIAL[_K3] = dict(
    doc='''Its fact (`EtcdGrove.k8s.registryFact`, `RegistryDefs.lean`): `endpointsMapMu` is a mutex over
the compactor registry, at the registry's name (`CompactorRegistry`, a variable of every package
importing this one). Its initializer allocates its variables, initializes its imports, runs
the translated initializers (`errTooMany`, an `errors.New` error; `typeToMessage`, a map literal;
`defaultWatcherMaxLimit`, kept read-only in the fact) and its translated `init` functions: `compact.go`'s makes
`endpointsMap` (then the registry's mutex is made, with the map empty), `logger.go`'s sets grpc's logger (`grpclog.SetLoggerV2`, names-only: the
trust-boundary axiom `grpclog.SetLoggerV2.wp_proof`), `watcher.go`'s stores in
`fatalOnDecodeError` whether `KUBE_PANIC_WATCH_DECODE_ERROR` parses as true (`os.Getenv` and
`strconv.ParseBool`: the trust-boundary axiom `os.Getenv.wp_proof`, and `strconv.ParseBool.wp_proof`, proved
over Perennial's translation since 2026-11-20).''',
    pre=['section toLoggerV2',
         'variable [GooseExts] [GooseSemantics] [GooseInterp]',
         'variable [go_gctx : GoGlobalContext]',
         '',
         '/-- A `klogWrapper` is not grpc\'s `*componentData` (`SetLoggerV2`\'s premise). -/',
         'theorem k8s_io.apiserver.pkg.storage.etcd3.klogWrapper_ne_componentData (v w : val) :',
         '    interface.mkOk k8s_io.apiserver.pkg.storage.etcd3.klogWrapper.ty v ≠',
         '      interface.mkOk (go.GoType.PointerType google_golang_org.grpc.grpclog.componentData.ty) w := by',
         '  intro h',
         '  injection h with h',
         '  injection h with h',
         '  unfold k8s_io.apiserver.pkg.storage.etcd3.klogWrapper.ty at h',
         '  cases h',
         '',
         'end toLoggerV2',
         ''],
    imports=['Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar', 'Perennial.Proof.sync.atomic.Link',
             'Proof.google_golang_org.grpc.grpclog.SetLoggerV2', 'Proof.os.Getenv',
             'Proof.strconv.ParseBool'],
    vars=['[reg : EtcdGrove.k8s.CompactorRegistry]'],
    table_vars=['[reg : EtcdGrove.k8s.CompactorRegistry]'],
    finish=['ipersist HdefaultWatcherMaxLimit'] + FIN_PRE[:6] +
        ['imodintro', 'unfold EtcdGrove.k8s.registryFact', 'iframe Hreg', 'iexact HdefaultWatcherMaxLimit'],
    alloc_types={'fatalOnDecodeError': "_root_.Perennial.sync.atomic.Bool'", 'defaultWatcherMaxLimit': 'w64',
                 'typeToMessage': 'Loc', 'errTooMany': 'GoInterface', 'endpointsMap': 'Loc',
                 'endpointsMapMu': '_root_.Perennial.sync.Mutex'},
    before={'$inits': [
        'try wp_auto',
        'wp_apply _root_.Perennial.errors.wp_New_errorString as %_ -',
        'try wp_auto',
        'wp_apply (wp_map_make1 (K := w64) (V := GoString) go.int go.string) as %mref Hmap',
        'try wp_auto',
        'repeat (wp_apply (wp_mapInsert (K := w64) (V := GoString) go.int) $$ Hmap as Hmap; try wp_auto)',
        'wp_alloc dd as Hdd', 'try wp_auto', 'wp_alloc tw as Htw', 'try wp_auto']},
    after={
        # (Q1 (c), 2026-11-05) the compactor registry: the mutex over the map (`registryFact`)
        'init.«0»': ['wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string',
                     '    (go.GoType.PointerType compactor.ty)) as %em Hem',
                     'try wp_auto',
                     'imod _root_.Perennial.sync.init_Mutex (EtcdGrove.k8s.registryInv (GF := GF)) ⊤ _',
                     '    $$ HendpointsMapMu [HendpointsMap Hem] with #Hreg',
                     '· inext',
                     '  iunfold EtcdGrove.k8s.registryInv',
                     '  iexists em, ∅',
                     '  iframe HendpointsMap Hem',
                     '  iapply BigSepM.bigSepM_empty.2',
                     '  itrivial'],
        # (prove-k8s3, 2026-11-21) the conversion of the `klogWrapper` to grpclog's `LoggerV2` steps
        # (grpclog imports `grpclog/internal`, so `LoggerV2` is an interface); until then the
        # trust-boundary axiom `klogWrapper_toLoggerV2`
        # (`grpclog.LoggerV2` is a named `internal.LoggerV2`: `≤u` has no transitive instance)
        'init.«1»': ['haveI : google_golang_org.grpc.grpclog.LoggerV2.ty ≤u '
                     'google_golang_org.grpc.grpclog.internal.LoggerV2.underlying := '
                     '⟨(go.underlying_unfold (t := google_golang_org.grpc.grpclog.LoggerV2.ty)).trans '
                     '(go.underlying_unfold (t := google_golang_org.grpc.grpclog.internal.LoggerV2.ty))⟩',
                     'try wp_auto',
                     'wp_apply (EtcdGrove.grpclog.SetLoggerV2.wp_proof _',
                     '    (k8s_io.apiserver.pkg.storage.etcd3.klogWrapper_ne_componentData _))',
                     'try wp_auto'],
        'init.«2»': ['wp_apply EtcdGrove.os.Getenv.wp_proof as %_ -', 'try wp_auto',
                     'wp_apply EtcdGrove.strconv.ParseBool.wp_proof as %_ %_ -', 'try wp_auto',
                     'ihave Hfod : _root_.Perennial.sync.atomic.ownBool (GF := GF) (globalAddr fatalOnDecodeError) (DFrac.own 1) false $$ [HfatalOnDecodeError]',
                     '· rw [_root_.Perennial.sync.atomic.ownBool_unseal]',
                     '  unfold _root_.Perennial.sync.atomic.ownBoolDef',
                     "  have e : (zero_val _root_.Perennial.sync.atomic.Bool') =",
                     "      ({ «_#0'» := zero_val _, v' := _root_.Perennial.sync.atomic.b32w false } :",
                     "        _root_.Perennial.sync.atomic.Bool') := rfl",
                     '  rw [← e]; iexact HfatalOnDecodeError',
                     'wp_apply_core _root_.Perennial.sync.atomic.Bool.wp_Store $$ [] [-]',
                     '· iPkgInit',
                     'iapply fupd_mask_intro Std.LawfulSet.empty_subset',
                     'iintro Hmask',
                     'inext; iexists _; iframe Hfod; iintro _',
                     'imod Hmask with _',
                     'imodintro',
                     'try wp_auto']},
)

# (metric-vecs, 2026-11-19) a metric vector whose initializer is translated: `prometheus.New<kind>Vec`
# of an options literal and a `[]string` literal of label names (a histogram's buckets
# `ExponentialBuckets(start, 2, n)`), over prometheus's constructor specs: `v<x>` the vector, `#L<x>`
# its label names (`vecLabels`), the steps before its store (`before`, keyed by the variable). Until
# then the trust-boundary axioms `<X>_init`, with the same post (D19l (iii), 2026-10-18).
PROM_VEC_CTORS = [f'Proof.github_com.prometheus.client_golang.prometheus.{f}'
                  for f in ['NewCounterVec', 'NewGaugeVec', 'NewHistogramVec', 'ExponentialBuckets']]

def vec_steps(x, kind, labels):
    P = 'EtcdGrove.prometheus'
    ls = '[' + ', '.join(f'go!"{l}"' for l in labels) + ']'
    pre, opts, more, hb = ['try wp_auto'], 'rfl', '', ''
    if kind == 'Histogram':
        pre += [f'wp_apply {P}.ExponentialBuckets.wp_proof _ _ _ (by rfl) (by decide) as %b{x} B{x}',
               'try wp_auto']
        opts, more, hb = '(by rfl)', f' ({P}.expBuckets_ok (by decide)) (by decide)', f' $B{x}'
    args = '_ _ _ _ _ ' + ('_ _ ' if kind == 'Histogram' else '') + ls + ' _ _' + (' _' if kind == 'Histogram' else '')
    return pre + [
        f'wp_apply (wp_slice_literal (l := {ls})); isplitr; (· ipureintro; rfl); iintro %s{x} ⟨S{x}, -⟩',
        'try wp_auto',
        f'wp_apply {P}.New{kind}Vec.wp_proof {args} {opts} (by decide) (by decide){more} $$ [$S{x}{hb}]'
        f' as %v{x} ⟨#L{x}, -⟩',
        'try wp_auto']

def promvec(cfg, x, kind, labels):
    """`x = prometheus.New<kind>Vec(opts, labels)`, translated (`vec_steps`) in the package config
    `cfg`: a fixed pointer with its label names (`EtcdGrove.prometheus.vecLabels`)."""
    cfg.setdefault('before', {})[x] = vec_steps(x, kind, labels)
    cfg.setdefault('alloc_types', {})[x] = 'Loc'
    imps = cfg.setdefault('imports', [])
    imps += [m for m in PROM_VEC_CTORS if m not in imps]

# (2026-10-23, rafthttp stage 4) the pipeline's metric vectors
for _x, _l in [('receivedBytes', 'From'), ('recvFailures', 'From'), ('sentBytes', 'To'),
               ('sentFailures', 'To')]:
    promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'], _x, 'Counter', [_l])
# (2026-10-23, rafthttp stage 4d) the peer status's
promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'], 'activePeers', 'Gauge', ['Local', 'Remote'])
promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'], 'disconnectedPeers', 'Counter', ['Local', 'Remote'])
# (2026-10-23, rafthttp stage 6c) the probers' round-trip histogram, which `AddPeer` hands to
# `addPeerToProber` (untranslated, the prober's axiom): the fact only says it is some pointer
promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'], 'rttSec', 'Histogram', ['To'])
# (prove-errinits, 2026-11-19) its errors' initializers translated, with their message cells:
# `errors.New`, and (`errMemberRemoved`, `errUnsupportedStreamType`) `fmt.Errorf` without verbs
newvars_cfg(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'],
            ['ErrExceedSizeLimit', 'errIncompatibleVersion', 'ErrClusterIDMismatch', 'errStopped',
             'errMemberRemoved', 'errUnsupportedStreamType'], cell=True,
            errorf={'errMemberRemoved': 'the member has been permanently removed from the cluster',
                    'errUnsupportedStreamType': 'unsupported stream type'})
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp']['finish'][0:0] = [
    'ipersist HreceivedBytes', 'ipersist HrecvFailures', 'ipersist HsentBytes', 'ipersist HsentFailures',
    'ipersist HactivePeers', 'ipersist HdisconnectedPeers', 'ipersist HrttSec']
# (2026-10-24, rafthttp stage 7d) the snapshot sender's and handler's metric vectors
_SNAP_METRICS = [('snapshotSend', 'Counter', 'To'), ('snapshotSendInflights', 'Gauge', 'To'),
                 ('snapshotSendFailures', 'Counter', 'To'), ('snapshotSendSeconds', 'Histogram', 'To'),
                 ('snapshotReceive', 'Counter', 'From'), ('snapshotReceiveInflights', 'Gauge', 'From'),
                 ('snapshotReceiveFailures', 'Counter', 'From'),
                 ('snapshotReceiveSeconds', 'Histogram', 'From')]
for _x, _k, _l in _SNAP_METRICS:
    promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'], _x, _k, [_l])
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp']['finish'][0:0] = [
    f'ipersist H{_x}' for _x, _, _ in _SNAP_METRICS]

_MEMBERSHIP_ERRS = ['ErrIDRemoved', 'ErrIDExists', 'ErrIDNotFound', 'ErrPeerURLexists',
                    'ErrMemberNotLearner', 'ErrTooManyLearners']
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.membership'] = dict(
    doc='''Its fact (`membershipInit`, `etcdserver/apply/Base.lean`): `ClusterVersionMetrics` holds a
fixed pointer (a `*prometheus.GaugeVec`, with its label names: D19l (iii)), and (D43 M4,
2026-10-26) every error variable its `errors.New` error (`errorsNewVars membershipErrMsgs`). Its
initializer allocates its error variables, initializes its imports, runs their translated
initializers (`errors.go`: `errors.New` calls, Perennial's `errors.wp_New_errorString`; translated
since 2026-11-19, until then the trust-boundary axiom `errorsNewVarsInit`) and its other variables'
untranslated initializers (`opaqueInitsOk`), but the one the fact reads, `ClusterVersionMetrics`
(`metrics.go`: `prometheus.NewGaugeVec(...)`, translated, over its spec; until 2026-11-19 the
trust-boundary axiom `ClusterVersionMetrics_init`).''',
    imports=['Perennial.Proof.errors.NewVar'],
    alloc_types={x: 'GoInterface' for x in _MEMBERSHIP_ERRS},
    before={x: ['try wp_auto', f'wp_apply _root_.Perennial.errors.wp_New_errorString as %x{x} ⟨#_, #M{x}⟩']
            for x in _MEMBERSHIP_ERRS},
    finish=['ipersist HClusterVersionMetrics'] +
        [f'ipersist H{x}' for x in _MEMBERSHIP_ERRS] +
        # (prove-ps2-metrics, 2026-11-22) the membership writers' metrics, in the fact
        ['ipersist HisLearner', 'ipersist HknownPeers'] + FIN_PRE[:6] +
        ['try (isplitl []; · (imodintro; itrivial))', 'imodintro',
         'unfold membershipInit membershipErrMsgs',
         'simp only [EtcdGrove.errorsNewVars, EtcdGrove.errorsNewVar]',
         'iframe #'],
)

promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.membership'], 'ClusterVersionMetrics', 'Gauge',
        ['cluster_version'])
# (prove-errinits, 2026-11-19) its other variables translated (until then `opaqueInitsOk`): the gauge
# vector `knownPeers`, the gauge `isLearner`, and the v2 store's paths `StoreMembersPrefix` and
# `storeRemovedMembersPrefix` (`path.Join(storePrefix, ...)`, `storev2.go`; `path.Join`'s proof)
def path_join_steps(prefix_const, prefix, seg, tag):
    es = f'[go!"{prefix}", go!"{seg}"]'
    return ['try wp_auto', f'try simp only [{prefix_const}]', 'try wp_auto',
            f'wp_apply (wp_slice_literal (l := {es})); isplitr; (· ipureintro; rfl); iintro %pj{tag} ⟨Sj{tag}, -⟩',
            'try wp_auto',
            'wp_apply (EtcdGrove.path.Join.wp_proof (EtcdGrove.path.Clean.wp_proof '
            'EtcdGrove.path.lazybuf.index.wp_proof EtcdGrove.path.lazybuf.append.wp_proof '
            f'EtcdGrove.path.lazybuf.string.wp_proof)) _ {es} _ (by decide) $$ [$Sj{tag}] as %rj{tag} ⟨%Hj{tag}, -⟩',
            'try wp_auto']
_MS = SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.membership']
promvec(_MS, 'knownPeers', 'Gauge', ['Local', 'Remote'])
_MS['alloc_types'].update({'isLearner': 'GoInterface', 'StoreMembersPrefix': 'GoString',
                           'storeRemovedMembersPrefix': 'GoString'})
_MS['before'].update({'isLearner': metric_steps('isLearner', 'gauge'),
                      'StoreMembersPrefix': path_join_steps('storePrefix', '/0', 'members', 'M'),
                      'storeRemovedMembersPrefix': path_join_steps('storePrefix', '/0', 'removed_members', 'R')})
_MS['imports'] += [m for m in PROM_CTORS + ['Proof.path.Join', 'Proof.path.Clean', 'Proof.path.lazybuf__index',
                   'Proof.path.lazybuf__append', 'Proof.path.lazybuf__string'] if m not in _MS['imports']]
_MS['doc'] = _MS['doc'].replace("""untranslated initializers (`opaqueInitsOk`), but the one the fact reads,""",
    """initializers (translated 2026-11-19, until then untranslated, `opaqueInitsOk`: the gauge vector
`knownPeers`, the gauge `isLearner`, and the store paths `StoreMembersPrefix` and
`storeRemovedMembersPrefix`, `path.Join` calls, over its proof), and the one the fact reads,""")

def hist(x, file='metrics.go'):
    return dict(doc=f'/-- `{x} = prometheus.NewHistogram(...)` (`{file}`): a `Histogram`, whose `Observe` returns. -/',
                post=f'∃ h : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok h ∗ histSpec h',
                pat='⟨%h@, H@, #S@⟩')

_BE_HIST = ['commitSec', 'rebalanceSec', 'spillSec', 'writeSec']
SPECIAL['go_etcd_io.etcd.server.v3.storage.backend'] = dict(
    doc='''Its fact (`backendInit`, `Base.lean`): the commit's histograms `rebalanceSec`,
`spillSec`, `writeSec`, `commitSec` hold `Histogram`s whose `Observe` returns. Its initializer
allocates and sets its translated constants, initializes its imports and runs its variables'
untranslated initializers: the four the fact reads are translated (`metrics.go`:
`prometheus.NewHistogram(...)` of `ExponentialBuckets`, over their specs; until 2026-11-19 the
trust-boundary axioms `<X>_init`), `opaqueInitsOk` states the others.''',
    custom={},
    imports=PROM_CTORS,
    before={x: metric_steps_to(x, 'hist', 'go_etcd_io.etcd.server.v3.storage.backend.histSpec')
            for x in _BE_HIST},
    alloc_types={**{x: 'GoInterface' for x in _BE_HIST},
                 'defaultBatchLimit': 'w64', 'defaultBatchInterval': 'w64', 'defragLimit': 'w64',
                 'InitialMmapSize': 'w64', 'minSnapshotWarningTimeout': 'w64'},
    finish=['ipersist HcommitSec', 'ipersist HrebalanceSec', 'ipersist HspillSec', 'ipersist HwriteSec']
           + FIN_PRE[:6] + ['imodintro', 'unfold backendInit', 'iframe #'],
)

# (R10, 2026-11-07) mvcc's randomized tester: its two string-slice literals, persisted
SPECIAL['github_com.mit_pdos.etcd_grove.examples.mvccrand'] = dict(
    doc='''Its fact (`mvccrandInit`, `Base.lean`): `keys` and `extraEnds` hold read-only slices of
`keyList` and `extraEndList`. Its initializer allocates them, initializes its imports and runs their
translated initializers, two slice literals (`mvccrand.go`), whose slices are made persistent.''',
    alloc_types={'keys': 'GoSlice', 'extraEnds': 'GoSlice'},
    before={'keys': ['try wp_auto',
                     'wp_apply (wp_slice_literal (l := [go!"a", go!"aa", go!"b", go!"ba", go!"c", go!"d"])); isplitr; (· ipureintro; rfl); iintro %pK ⟨SK, -⟩',
                     'try wp_auto'],
            'extraEnds': ['try wp_auto',
                          'wp_apply (wp_slice_literal (l := [go!"bb", go!"z"])); isplitr; (· ipureintro; rfl); iintro %pE ⟨SE, -⟩',
                          'try wp_auto'],
            '$end': ['try wp_auto']},
    finish=['ipersist Hkeys', 'ipersist HextraEnds', 'imod ownSlice_persist $$ SK with #SK',
            'imod ownSlice_persist $$ SE with #SE'] + FIN_PRE[:6] +
           ['imodintro', 'unfold mvccrandInit keyList extraEndList', 'iframe #'],
)

SPECIAL['go_etcd_io.etcd.api.v3.etcdserverpb'] = dict(
    doc='''Its fact is `True`. Its initializer allocates and sets the translated gRPC service
descriptors (`KV_ServiceDesc`, ...: `grpc.ServiceDesc` literals), initializes its imports and
runs its other variables' untranslated initializers (the generated protobuf descriptors and enum
name maps), which the trust-boundary axiom `opaqueInitsOk` says run.''',
    alloc_types={x: 'google_golang_org.grpc.ServiceDesc' for x in
                 ['Auth_ServiceDesc', 'Maintenance_ServiceDesc', 'Cluster_ServiceDesc',
                  'Lease_ServiceDesc', 'Watch_ServiceDesc', 'KV_ServiceDesc']},
    finish=['repeat (wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩; wp_auto)',
            'iframe Hown', 'is_pkg_init_finish'],
)

SPECIAL['go_etcd_io.etcd.server.v3.storage.schema'] = dict(
    doc='''Its fact (`schemaInit`, `etcdserver/Base.lean`): the `Meta`, `Key`, `Auth`, `AuthUsers` and
`AuthRoles` buckets, as `bucket.go` makes them, the consistent index's two key names (`cindex.go`),
the auth bucket's two key names and the auth backend's `authEnabled`/`authDisabled` values
(`auth.go`; the auth plan's S1, 2026-10-23), the lessor's `Lease` bucket (leases T3,
2026-10-25), the membership's `Members`, `MembersRemoved` and `Cluster` buckets (prove-ps2-members,
2026-11-22) and the alarm store's `Alarm` bucket (prove-ps2-v3alarm, 2026-11-24). Its initializer allocates and sets those translated variables (with the buckets'
names), initializes its imports and runs its other variables' initializers, all translated
(prove-initleft, 2026-11-21: `schemaChanges`, a map literal keyed by `version`'s versions, and the
interface assertions; until then the trust-boundary axiom `opaqueInitsOk`), and its `init` function
(`bucket.go`), whose trusted model does nothing (`TrustedCode/go_etcd_io/etcd/server/v3/storage/schema.lean`,
etcd-grove#32; until 2026-11-23 the trust-boundary axiom `initFuncsOk` said it returns).''',
    imports=['Proof.github_com.Masterminds.semver.v3.MapKey'],
    alloc_types={'schemaChanges': 'Loc', 'MetaTermKeyName': 'GoSlice', 'MetaConsistentIndexKeyName': 'GoSlice',
                 'Meta': 'GoInterface', 'Key': 'GoInterface', 'metaBucketName': 'GoSlice',
                 'keyBucketName': 'GoSlice', 'authEnabled': 'GoSlice', 'authDisabled': 'GoSlice',
                 'authBucketName': 'GoSlice', 'authUsersBucketName': 'GoSlice',
                 'authRolesBucketName': 'GoSlice', 'Auth': 'GoInterface', 'AuthUsers': 'GoInterface',
                 'AuthRoles': 'GoInterface', 'AuthEnabledKeyName': 'GoSlice',
                 'AuthRevisionKeyName': 'GoSlice', 'Lease': 'GoInterface',
                 'leaseBucketName': 'GoSlice',
                 **{x: 'GoSlice' for x in ['alarmBucketName', 'clusterBucketName', 'membersBucketName',
                                           'membersRemovedBucketName', 'testBucketName', 'AllBuckets',
                                           'ScheduledCompactKeyName', 'FinishedCompactKeyName',
                                           'MetaConfStateName', 'ClusterClusterVersionKeyName',
                                           'ClusterDowngradeKeyName', 'MetaStorageVersionName',
                                           'emptyStorageVersion']},
                 **{x: 'GoInterface' for x in ['Alarm', 'Cluster', 'Members', 'MembersRemoved', 'Test']}},
    before={
        # `authEnabled`/`authDisabled` (slice literals), then the interface assertions `var _ ... = (*T)(nil)`
        # (prove-initleft, 2026-11-21: until then in `opaqueInitsOk`), stepped by `wp_auto`
        'keyBucketName': ['wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sen ⟨Hsen, -⟩',
                'simp only [go.arrayLiteralSize, List.foldl]', 'try wp_auto',
                'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sdis ⟨Hsdis, -⟩',
                'simp only [go.arrayLiteralSize, List.foldl]', 'try wp_auto'],
        # (2026-11-19) all of `bucket.go`'s variables are translated: the bucket names' conversions, in
        # order (`alarm` ... `test` named `-`: the fact does not read them)
        'leaseBucketName': ['wp_apply wp_string_to_bytes go!"key" as %skey ⟨Hskey, -⟩', 'try wp_auto',
                            'wp_apply wp_string_to_bytes go!"meta" as %smeta ⟨Hsmeta, -⟩', 'try wp_auto',
                            'wp_apply wp_string_to_bytes go!"lease" as %slease ⟨Hslease, -⟩', 'try wp_auto']
                           + ['wp_apply wp_string_to_bytes go!"alarm" as %salarm ⟨Hsalarm, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"cluster" as %scluster ⟨Hscluster, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"members" as %smembers ⟨Hsmembers, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"members_removed" as %smrem ⟨Hsmrem, -⟩',
                              'try wp_auto'] + [
                            'wp_apply wp_string_to_bytes go!"auth" as %sauth ⟨Hsauth, -⟩', 'try wp_auto',
                            'wp_apply wp_string_to_bytes go!"authUsers" as %sausers ⟨Hsausers, -⟩', 'try wp_auto',
                            'wp_apply wp_string_to_bytes go!"authRoles" as %saroles ⟨Hsaroles, -⟩', 'try wp_auto',
                            'wp_apply wp_string_to_bytes go!"test" as %_ ⟨-, -⟩', 'try wp_auto'],
        # the buckets (stepped by `wp_auto`), `AllBuckets`' slice literal, then the key names
        'MetaConfStateName': ['try wp_auto',
                              'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩',
                              'simp only [go.arrayLiteralSize, List.foldl]', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"scheduledCompactRev" as %ssc ⟨Hssc, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"finishedCompactRev" as %sfc ⟨Hsfc, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"consistent_index" as %sci ⟨Hsci, -⟩',
                              'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"authEnabled" as %sae ⟨Hsae, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"authRevision" as %sar ⟨Hsar, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"term" as %sterm ⟨Hsterm, -⟩', 'try wp_auto',
                              'wp_apply wp_string_to_bytes go!"confState" as %sconf ⟨Hsconf, -⟩', 'try wp_auto']
                             + [l for n in ['clusterVersion', 'downgrade', 'storageVersion', '']
                                for l in (f'wp_apply wp_string_to_bytes go!"{n}" as %_ ⟨-, -⟩', 'try wp_auto')],
        # (prove-initleft, 2026-11-21) `schemaChanges`, a map literal keyed by `version.V3_6`, `V3_7`,
        # `V3_8` (read-only by `version`'s fact; `semver.Version` a safe map key, `MapKey.lean`), whose
        # first value is a slice of one `addNewField(...)` (translated, its body stepped); until then
        # `opaqueInitsOk`
        'schemaChanges': [
            'try wp_auto',
            'ihave #Hvv : iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗',
            '    (∃ v : github_com.Masterminds.semver.v3.Version, globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗',
            '    globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0" ∗',
            '    (∃ v7 v8 : github_com.Masterminds.semver.v3.Version,',
            '      globalAddr go_etcd_io.etcd.api.v3.version.V3_7 ↦□ v7 ∗ globalAddr go_etcd_io.etcd.api.v3.version.V3_8 ↦□ v8)) $$ []',
            '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.api.v3.version}',
            'icases Hvv with ⟨-, ⟨%v36, #Hv36⟩, -, ⟨%v37, %v38, #Hv37, #Hv38⟩⟩',
            'try wp_auto',
            'wp_func_call', 'wp_call', 'try wp_auto',
            'wp_apply (wp_map_make1 (K := github_com.Masterminds.semver.v3.Version) (V := GoSlice) '
            'github_com.Masterminds.semver.v3.Version.ty (go.GoType.SliceType schemaChange.ty)) as %msc Hmsc'] +
            ['try wp_auto',
             'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩',
             'try wp_auto',
             'wp_apply (wp_mapInsert (K := github_com.Masterminds.semver.v3.Version) (V := GoSlice) '
             'github_com.Masterminds.semver.v3.Version.ty) $$ Hmsc as Hmsc'] * 3 + ['try wp_auto'],
    },
    finish=['ipersist Hskey', 'ipersist Hsmeta', 'ipersist Hsci', 'ipersist Hsterm',
            'ipersist Hsen', 'ipersist Hsdis', 'ipersist Hsauth', 'ipersist Hsausers', 'ipersist Hsaroles',
            'ipersist Hsae', 'ipersist Hsar',
            'ipersist HKey', 'ipersist HMeta', 'ipersist HMetaConsistentIndexKeyName',
            'ipersist HMembers', 'ipersist HMetaTermKeyName', 'ipersist HMetaConfStateName', 'ipersist Hsconf', 'ipersist HAuth', 'ipersist HAuthUsers', 'ipersist HAuthRoles',
            'ipersist HAuthEnabledKeyName', 'ipersist HAuthRevisionKeyName', 'ipersist HauthEnabled',
            'ipersist HauthDisabled', 'ipersist Hslease', 'ipersist HLease',
            # (prove-ps2-members, 2026-11-22) the membership's three buckets
            'ipersist Hscluster', 'ipersist Hsmembers', 'ipersist Hsmrem', 'ipersist HMembersRemoved',
            'ipersist HCluster',
            # (prove-ps2-v3alarm, 2026-11-24) the alarm store's bucket
            'ipersist Hsalarm', 'ipersist HAlarm'] + FIN_PRE[:6] + ['imodintro',
            'unfold schemaInit bucketIs metaName ciKeyBytes termKeyBytes keyName authName authUsersName authRolesName leaseName',
            'iframe #', 'repeat (first | (isplitl []; · (ipureintro; rfl)) | (ipureintro; rfl))'],
)

def counter_inc(x, file='metrics.go'):
    return dict(doc=f'/-- `{x} = prometheus.NewCounter(...)` (`{file}`): a `Counter`, whose `Inc` returns. -/',
                post=f'∃ c : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok c ∗ counterSpec c',
                pat='⟨%c@, H@, #S@⟩')

SPECIAL['go_etcd_io.etcd.server.v3.lease'] = dict(
    doc='''Its fact (`leaseInit`, `Base.lean`): the error variables `ErrNotPrimary`,
`ErrLeaseNotFound`, `ErrLeaseExists`, `ErrLeaseTTLTooLarge` (translated `errors.New` calls: leaf pointer errors
without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose `Error()` returns), `forever` (the zero
`time.Time`), the counters `leaseGranted`, `leaseRevoked`, `leaseRenewed` and the histogram `leaseTotalTTLs`
(`metrics.go`, translated: over prometheus's constructor specs; until 2026-11-19 the trust-boundary
axioms `<X>_init`); `opaqueInitsOk` states the
other untranslated initializers run.''',
    imports=['Proof.errors.NewVarCell', 'Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar'] + PROM_CTORS,
    alloc_types={'leaseGranted': 'GoInterface', 'leaseRevoked': 'GoInterface', 'leaseRenewed': 'GoInterface',
                 'leaseTotalTTLs': 'GoInterface',
                 'ErrNotPrimary': 'GoInterface',
                 'ErrLeaseTTLTooLarge': 'GoInterface', 'ErrLeaseExists': 'GoInterface',
                 'ErrLeaseNotFound': 'GoInterface', 'forever': '_root_.Perennial.time.Time'},
    before={'leaseGranted': [
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xNP ⟨-, #MNP⟩',
        'wp_apply EtcdGrove.wp_New_errorString_cell as %xNF ⟨#MNF, #CNF⟩',
        'wp_apply EtcdGrove.wp_New_errorString_cell as %xEx ⟨#MEx, #CEx⟩',
        'wp_apply EtcdGrove.wp_New_errorString_cell as %xTL ⟨#MTL, #CTL⟩'] +
        metric_steps_to('leaseGranted', 'counter', 'go_etcd_io.etcd.server.v3.lease.counterSpec'),
        'leaseRevoked': metric_steps_to('leaseRevoked', 'counter', 'go_etcd_io.etcd.server.v3.lease.counterSpec'),
        # (prove-ps2-renew, 2026-11-21) `Renew`'s `leaseRenewed.Inc()`
        'leaseRenewed': metric_steps_to('leaseRenewed', 'counter', 'go_etcd_io.etcd.server.v3.lease.counterSpec'),
        'leaseTotalTTLs': metric_steps_to('leaseTotalTTLs', 'hist', 'go_etcd_io.etcd.server.v3.storage.backend.histSpec')},
    finish=['ipersist HErrNotPrimary', 'ipersist HErrLeaseNotFound', 'ipersist HErrLeaseExists', 'ipersist HErrLeaseTTLTooLarge',
            'ipersist Hforever', 'ipersist HleaseGranted', 'ipersist HleaseRevoked', 'ipersist HleaseRenewed',
            # (prove-ps2-newlessor3, 2026-11-21) `leaseConsts`, what `newLessor` and the expiry loop read
            'ipersist HdefaultLeaseRevokeRate', 'ipersist HleaseCheckpointRate', 'ipersist HmaxLeaseCheckpointBatchSize',
            'ipersist HdefaultLeaseCheckpointInterval', 'ipersist HdefaultExpiredleaseRetryInterval',
            'ipersist HleaseTotalTTLs',
            'ihave #TNP := EtcdGrove.errorMsg_triple _ _ _ $$ MNP',
            'ihave #TNF := EtcdGrove.errorMsg_triple _ _ _ $$ MNF',
            'ihave #TEx := EtcdGrove.errorMsg_triple _ _ _ $$ MEx',
            'ihave #TTL := EtcdGrove.errorMsg_triple _ _ _ $$ MTL',
            'ihave #VNF : (EtcdGrove.errVarCell ErrLeaseNotFound go!"lease not found" : IProp GF) $$ []',
            '· unfold EtcdGrove.errVarCell; iexists _; iframe HErrLeaseNotFound CNF',
            # (lease-grant amendment (E), 2026-11-03) the grant's errors' cells, for `ErrNoSpace`'s apartness
            'ihave #VEx : (EtcdGrove.errVarCell ErrLeaseExists go!"lease already exists" : IProp GF) $$ []',
            '· unfold EtcdGrove.errVarCell; iexists _; iframe HErrLeaseExists CEx',
            'ihave #VTL : (EtcdGrove.errVarCell ErrLeaseTTLTooLarge go!"too large lease TTL" : IProp GF) $$ []',
            '· unfold EtcdGrove.errVarCell; iexists _; iframe HErrLeaseTTLTooLarge CTL',
            # (prove-ps2-newlessor3, 2026-11-21) the rates and intervals
            'ihave #HlC : (leaseConsts : IProp GF) $$ []',
            '· unfold leaseConsts; iframe HdefaultLeaseRevokeRate HleaseCheckpointRate HmaxLeaseCheckpointBatchSize',
            '  isplitr; · iexists _; iexact HdefaultLeaseCheckpointInterval',
            '  iexists _; iexact HdefaultExpiredleaseRetryInterval'] + FIN_PRE[:6] + [
            'imodintro', 'unfold leaseInit leaseErrVar', 'iframe #', 'dsimp only', 'iframe #',
            'repeat (first | (isplitl []; · (ipureintro; first | exact EtcdGrove.errorString_errLeaf _ | exact EtcdGrove.errorString_leaf _)) | (ipureintro; first | exact EtcdGrove.errorString_errLeaf _ | exact EtcdGrove.errorString_leaf _))'],
)

SPECIAL['go_etcd_io.etcd.pkg.v3.wait'] = dict(
    doc='''Its fact (`closecClosed`, `etcdserver/apply/Base.lean`; D19r (D), 2026-10-18: `True` until
then): `closec` holds a channel closed for good, an invariant keeping it `Closed []`. Its
initializer allocates `closec`, initializes its imports and runs its translated `init()`
(`wait_time.go`: `closec = make(chan struct{}); close(closec)`).''',
    alloc_types={'closec': 'GoChan'},
    before={'$end': [
        'wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩',
        'wp_apply_core chan.wp_close (V := Unit) ch γ $$ His_ch',
        'iintro -', 'unfold closeAu', 'iapply ncfupd_of_fupd', 'iapply fupd_mask_intro Std.LawfulSet.empty_subset',
        'iintro Hmask', 'inext', 'iexists .Idle', 'iframe Hch', 'dsimp only', 'iintro Hch',
        'imod Hmask with -', 'imodintro', 'wp_auto']},
    finish=['ipersist Hclosec',
            'imod (inv_alloc _root_.Perennial.context.closedchanN ⊤ (ownChan γ Unit (.Closed []))) $$ [Hch] with #Hinv',
            '· inext; iexact Hch',
            'ihave #Hfact : (closecClosed : IProp GF) $$ []',
            '· unfold closecClosed; iexists ch, γ; iframe #',
            'imodintro', 'iframe Hown', 'is_pkg_init_finish'],
)

CV3 = 'go_etcd_io.etcd.cache.v3'
SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes'] = dict(
    doc='''Its fact (`rpctypesInit`, `cache/v3/Base.lean`): the errors `ErrFutureRev`, `ErrCompacted`
(`EtcdError`s, whose `Error()` returns), the map `errStringToError` (its values `status.Error`
errors grpc's `status` accepts), `EtcdError`'s method set (`EtcdGrove.RpctypesEtcdErrorMethods`, of
the method set goose emits), the `EtcdError`s `ErrUserEmpty`, `ErrInvalidAuthToken`,
`ErrAuthOldRevision`, `ErrNoLeader`, `ErrAuthNotEnabled` and the pointer error `ErrGRPCNotSupportedForLearner`. Its variables'
initializers (`error.go`, `metadatafields.go`) are untranslated: the trust-boundary axioms
`<X>_init` state the ones the fact reads, `opaqueInitsOk` the others.''',
    pre=['/-- **The method set of `rpctypes.EtcdError`** is `{Code, Error}` (`error.go`): no `As`,',
         '`Unwrap`, `GRPCStatus` or `Is` method: a theorem of the method set goose emits',
         '(`EtcdError.TypeAssumptions.method_set`), as `EtcdGrove.ErrorStringLeaf`. -/',
         'class EtcdGrove.RpctypesEtcdErrorMethods [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where',
         '  leaf : ∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩',
         '  noGRPCStatus : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none',
         '  noIs : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none',
         '  /-- (premise-fixes-4) nor a `Format` method (`fmt` prints it with its `Error`). -/',
         '  noFormat : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Format" = none',
         '  /-- (fmt soundness 2) and its `Error` is `Error() string` (what `fmt.argOk` asks). -/',
         '  errorSig : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Error" =',
         '    some (go.signature.Signature [] false [go.string])',
         '',
         'instance EtcdGrove.rpctypesEtcdErrorMethods_inst [GooseExts] [GoGlobalContext] [GoLocalContext]',
         '    [GoSemanticsFunctions] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :',
         '    EtcdGrove.RpctypesEtcdErrorMethods := by',
         '  have h := fun m => go.method_set_is (t := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) m',
         '  have hAs := h go!"As"; have hU := h go!"Unwrap"; have hG := h go!"GRPCStatus"; have hIs := h go!"Is"',
         '  have hF := h go!"Format"; have hE := h go!"Error"',
         '  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hAs hU hG hIs hF hE',
         '  exact ⟨fun _ => by simp [errors.isLeafError, hAs, hU], hG, hIs, hF, hE⟩',
         '',
         '/-- `rpctypes.EtcdError` implements `error` (its `Error` has a value receiver): a target',
         '`errors.As` accepts. -/',
         'theorem EtcdGrove.rpctypesEtcdError_asTarget [GooseExts] [GoGlobalContext] [GoLocalContext]',
         '    [sem : go.Semantics] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :',
         '    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty :=',
         '  Or.inr (by go_type_set)',
         ''],
    imports=['Perennial.Golang.Theory.TypeSet'],
    custom={
        'ErrFutureRev': dict(doc='/-- `ErrFutureRev = Error(ErrGRPCFutureRev)` (`error.go`): an `EtcdError`, whose `Error()` returns its description, `ErrGRPCFutureRev`\'s (k8s etcd3 7c), with no `Format` method (an `EtcdError`\'s method set is `{Code, Error}`: `fmt` prints it through `Error()`; premise-fixes-4), an `EtcdError` value (k8s etcd3 7e-2, D1: stated, checked by `examples/k8s7e2attack`\'s `TestRpctypesErrTypes` at the etcd pin). -/',
                             post=f'∃ e : GoInterfaceOk, globalAddr ErrFutureRev ↦ GoInterface.ok e ∗ {CV3}.errorStringSpec e ∗ {CV3}.descIs (GoInterface.ok e) {CV3}.futureRevDesc ∗ ⌜methodSet e.ty !! go!"Format" = none⌝ ∗ ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝',
                             pat='⟨%e@, H@, #S@, #D@, %F@, %T@⟩'),
        'ErrCompacted': dict(doc='/-- `ErrCompacted = Error(ErrGRPCCompacted)` (`error.go`): an `EtcdError`, whose `Error()` returns its description, `ErrGRPCCompacted`\'s (k8s etcd3 7c), with no `Format` method (an `EtcdError`\'s method set is `{Code, Error}`: `fmt` prints it through `Error()`; premise-fixes-4), an `EtcdError` value (k8s etcd3 7e-2, D1: stated, checked by `examples/k8s7e2attack`\'s `TestRpctypesErrTypes` at the etcd pin). -/',
                             post=f'∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦ GoInterface.ok e ∗ {CV3}.errorStringSpec e ∗ {CV3}.descIs (GoInterface.ok e) {CV3}.compactedDesc ∗ ⌜methodSet e.ty !! go!"Format" = none⌝ ∗ ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝',
                             pat='⟨%e@, H@, #S@, #D@, %F@, %T@⟩'),
        # (k8s etcd3 7c) the server-side read errors `togRPCError` maps mvcc's to
        'ErrGRPCFutureRev': dict(doc='/-- `ErrGRPCFutureRev = status.Error(codes.OutOfRange, "etcdserver: mvcc: required revision is a future revision")` (`error.go`): with that description (k8s etcd3 7c). -/',
                             post=f'∃ e : GoInterfaceOk, globalAddr ErrGRPCFutureRev ↦ GoInterface.ok e ∗ {CV3}.descIs (GoInterface.ok e) {CV3}.futureRevDesc',
                             pat='⟨%e@, H@, #D@⟩'),
        'ErrGRPCCompacted': dict(doc='/-- `ErrGRPCCompacted = status.Error(codes.OutOfRange, "etcdserver: mvcc: required revision has been compacted")` (`error.go`): with that description (k8s etcd3 7c). -/',
                             post=f'∃ e : GoInterfaceOk, globalAddr ErrGRPCCompacted ↦ GoInterface.ok e ∗ {CV3}.descIs (GoInterface.ok e) {CV3}.compactedDesc',
                             pat='⟨%e@, H@, %D@⟩'),
        'errStringToError': dict(doc='/-- `errStringToError = map[string]error{...}` (`error.go`): a map whose values are `ErrGRPC*` errors, `status.Error(...)`s: `*status.Error`s, leaf errors whose `Error()`, `GRPCStatus()` and `Is` return. -/',
                                 post=f'∃ (mref : Loc) (m : GMap GoString GoInterface), globalAddr errStringToError ↦ mref ∗ mref ↦$□ m ∗ □ (∀ (k : GoString) (v : GoInterface), ⌜m !! k = some v⌝ → {CV3}.statusErrOk v) ∗ □ (∀ (k : GoString) (v : GoInterface), ⌜m !! k = some v⌝ → {CV3}.descIs v k)',
                                 pat='⟨%mref@, %m@, H@, #M@, #S@, #D@⟩'),
        'ErrUserEmpty': dict(doc='/-- `ErrUserEmpty = Error(ErrGRPCUserEmpty)` (`error.go`): an `EtcdError`, with `ErrGRPCUserEmpty`\'s description (D29). -/',
                             post='∃ x : EtcdError, globalAddr ErrUserEmpty ↦ interface.mkOk EtcdError.ty #x ∗ ⌜x.desc\' = go!"etcdserver: user name is empty"⌝',
                             pat='⟨%x@, H@, %D@⟩'),
        'ErrInvalidAuthToken': dict(doc='/-- `ErrInvalidAuthToken = Error(ErrGRPCInvalidAuthToken)` (`error.go`): an `EtcdError`, with `ErrGRPCInvalidAuthToken`\'s description (D29). -/',
                             post='∃ x : EtcdError, globalAddr ErrInvalidAuthToken ↦ interface.mkOk EtcdError.ty #x ∗ ⌜x.desc\' = go!"etcdserver: invalid auth token"⌝',
                             pat='⟨%x@, H@, %D@⟩'),
        'ErrAuthOldRevision': dict(doc='/-- `ErrAuthOldRevision = Error(ErrGRPCAuthOldRevision)` (`error.go`): an `EtcdError`, with `ErrGRPCAuthOldRevision`\'s description (D29). -/',
                             post='∃ x : EtcdError, globalAddr ErrAuthOldRevision ↦ interface.mkOk EtcdError.ty #x ∗ ⌜x.desc\' = go!"etcdserver: revision of auth store is old"⌝',
                             pat='⟨%x@, H@, %D@⟩'),
        'ErrGRPCNotSupportedForLearner': dict(doc='/-- `ErrGRPCNotSupportedForLearner = status.Error(codes.FailedPrecondition, "etcdserver: rpc not supported for learner")` (`error.go`): a `*status.Error`, a pointer error, with that description (D29), which grpc\'s `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6). -/',
                             post=f'∃ e : GoInterfaceOk, globalAddr ErrGRPCNotSupportedForLearner ↦ GoInterface.ok e ∗ ⌜errors.IsPointerError e⌝ ∗ {CV3}.descIs (GoInterface.ok e) go!"etcdserver: rpc not supported for learner" ∗ {CV3}.statusErrOk (GoInterface.ok e)',
                             pat='⟨%e@, H@, %P@, #D@, #S@⟩'),
        # (item 1, the client lease, 2026-10-18: the lessor's keep-alive loop compares a stream's
        # error with it, `errors.Is`)
        'ErrNoLeader': dict(doc='/-- `ErrNoLeader = Error(ErrGRPCNoLeader)` (`error.go`): an `EtcdError`. -/',
                             post='∃ x : EtcdError, globalAddr ErrNoLeader ↦ interface.mkOk EtcdError.ty #x',
                             pat='⟨%x@, H@⟩'),
        # (the auth plan's C1, 2026-10-28: the client's `getToken` compares `Authenticate`'s error
        # with it, `errors.Is`)
        'ErrAuthNotEnabled': dict(doc='/-- `ErrAuthNotEnabled = Error(ErrGRPCAuthNotEnabled)` (`error.go`): an `EtcdError`. -/',
                             post='∃ x : EtcdError, globalAddr ErrAuthNotEnabled ↦ interface.mkOk EtcdError.ty #x',
                             pat='⟨%x@, H@⟩'),
    },
    finish=['ipersist HErrFutureRev', 'ipersist HErrCompacted', 'ipersist HErrGRPCFutureRev',
            'ipersist HErrGRPCCompacted', 'ipersist HerrStringToError',
            'ipersist HErrUserEmpty', 'ipersist HErrInvalidAuthToken', 'ipersist HErrAuthOldRevision',
            'ipersist HErrGRPCNotSupportedForLearner', 'ipersist HErrNoLeader', 'ipersist HErrAuthNotEnabled',
            'ihave #HFRS : iprop(□ ∀ e : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok e -∗',
            '    go_etcd_io.etcd.cache.v3.errorStringSpec e) $$ []',
            '· iintro !> %e He',
            '  icombine HErrFutureRev He gives %Heq',
            '  cases Heq',
            '  iexact SErrFutureRev'] + FIN_PRE[:6] + [
            'imodintro', 'unfold go_etcd_io.etcd.cache.v3.rpctypesInit', 'iframe #',
            'ipureintro',
            'repeat\' (first',
            '  | assumption',
            '  | exact ⟨EtcdGrove.RpctypesEtcdErrorMethods.leaf, EtcdGrove.RpctypesEtcdErrorMethods.noGRPCStatus, EtcdGrove.RpctypesEtcdErrorMethods.noIs, EtcdGrove.RpctypesEtcdErrorMethods.noFormat, EtcdGrove.RpctypesEtcdErrorMethods.errorSig⟩',
            '  | constructor)'],
)

SPECIAL['go_etcd_io.etcd.client.v3'] = dict(
    doc='''Its fact (`clientv3Init`, `cache/v3/Base.lean`): `noPrefixEnd` (`op.go`, translated:
`[]byte{0}`) and `defaultOptions` (`retry_interceptor.go`, translated since 2026-11-22: `&options{...}`
whose backoff function, `backoffLinearWithJitter`'s, returns; until then the trust-boundary axiom
`defaultOptions_init`), and its translated
`valCtxCh`, `zeroTime` (`time.Unix(0, 0)`, `time.Unix.wp_proof`: proved over Perennial's translation since
2026-11-20, until then a trust-boundary axiom) and
`maxBackoff`, and `LeaseResponseChSize` (`lease.go`, translated: `16`; until 2026-11-19 the
trust-boundary axiom `LeaseResponseChSize_init`), and the translated constants
`defaultUnaryMaxRetries`, `defaultStreamMaxRetries` and `defaultBackoffWaitBetween`
(`options.go`). (prove-smallinits, 2026-11-20) Its other variables' initializers are translated
too: the three `errors.New` errors, the call options (grpc's `WaitForReady`, `MaxCallSendMsgSize`,
`MaxCallRecvMsgSize`), `defaultCallOpts` (their slice) and `defaultBackoffJitterFraction` (until then
`opaqueInitsOk` and the trust-boundary axioms `defaultCallOpts_init`,
`defaultBackoffJitterFraction_init`).''',
    imports=['Proof.time.Unix', 'Proof.math.rand.Float64', 'Proof.go_etcd_io.etcd.client.v3.jitterUp',
             'Proof.go_etcd_io.etcd.client.v3.backoffLinearWithJitter'],
    alloc_types={'maxBackoff': 'w64', 'defaultOptions': 'Loc', 'zeroTime': '_root_.Perennial.time.Time', 'valCtxCh': 'GoChan',
                 'noPrefixEnd': 'GoSlice', 'LeaseResponseChSize': 'w64', 'defaultUnaryMaxRetries': 'w64', 'defaultStreamMaxRetries': 'w64',
                 'defaultBackoffWaitBetween': 'w64'},
    before={'defaultWaitForReady': [
        'wp_apply wp_slice_literal (l := [W8 0])', 'isplitr', '· ipureintro; rfl',
        'iintro %snp ⟨Hsnp, -⟩', 'try wp_auto'],
        '$inits': ['wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩',
                   'wp_apply EtcdGrove.time.Unix.wp_proof as %zt -']},
    finish=['ipersist Hsnp', 'ipersist HnoPrefixEnd', 'ipersist HdefaultOptions'] + FIN_PRE[:6] + [
            'imodintro', 'unfold go_etcd_io.etcd.cache.v3.clientv3Init', 'iframe #'],
)

# (the auth plan's E2c, 2026-10-25) the strings themselves: `AuthInfoFromCtx`'s token is the
# context's metadata under these keys; (const-inits, 2026-11-19) translated, as the metadata keys
SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes'].setdefault('alloc_types', {}).update(
    {x: 'GoString' for x in ['TokenFieldNameGRPC', 'TokenFieldNameSwagger', 'MetadataRequireLeaderKey',
                             'MetadataHasLeader', 'MetadataClientAPIVersionKey']})
SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes']['finish'] = (
    ['ipersist HTokenFieldNameGRPC', 'ipersist HTokenFieldNameSwagger'] +
    SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes']['finish'])

def _cacheErrVar(x, tag, msg):
    """`cacheInit`'s `errorStringSpec` of the `errors.New(msg)` error variable `x` (`#M<tag>`)."""
    return ['isplitr',
            '· iintro !> %e #He',
            f'  icombine H{x} He gives %Heq',
            '  simp only [interface.mkOk, GoInterface.ok.injEq] at Heq',
            '  subst Heq',
            f'  iapply (errorStringSpec_of_msg _ go!"{msg}")',
            f'  iexact M{tag}']

SPECIAL['go_etcd_io.etcd.cache.v3'] = dict(
    doc='''Its fact (`cacheInit`, `Base.lean`; 2026-10-20, cachekv): the error variables `ErrUnsupportedRequest`,
`ErrKeyRangeInvalid`, `ErrCacheTimeout` (translated `errors.New` calls, whose `Error()` returns
their message) and `ErrNotReady` (a translated `fmt.Errorf` call), each a fixed non-nil error,
the first two with `errorStringSpec`. Its initializer allocates them, initializes its imports and
runs their translated initializers.''',
    imports=['Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar', 'Proof.fmt.Link'],
    vars=['[_root_.Perennial.fmt.Assumptions]'],
    alloc_types={'ErrUnsupportedRequest': 'GoInterface', 'ErrKeyRangeInvalid': 'GoInterface',
                 'ErrCacheTimeout': 'GoInterface', 'ErrNotReady': 'GoInterface'},
    before={'$end': [
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xUR ⟨-, #MUR⟩',
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xKR ⟨-, #MKR⟩',
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xCT ⟨-, #MCT⟩',
        'wp_apply (EtcdGrove.fmt.wp_Errorf go!"cache: store not ready" slice.nil [] (DFrac.own 1))',
        '    $$ [] as %eNR -',
        '· isplitl',
        '  · iapply ownSlice_nil',
        '  fmt_args_intro; itrivial']},
    finish=['ipersist HErrUnsupportedRequest', 'ipersist HErrKeyRangeInvalid',
            'ipersist HErrCacheTimeout', 'ipersist HErrNotReady'] + FIN_PRE[:6] + [
            'imodintro', 'unfold cacheInit',
            'isplitr; · iexists _; iexact HErrNotReady',
            'isplitr; · iexists _; iexact HErrUnsupportedRequest',
            'isplitr; · iexists _; iexact HErrKeyRangeInvalid',
            'isplitr; · iexists _; iexact HErrCacheTimeout'] +
           _cacheErrVar('ErrKeyRangeInvalid', 'KR', 'cache: invalid or out‑of‑range key range')[0:1] +
           _cacheErrVar('ErrKeyRangeInvalid', 'KR', 'cache: invalid or out‑of‑range key range')[1:] +
           ['iintro !> %e #He', 'icombine HErrUnsupportedRequest He gives %Heq',
            'simp only [interface.mkOk, GoInterface.ok.injEq] at Heq', 'subst Heq',
            # (premise-fixes-4) and its type has no `Format` method (`fmt.argOk`)
            'isplitr',
            '· iapply (errorStringSpec_of_msg _ go!"cache: unsupported request parameters")',
            '  iexact MUR',
            '· ipureintro; fmt_method_facts'],
)

_AUTH_ERRS = ['ErrRootUserNotExist', 'ErrRootRoleNotExist', 'ErrUserAlreadyExist', 'ErrUserEmpty',
              'ErrUserNotFound', 'ErrRoleAlreadyExist', 'ErrRoleNotFound', 'ErrRoleEmpty',
              'ErrPermissionNotGiven', 'ErrAuthFailed', 'ErrNoPasswordUser', 'ErrPermissionDenied',
              'ErrRoleNotGranted', 'ErrPermissionNotGranted', 'ErrAuthNotEnabled', 'ErrAuthOldRevision',
              'ErrInvalidAuthToken', 'ErrInvalidAuthOpts', 'ErrInvalidAuthMgmt']
def _auth_news(names):
    # with the message cells (the auth plan's E3i, 2026-10-27: `authErrMsgs`, what tells them apart
    # from `etcdserver/errors.ErrNoSpace`)
    return [f'wp_apply EtcdGrove.wp_New_errorString_cell as %x{n} ⟨#M{n}, #C{n}⟩' for n in names]
SPECIAL['go_etcd_io.etcd.server.v3.auth'] = dict(
    doc='''Its fact (`authInit`, `Base.lean`): its error variables `ErrUserEmpty`, `ErrUserNotFound`,
`ErrPermissionDenied`, `ErrAuthOldRevision`, `ErrInvalidAuthToken`, and the admin side's eleven
(the auth plan's S4, 2026-10-24: `ErrRootUserNotExist`, ..., `ErrInvalidAuthMgmt`), and S5's two
(`ErrAuthFailed`, `ErrAuthNotEnabled`), and E2g's `ErrInvalidAuthOpts` (translated
`errors.New` calls: leaf pointer errors without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose
`Error()` returns), and `rpctypes`' token keys (from `rpctypes`' fact). (prove-initmisc,
2026-11-20) Its other variables' initializers are translated too: `currentAuthRevision`
(`prometheus.NewGaugeFunc`, over its spec), `knownOptions` (a map literal), `DefaultTTL`, `_` (`var _
AuthStore = (*authStore)(nil)`), `rootPerm` (an `authpb.Permission` literal) and the JWT errors
(until then the trust-boundary axiom `opaqueInitsOk`).''',
    imports=['Proof.errors.NewVar', 'Proof.errors.NewVarCell', 'Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar',
             'Perennial.Proof.sync.RWMutexGuard', 'Proof.github_com.prometheus.client_golang.prometheus.NewGaugeFunc'],
    alloc_types={**{x: 'GoInterface' for x in reversed(_AUTH_ERRS)},
                 # the simple provider's TTL default (the auth plan's S5b, 2026-10-24), a `time.Duration`
                 'simpleTokenTTLDefault': 'w64',
                 # the keeper's tick (S5c, 2026-10-25), a `time.Duration`
                 'simpleTokenTTLResolution': 'w64',
                 # the metrics reporter and its lock (the auth plan's E2a, 2026-10-25)
                 'reportCurrentAuthRevMu': '_root_.Perennial.sync.RWMutex',
                 'reportCurrentAuthRev': 'GoFunc',
                 # (prove-initmisc, 2026-11-20) the package's other variables, translated (until
                 # then `opaqueInitsOk`)
                 'currentAuthRevision': 'GoInterface', 'knownOptions': 'Loc', 'DefaultTTL': 'w64',
                 'rootPerm': 'go_etcd_io.etcd.api.v3.authpb.Permission',
                 **{x: 'GoInterface' for x in ['ErrInvalidAuthMethod', 'ErrMissingKey', 'ErrKeyMismatch',
                                               'ErrVerifyOnly']}},
    before={
        'currentAuthRevision': gaugefunc_steps('currentAuthRevision'),
        # `map[string]bool{optSignMethod: true, ...}`: made, then its four entries inserted
        'knownOptions': ['try wp_auto',
            'wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %mko Hko',
            'try wp_auto'] + ['wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hko as Hko',
                              'try wp_auto'] * 4,
        # `authpb.Permission{PermType: READWRITE, Key: []byte{}, RangeEnd: []byte{0}}`
        'rootPerm': ['try wp_auto'] + [l for i in range(2) for l in [
            f'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %srp{i} ⟨Srp{i}, -⟩',
            'try wp_auto']],
        # the recipes run before the first JWT error's initializer, consuming the translated
        # `errors.New` calls that precede it in `store.go`'s order, then the JWT errors' own
        'ErrInvalidAuthMethod': _auth_news(_AUTH_ERRS) +
            ['wp_apply _root_.Perennial.errors.wp_New_errorString as %_ -', 'try wp_auto'] * 4,
    },
    finish=[f'ipersist H{n}' for n in _AUTH_ERRS] + ['ipersist HsimpleTokenTTLResolution'] +
           [f'ihave #T{n} := EtcdGrove.errorMsg_triple _ _ _ $$ M{n}' for n in _AUTH_ERRS] + [
            # the message cells (E3i): `errVarCells authErrMsgs`
            'ihave #VCells : (EtcdGrove.errVarCells go_etcd_io.etcd.server.v3.auth.authErrMsgs : IProp GF) $$ []',
            '· unfold go_etcd_io.etcd.server.v3.auth.authErrMsgs',
            '  simp only [EtcdGrove.errVarCells, EtcdGrove.errVarCell]',
            '  iframe #',
            '  repeat (first | (isplitl []; · (iexists _; iframe #)) | (iexists _; iframe #))',
            '  try itrivial'] + [
            'ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []',
            '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.api.v3.v3rpc.rpctypes}',
            'icases Hri with ⟨-, -, -, -, -, -, -, -, -, #HTG, #HTS, -⟩',
            # the metrics reporter's lock over the reporter (E2a)
            'imod (sync.init_RWMutex go_etcd_io.etcd.server.v3.auth.reportP (globalAddr reportCurrentAuthRevMu) (E := ⊤)) $$ [HreportCurrentAuthRev] HreportCurrentAuthRevMu with HRP',
            '· inext',
            '  unfold go_etcd_io.etcd.server.v3.auth.reportP',
            '  iexists _; iframe HreportCurrentAuthRev',
            'ihave ⟨-, #GRP⟩ := sync.ownRWMutex_slots_guard _ _ $$ HRP'] + FIN_PRE[:6] + [
            'imodintro', 'unfold authInit authErrVar', 'iframe #', 'dsimp only', 'iframe #',
            'repeat (first | (isplitl []; · (ipureintro; first | exact EtcdGrove.errorString_errLeaf _ | exact EtcdGrove.errorString_leaf _)) | (ipureintro; first | exact EtcdGrove.errorString_errLeaf _ | exact EtcdGrove.errorString_leaf _))',
            # the keeper's tick (S5e): `1 * time.Second`, read-only; then E2g's error variable
            'all_goals first | (ipureintro; decide) | (ipureintro; exact EtcdGrove.errorString_errLeaf _) | (ipureintro; exact EtcdGrove.errorString_leaf _) | (ipureintro; exact ⟨by decide, EtcdGrove.errorString_errLeaf _⟩) | (ipureintro; exact ⟨by decide, EtcdGrove.errorString_leaf _⟩)'],
)

# Item 8, step 3 (2026-10-17): facts moved into their owners' packages.
_E = SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.errors']
_E['doc'] = """Its fact (`errorsInit`, `errors/Base.lean`): `ErrNoSpace` holds a pointer error, and every
error variable its `errors.New` error (`errorsNewVars errorsMsgs`). Its initializer allocates its
variables and runs their translated initializers, `errors.New` calls (`errors.go`; with their
message cells, `EtcdGrove.wp_New_errorString_cell`; until 2026-11-19 the trust-boundary axiom
`errorsNewVarsInit`)."""
_E['finish'] = ([f'ipersist H{x}' for x in _ETCD_ERRMSGS] + FIN_PRE[:6] +
    ['try (isplitl []; · (imodintro; itrivial))', 'imodintro',
     'unfold errorsInit errorsMsgs',
     'simp only [EtcdGrove.errorsNewVars, EtcdGrove.errorsNewVar, EtcdGrove.errVarCells, EtcdGrove.errVarCell]',
     'iframe #', 'ipureintro', 'exact ⟨_, _, rfl, rfl⟩'])

_B = SPECIAL['go_etcd_io.etcd.server.v3.storage.backend']
# (prove-etcdint3, 2026-11-21) `boltOpenOptions` translated (`&bolt.Options{...}`, over project bboltfs's
# `syscall.MAP_POPULATE`): its allocation persisted, and `boltOpenOptionsOk` from it (until then the
# trust-boundary axiom `boltOpenOptions_init`)
_B['alloc_types']['boltOpenOptions'] = 'Loc'
_B['before']['boltOpenOptions'] = ['try wp_auto', 'irename : (_ ↦ (_ : _root_.Perennial.go_etcd_io.bbolt.Options) : IProp GF) => HpbOO']
_B['doc'] = _B['doc'].replace("hold `Histogram`s whose `Observe` returns.", "hold `Histogram`s whose `Observe` returns, and `boltOpenOptions` (`boltOpenOptionsOk`).")
# (2026-11-07, R10) the defaults `DefaultBackendConfig` loads (translated stores of constants)
_B['doc'] = _B['doc'].replace("and `boltOpenOptions` (`boltOpenOptionsOk`).", "and `boltOpenOptions` (`boltOpenOptionsOk`), and `defaultBatchInterval`,\n`defaultBatchLimit`, `InitialMmapSize` their translated initializers' constants.")
_B['finish'] = (['ipersist HcommitSec', 'ipersist HrebalanceSec', 'ipersist HspillSec', 'ipersist HwriteSec',
                 # (backend-snapshot B4, 2026-11-21) `Snapshot`'s goroutine observes it
                 'ipersist HsnapshotTransferSec',
                 # (backend-snapshot B4, 2026-11-21) the floor of `Snapshot`'s ticker interval
                 'ipersist HminSnapshotWarningTimeout',
                 'ipersist HboltOpenOptions', 'ipersist HpbOO', 'ipersist HdefaultBatchInterval',
                 'ipersist HdefaultBatchLimit', 'ipersist HInitialMmapSize',
                 'ihave #HbOO : (EtcdGrove.backend.boltOpenOptionsOk : IProp GF) $$ []', '· iapply EtcdGrove.backend.boltOpenOptionsOk_intro $$ HboltOpenOptions HpbOO', '  ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩'] + FIN_PRE[:6] +
                ['imodintro', 'unfold backendInit',
                 # `minSnapshotWarningTimeout`'s store: `30 * time.Second`, unevaluated
                 'rw [show (W64 30000000000 : w64) = W64 30 * W64 1000000000 from by decide]',
                 'iframe #',
                 # `defaultBatchInterval`'s store: `100 * time.Millisecond`, unevaluated
                 'rw [show (W64 100000000 : w64) = W64 100 * W64 1000000 from by decide]',
                 'iexact HdefaultBatchInterval'])

# (prove-protootel, 2026-11-20) otel `trace`'s `noopSpanInstance` translated (until then in its
# `opaqueInitsOk`), what `SpanFromContext` returns
SPECIAL['go_opentelemetry_io.otel.trace'] = dict(
    doc="""Its fact (`traceInit`, `storage/mvcc/Base.lean`): `noopSpanInstance` holds a `noopSpan` as a
`Span`, read-only for good. Its initializer allocates it, initializes its imports and runs its
translated initializer (`noopSpan{}` converted to `Span`, `noop.go`; prove-protootel, 2026-11-20:
until then in `opaqueInitsOk`), those of `tracerProviderInstance` and
`autoInstEnabled` (`new`) and of the `start`/`ended` func literals (prove-otel4, 2026-11-21), and the
untranslated initializers of its other variables (`maxSpan`, which goose's guard refuses, and the
`var _ I = T{}` assertions: `trace.toml`), which the trust-boundary axiom `opaqueInitsOk` says run
without panicking.""",
    alloc_types={'noopSpanInstance': 'GoInterface', 'tracerProviderInstance': 'Loc', 'start': 'GoFunc',
                 'ended': 'GoFunc', 'autoInstEnabled': 'Loc'},
    finish=['ipersist HnoopSpanInstance'] + FIN_PRE[:6] +
           ['imodintro', 'unfold traceInit', 'iexists _; iexact HnoopSpanInstance'],
)
# (otel-tracing, 2026-11-23) otel's no-op tracer package, what `traceutil.Tracer`'s initializer calls
SPECIAL['go_opentelemetry_io.otel.trace.noop'] = dict(
    doc="""Its fact (`noopInit`, `storage/mvcc/Base.lean`): `noopSpanInstance` holds a no-op `Span` as a
`trace.Span`, read-only for good. Its initializer allocates it, initializes its imports and runs its
translated initializers (`noopSpanInstance = Span{}` and the interface assertions `var _ I = T{}`,
`noop.go`).""",
    alloc_types={'noopSpanInstance': 'GoInterface'},
    finish=['ipersist HnoopSpanInstance'] + FIN_PRE[:6] +
           ['imodintro', 'unfold noopInit', 'iexists _; iexact HnoopSpanInstance'],
)
SPECIAL['go_etcd_io.etcd.pkg.v3.traceutil'] = dict(
    doc="""Its fact (`traceutilInit`, `storage/mvcc/Base.lean`): `Tracer` holds a fixed tracer. Its
initializer allocates `Tracer`, initializes its imports and runs its translated initializer,
`Tracer = noop.NewTracerProvider().Tracer(instrumentationScope)` (`trace.go`; otel-tracing,
2026-11-23: until then the trust-boundary axiom `Tracer_init`), stepping into otel's no-op
`NewTracerProvider` and `TracerProvider.Tracer` (translated with their bodies).""",
    alloc_types={'Tracer': 'GoInterface'},
    before={'Tracer': ['try wp_auto', 'wp_func_call', 'wp_auto', 'wp_method_call', 'wp_auto']},
    finish=['ipersist HTracer'] + FIN_PRE[:6] +
           ['imodintro', 'unfold traceutilInit', 'iexists _; iexact HTracer'],
)

_R = SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes']
_RERRS = ['ErrGRPCEmptyKey', 'ErrGRPCInvalidSortOption', 'ErrGRPCValueProvided', 'ErrGRPCLeaseProvided',
          'ErrGRPCTooManyOps', 'ErrGRPCDuplicateKey', 'ErrGRPCKeyNotFound', 'ErrGRPCNoSpace',
          'ErrGRPCNotCapable', 'ErrGRPCInvalidClientAPIVersion', 'ErrGRPCNoLeader']
_RKEYS = {'MetadataClientAPIVersionKey': 'client-api-version', 'MetadataRequireLeaderKey': 'hasleader',
          'MetadataHasLeader': 'true'}
# (k8s etcd3 7c, HS-1) with their descriptions: no one of them is a read error's (`handlerDescs`)
_RERRDESCS = {
           'ErrGRPCEmptyKey': ('InvalidArgument', 'etcdserver: key is not provided'),
           'ErrGRPCKeyNotFound': ('InvalidArgument', 'etcdserver: key not found'),
           'ErrGRPCValueProvided': ('InvalidArgument', 'etcdserver: value is provided'),
           'ErrGRPCLeaseProvided': ('InvalidArgument', 'etcdserver: lease is provided'),
           'ErrGRPCTooManyOps': ('InvalidArgument', 'etcdserver: too many operations in txn request'),
           'ErrGRPCDuplicateKey': ('InvalidArgument', 'etcdserver: duplicate key given in txn request'),
           'ErrGRPCInvalidClientAPIVersion': ('InvalidArgument', 'etcdserver: invalid client api version'),
           'ErrGRPCInvalidSortOption': ('InvalidArgument', 'etcdserver: invalid sort option'),
           'ErrGRPCNoSpace': ('ResourceExhausted', 'etcdserver: mvcc: database space exceeded'),
           'ErrGRPCNoLeader': ('Unavailable', 'etcdserver: no leader'),
           'ErrGRPCNotCapable': ('FailedPrecondition', 'etcdserver: not capable')}
for x in _RERRS:
    c, m = _RERRDESCS[x]
    _R['custom'][x] = dict(doc=f'/-- `{x} = status.Error(codes.{c}, "{m}")` (`error.go`): a `*status.Error`, which grpc\'s `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6), with that description (k8s etcd3 7c). -/',
                           post=f'∃ e : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok e ∗ {CV3}.statusErrOk (GoInterface.ok e) ∗ {CV3}.descIs (GoInterface.ok e) go!"{m}"',
                           pat='⟨%e@, H@, #S@, #D@⟩')
# (D19j, 2026-10-18) the `ErrGRPC*` errors `v3rpc`'s watch server returns or reports: `status.Error`
# values whose `Error()` returns
_RWERRS = {'ErrGRPCInvalidAuthToken': ('Unauthenticated', 'etcdserver: invalid auth token'),
           'ErrGRPCAuthOldRevision': ('InvalidArgument', 'etcdserver: revision of auth store is old'),
           'ErrGRPCUserEmpty': ('InvalidArgument', 'etcdserver: user name is empty'),
           'ErrGRPCPermissionDenied': ('PermissionDenied', 'etcdserver: permission denied'),
           'ErrGRPCWatchCanceled': ('Canceled', 'etcdserver: watch canceled')}
for x, (c, m) in _RWERRS.items():
    if x == 'ErrGRPCWatchCanceled':
        # (premise-fixes-7, Q1) the watch server returns it from `Watch`, a stream handler's
        # error, which grpc and the prometheus interceptor pass to `status.FromError`
        _R['custom'][x] = dict(
            doc=f'/-- `{x} = status.Error(codes.{c}, "{m}")` (`error.go`): a `*status.Error`, whose `Error()` returns, which grpc\'s `status.FromError` accepts (`statusErrOk`; premise-fixes-7: `watchServer.Watch` returns it). -/',
            post=f'∃ e : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok e ∗ {CV3}.errorStringSpec e ∗ {CV3}.statusErrOk (GoInterface.ok e)',
            pat='⟨%e@, H@, #S@, #T@⟩')
        continue
    _R['custom'][x] = dict(
        doc=f'/-- `{x} = status.Error(codes.{c}, "{m}")` (`error.go`): a `*status.Error`, whose `Error()` returns. -/',
        post=f'∃ e : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok e ∗ {CV3}.errorStringSpec e',
        pat='⟨%e@, H@, #S@⟩')
_R['finish'] = [f'ipersist H{x}' for x in _RERRS + list(_RKEYS) + list(_RWERRS)] + _R['finish']
_R['doc'] = _R['doc'].replace("the pointer error `ErrGRPCNotSupportedForLearner`.", "the pointer error `ErrGRPCNotSupportedForLearner`, the token keys, the `ErrGRPC*` errors\n`v3rpc`'s checks and interceptors return and its metadata keys, and (D19j) the `ErrGRPC*` errors its\nwatch server returns, whose `Error()` returns.")

# (prove-rpctypes, 2026-11-20) the `ErrGRPC* = status.Error(codes.X, "...")` variables the fact reads are
# translated: the steps of each initializer (`before`, keyed by the variable), `status.Error`'s spec
# (`EtcdGrove.status.Error.wp_proof`; the code is not `OK`), then the error is an interface value
# (`%e<x>`), grpc's `status` accepts it (`#O<x>`), its `Error()` returns (`#E<x>`, from `statusErrOk`'s
# stable message) and its description is the literal (`%D<x>`; `desc`: restated with the fact's
# name for it). Until then the trust-boundary axioms `<X>_init`. (prove-initmisc, 2026-11-20) also
# `ErrGRPCNotSupportedForLearner`, whose fact says its value is a pointer (`errors.IsPointerError`,
# `ptr`: from the spec's dynamic type and pointer value).
def status_steps(x, desc=None, ptr=False):
    pat = f'⟨%N{x}, #O{x}, #DR{x}, %T{x}, %L{x}⟩' if ptr else f'⟨%N{x}, #O{x}, #DR{x}, -⟩'
    return (['try wp_auto',
             f'wp_apply _root_.Perennial.EtcdGrove.status.Error.wp_proof as %r{x} {pat}',
             '· ipureintro; simp only [google_golang_org.grpc.codes.OK]; exact fun h => absurd (go.intoVal_inj h) (by decide)',
             f'obtain ⟨e{x}, rfl⟩ : ∃ e, r{x} = GoInterface.ok e := match r{x}, N{x} with | .ok e, _ => ⟨e, rfl⟩ | .nil, h => absurd rfl h',
             f'ihave #E{x} : ({CV3}.errorStringSpec e{x} : IProp GF) $$ []',
             f'· ihave ⟨%m{x}, #M{x}⟩ := {CV3}.statusErrOk_msg _ $$ O{x}',
             f'  iapply {CV3}.errorMsgIs_errorStringSpec; iapply M{x}; ipureintro; rfl'] +
            ([f'ihave #D{x} : ({CV3}.descIs (GoInterface.ok e{x}) {CV3}.{desc} : IProp GF) $$ []',
              f'· unfold {CV3}.{desc}; iexact DR{x}'] if desc else []) +
            ([f'have P{x} : errors.IsPointerError e{x} := let ⟨l, hl⟩ := L{x} _ rfl; ⟨_, l, T{x} _ rfl, hl⟩']
             if ptr else []) +
            ['try wp_auto'])

_RSTATUS = dict({x: None for x in _RERRS + list(_RWERRS)}, ErrGRPCFutureRev='futureRevDesc',
                ErrGRPCCompacted='compactedDesc')
for x, desc in _RSTATUS.items():
    del _R['custom'][x]
    _R.setdefault('before', {})[x] = status_steps(x, desc)
    _R['alloc_types'][x] = 'GoInterface'
del _R['custom']['ErrGRPCNotSupportedForLearner']
_R.setdefault('before', {})['ErrGRPCNotSupportedForLearner'] = status_steps('ErrGRPCNotSupportedForLearner', ptr=True)
_R['alloc_types']['ErrGRPCNotSupportedForLearner'] = 'GoInterface'
_R['imports'].append('Proof.google_golang_org.grpc.status.Error')

# (prove-rpcmap, 2026-11-20) the whole package is translated: its other `ErrGRPC* = status.Error(...)`
# errors (`status_steps`), the map literal `errStringToError` and the client-side errors
# `Err* = Error(ErrGRPC*)`; until then the trust-boundary axioms `opaqueInitsOk`, `errStringToError_init`
# and the seven `Err*_init`. The map's keys are `ErrorDesc(ErrGRPC*)` (`ErrorDesc.wp_init`: over grpc's
# `status`, the package's own `isPkgInit` not holding yet), each its description
# (`descIs`, errdesc stage 2b; `errDesc` until then), and its values the `ErrGRPC*` errors: built under `rpctypesErrMapInv` (each value one
# grpc's `status` accepts, under its description), it gives the fact's map. `Error(ErrGRPC*)` is then
# `Error.wp_initErr` (an `EtcdError` with `ErrGRPC*`'s description: its key is in the map, found along
# the literal's insertions) or, for `ErrGRPCTimeoutWaitAppliedIndex` (no key of the map),
# `Error.wp_initAny`.
def _rpc_code():
    return open('Code/go_etcd_io/etcd/api/v3/v3rpc/rpctypes.lean').read()
_RPC_CODE = _rpc_code()
# the variables' stores, in execution order (the translation nests them in reverse)
_RPC_STORES = list(reversed(re.findall(r'\(GoStore go\.error\)\)\) \(Pair \(App \(Val \(GoInstruction \(GlobalVarAddr (\w+)\)',
                                       _RPC_CODE)))
# the aliases (`ErrGRPCClusterIdMismatch = ErrGRPCClusterIDMismatch`, deprecated names): a load
_RPC_ALIASES = ['ErrGRPCClusterIdMismatch', 'ErrClusterIdMismatch']
# the `status.Error(...)` errors
_RPC_STATUS = [x for x in _RPC_STORES if x.startswith('ErrGRPC') and x not in _RPC_ALIASES]
assert len(_RPC_STATUS) == _RPC_CODE.count('FuncResolve _root_.Perennial.google_golang_org.grpc.status.Error []'), _RPC_STATUS
# the map literal's keys `ErrorDesc(X)`, in the literal's order (its values are the same `X`)
_RPC_KEYS = re.findall(r'\(Let "\$k\d+" \(Let "\$a0" \(App \(Val \(GoInstruction \(GoLoad go\.error\)\)\) '
                       r'\(App \(Val \(GoInstruction \(GlobalVarAddr (\w+)\)', _RPC_CODE)
_RPC_VALS = re.findall(r'\(Let "\$v\d+" \(App \(Val \(GoInstruction \(GoLoad go\.error\)\)\) '
                       r'\(App \(Val \(GoInstruction \(GlobalVarAddr (\w+)\)', _RPC_CODE)
# `Error(X)`'s arguments in execution order, and the variables they initialize (in the same order)
_RPC_ERRARGS = re.findall(r'\(Let "\$r0" \(Let "\$a0" \(App \(Val \(GoInstruction \(GoLoad go\.error\)\)\) '
                          r'\(App \(Val \(GoInstruction \(GlobalVarAddr (\w+)\)\)\) \(Val #\(\)\)\)\)\n\s*'
                          r'\(App \(App \(Val \(GoInstruction \(FuncResolve Error \[\]\)\)\)', _RPC_CODE)

# the client-side errors `Err* = Error(ErrGRPC*)`, with their arguments
_RPC_ERRS = [x for x in _RPC_STORES if not x.startswith('ErrGRPC') and x not in _RPC_ALIASES]
assert len(_RPC_ERRS) == len(_RPC_ERRARGS) and _RPC_KEYS == _RPC_VALS, (_RPC_ERRS, _RPC_ERRARGS)
_RPC_ERRS = dict(zip(_RPC_ERRS, _RPC_ERRARGS))
_RPCST = '{Hd:google_golang_org.grpc.status}'
for x in _RPC_STATUS:
    if x not in _R['before']:
        _R['before'][x] = status_steps(x)
    _R['alloc_types'][x] = 'GoInterface'
for x in _RPC_ALIASES + list(_RPC_ERRS):
    _R['alloc_types'][x] = 'GoInterface'
_R['alloc_types']['errStringToError'] = 'Loc'
for x in ['ErrFutureRev', 'ErrCompacted', 'errStringToError', 'ErrUserEmpty', 'ErrInvalidAuthToken',
          'ErrAuthOldRevision', 'ErrNoLeader', 'ErrAuthNotEnabled']:
    del _R['custom'][x]
_RPC_ARGS = ('EtcdGrove.status.FromError.wp_proof EtcdGrove.rpctypes.EtcdError.Error.wp_proof HtyRpc')
_RPC_ED = '(EtcdGrove.rpctypes.ErrorDesc.wp_init EtcdGrove.status.FromError.wp_proof)'
# the map literal: its keys (`ErrorDesc(X)`, each its description), then the map made and its entries inserted
_R['before']['errStringToError'] = (
    ['have HtyRpc : go_etcd_io.etcd.cache.v3.rpctypesEtcdErrorTy (GF := GF) (hG := hG) :=',
     '  ⟨EtcdGrove.RpctypesEtcdErrorMethods.leaf, EtcdGrove.RpctypesEtcdErrorMethods.noGRPCStatus,',
     '   EtcdGrove.RpctypesEtcdErrorMethods.noIs, EtcdGrove.RpctypesEtcdErrorMethods.noFormat,',
     '   EtcdGrove.RpctypesEtcdErrorMethods.errorSig⟩'] +
    sum([['try wp_auto',
          f'wp_apply ({_RPC_ED} (GoInterface.ok e{x}) _) $$ [${_RPCST} $O{x} $DR{x}]'] for x in _RPC_KEYS], []) +
    ['try wp_auto',
     'wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string go.error) as %mesm Hesm0',
     'ihave Hesm := EtcdGrove.rpctypes_errMapInv_empty mesm $$ Hesm0',
     'try wp_auto'] +
    sum([[f'wp_apply (EtcdGrove.rpctypes_wp_errMapInsert mesm _ e{x} _) $$ [$Hesm $O{x} $DR{x}] as Hesm',
          'try wp_auto'] for x in _RPC_KEYS], []))
# `Err* = Error(ErrGRPC*)`: the map's facts first (before the first one), then each call
_RPC_FIRST = next(iter(_RPC_ERRS))
for x, g in _RPC_ERRS.items():
    st = []
    if x == _RPC_FIRST:
        st += ['try wp_auto', 'ihave ⟨Hesm, #MS, #MD⟩ := EtcdGrove.rpctypes_errMapInv_elim _ _ $$ Hesm', 'ipersist Hesm', 'ipersist HerrStringToError']
    st += ['try wp_auto']
    if g in _RPC_KEYS:
        st += [f'wp_apply (EtcdGrove.rpctypes.Error.wp_initErr {_RPC_ED} {_RPC_ARGS} e{g} _)',
               f'    $$ [${_RPCST} $HerrStringToError $Hesm $MS $MD $O{g} $DR{g}] as %x{x} ⟨%X{x}, #S{x}⟩',
               '· ipureintro',
               '  repeat (first | exact EtcdGrove.rpctypes_lookup_insert_isSome _ _ _ _ (Or.inl rfl) | refine EtcdGrove.rpctypes_lookup_insert_isSome _ _ _ _ (Or.inr ?_))']
        if x in ('ErrFutureRev', 'ErrCompacted'):
            st += [f'ihave #D{x} : (go_etcd_io.etcd.cache.v3.descIs (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x{x})',
                   f'    go_etcd_io.etcd.cache.v3.{_RSTATUS[g]} : IProp GF) $$ []',
                   f'· iapply (go_etcd_io.etcd.cache.v3.descIs_etcdError_of _ _ (by unfold go_etcd_io.etcd.cache.v3.{_RSTATUS[g]}; exact X{x}))',
                   f'have F{x} : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Format" = none := HtyRpc.2.2.2.1',
                   f'have T{x} : ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x{x} =',
                   f'    interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x := ⟨_, rfl⟩']
    else:
        st += [f'wp_apply (EtcdGrove.rpctypes.Error.wp_initAny {_RPC_ED} {_RPC_ARGS} e{g})',
               f'    $$ [${_RPCST} $HerrStringToError $Hesm $MS $MD $O{g}] as %r{x} -']
    st += ['try wp_auto']
    _R['before'][x] = st
_R['finish'].remove('ipersist HerrStringToError')
_R['rec_depth'] = 200000
_R['imports'] += ['Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error',
                  'Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc',
                  'Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError__Error',
                  'Proof.google_golang_org.grpc.status.FromError']
_R['pre'] += [
    'section rpcmap',
    'variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]',
    'variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]',
    '',
    '/-- (prove-rpcmap) A lookup in `<[k := v]> m` finds `v` at `k`, or one of `m`\'s entries. -/',
    'theorem EtcdGrove.rpctypes_lookup_insert_some {K V : Type} [DecidableEq K] {m : GMap K V} {k k\' : K}',
    '    {v w : V} (h : (<[k := v]> m) !! k\' = some w) : (k = k\' ∧ v = w) ∨ m !! k\' = some w :=',
    '  ((GMap.lookup_insert_Some m k k\' v w).1 h).imp id And.right',
    '',
    '/-- (prove-rpcmap) A key of `<[k := v]> m`: `k`, or one of `m`\'s. -/',
    'theorem EtcdGrove.rpctypes_lookup_insert_isSome {K V : Type} [DecidableEq K] (m : GMap K V) (k k\' : K)',
    '    (v : V) (h : k = k\' ∨ (m !! k\').isSome) : ((<[k := v]> m) !! k\').isSome :=',
    '  (GMap.lookup_insert_is_Some m k k\' v).2 (by by_cases hk : k = k\' <;> simp_all)',
    '',
    '/-- (prove-rpcmap) The map literal `errStringToError` while `rpctypes`\' initializer builds it: its',
    'values are errors grpc\'s `status` accepts, each under its description (`rpctypesInit`\'s map). -/',
    'abbrev EtcdGrove.rpctypesErrMapInv (mref : Loc) (M : GMap GoString GoInterface) : IProp GF :=',
    '  iprop(mref ↦$ M ∗',
    '    (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗',
    '    (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.descIs v k))',
    '',
    'theorem EtcdGrove.rpctypes_errMapInv_elim (mref : Loc) (M : GMap GoString GoInterface) :',
    '    (EtcdGrove.rpctypesErrMapInv mref M : IProp GF) ⊢ mref ↦$ M ∗',
    '      (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗',
    '      (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.descIs v k) := by',
    '  iintro H; iexact H',
    '',
    'theorem EtcdGrove.rpctypes_errMapInv_empty (mref : Loc) :',
    '    (mref ↦$ (∅ : GMap GoString GoInterface) : IProp GF) ⊢ EtcdGrove.rpctypesErrMapInv mref ∅ := by',
    '  iintro Hm',
    '  unfold EtcdGrove.rpctypesErrMapInv',
    '  iframe Hm',
    '  isplitr',
    '  · iintro !> %k %v %h; simp at h',
    '  · iintro !> %k %v %h; simp at h',
    '',
    '/-- (prove-rpcmap) Inserting an error grpc\'s `status` accepts under its description. -/',
    'theorem EtcdGrove.rpctypes_wp_errMapInsert (mref : Loc) (M : GMap GoString GoInterface) (e : GoInterfaceOk)',
    '    (d : GoString) :',
    '    {{ (EtcdGrove.rpctypesErrMapInv mref M : IProp GF) ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗',
    '        go_etcd_io.etcd.cache.v3.descIs (GoInterface.ok e) d }}',
    '      (App (App (App (Val (map.insert go.string)) (Val #mref))',
    '        (Val #d)) (Val #(GoInterface.ok e)))',
    '    {{ RET #(); EtcdGrove.rpctypesErrMapInv mref (<[d := GoInterface.ok e]> M) }} := by',
    '  wp_start_folded as ⟨Hinv, #Hok, #Hd⟩',
    '  ihave ⟨Hm, #HS, #HD⟩ := EtcdGrove.rpctypes_errMapInv_elim _ _ $$ Hinv',
    '  wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string) $$ Hm as Hm',
    '  iapply HΦ',
    '  unfold EtcdGrove.rpctypesErrMapInv',
    '  iframe Hm',
    '  isplitr',
    '  · iintro !> %k %v %h',
    '    rcases EtcdGrove.rpctypes_lookup_insert_some h with ⟨-, rfl⟩ | h',
    '    · iexact Hok',
    '    · iapply HS; ipureintro; exact h',
    '  · iintro !> %k %v %h',
    '    rcases EtcdGrove.rpctypes_lookup_insert_some h with ⟨rfl, rfl⟩ | h',
    '    · iexact Hd',
    '    · iapply HD; ipureintro; exact h',
    '',
    'end rpcmap',
    '']
_R['doc'] = _R['doc'].replace("""Its variables'
initializers (`error.go`, `metadatafields.go`) are untranslated: the trust-boundary axioms
`<X>_init` state the ones the fact reads, `opaqueInitsOk` the others.""",
"""(prove-rpcmap, 2026-11-20) Its
variables' initializers (`error.go`, `md.go`, `metadatafields.go`) are all translated: the
`status.Error` errors, the map literal `errStringToError` (keys `ErrorDesc(ErrGRPC*)`) and the
client-side `Err* = Error(ErrGRPC*)` (`Error.wp_initErr`); until then the trust-boundary axioms
`opaqueInitsOk`, `errStringToError_init` and `<X>_init` for the errors the fact reads.""")

_P = SPECIAL['go_etcd_io.etcd.api.v3.etcdserverpb']
_P['doc'] = """Its fact (`etcdserverpbInit`, `cache/v3/Base.lean`): the sort enumerations' name maps. Its
initializer allocates and sets the translated gRPC service descriptors (`KV_ServiceDesc`, ...:
`grpc.ServiceDesc` literals), initializes its imports and runs its other variables' untranslated
initializers (the generated protobuf descriptors and enum maps), which the trust-boundary axiom
`opaqueInitsOk` says run. (const-inits, 2026-11-19) The two sort enumerations' name maps the fact
reads (`RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`: `map[int32]string` literals,
`rpc.pb.go`) are translated and set; until then the trust-boundary axioms `<X>_init`."""
_P['alloc_types'].update({'RangeRequest_SortOrder_name': 'Loc', 'RangeRequest_SortTarget_name': 'Loc'})
# (etcd-small-3, 2026-11-23, etcd-grove#39) and `AlarmType_name`, which `AlarmType.String`'s trusted
# model reads (until then skipped)
_P['doc'] += """ (etcd-grove#39, 2026-11-23) And `AlarmType_name` (a `map[int32]string` literal),
which the fact holds read-only, `etcdserverpb.alarmTypeNames`: `AlarmType.String`'s trusted model reads
it."""
_P['alloc_types']['AlarmType_name'] = 'Loc'
_P['heavy'] = True
_P['pre'] = ['/-- A small 64-bit literal\'s value as a signed natural (the descriptors\' slice indices). -/',
             'theorem EtcdGrove.sint_nat_ofNat64 (n : Nat) (h : n < 2 ^ 63) : sint.nat (BitVec.ofNat 64 n) = n := by',
             '  simp [sint.nat, BitVec.toInt]; omega', '']
_PB_SL = ['KVm', 'KVs', 'Wm', 'Ws', 'Lm', 'Ls', 'Cm', 'Cs', 'Mm', 'Ms', 'Am', 'As']
_PB_DESCS = ['KV', 'Watch', 'Lease', 'Cluster', 'Maintenance', 'Auth']
_P['before'] = {'$inits': [f'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %p{t} ⟨S{t}, -⟩; try wp_auto'
                            for t in _PB_SL] + ['try wp_auto']}
# (const-inits, 2026-11-19) the sort enumerations' name maps: `map[int32]string` literals
for _x, _h in [('RangeRequest_SortOrder_name', 'Hso'), ('RangeRequest_SortTarget_name', 'Hst'),
               ('AlarmType_name', 'Hatn')]:
    _P['before'][_x] = ['try wp_auto',
        f'wp_apply (wp_map_make1 (K := w32) (V := GoString) go.int32 go.string) as %m{_h} {_h}',
        'try wp_auto',
        f'repeat (wp_apply (wp_mapInsert (K := w32) (V := GoString) go.int32) $$ {_h} as {_h}; try wp_auto)']
def _PB_DOM(n):
    """The name map's domain, keys `0` to `n`: the literal's lookups, case by case."""
    ks = ' ∨ '.join(f'k = W32 {i}' for i in range(n + 1))
    pats = ' | '.join(['rfl'] * (n + 1))
    nes = ', '.join(f'if_neg (show ¬(W32 {i} = k) from fun h => hk (by subst h; simp))' for i in reversed(range(n + 1)))
    return ('ipureintro; intro k; simp only [GMap.lookup_insert_eq_iff, GMap.lookup_empty]; '
            f'by_cases hk : {ks}; '
            f'(· rcases hk with {pats} <;> simp (config := {{decide := true}})); '
            f'(· have hr : ¬ (0 ≤ sint.Z k ∧ sint.Z k ≤ {n}) := fun hr => hk (by word); '
            'simp only [hr, iff_false, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]; '
            f'rw [{nes}])')
_P['finish'] = ([f'ipersist S{t}' for t in _PB_SL] +
                [f'ipersist H{d}_ServiceDesc' for d in _PB_DESCS] +
                [f'iStructNamedSuffix H{d}_ServiceDesc "{d}"' for d in _PB_DESCS] +
                ['ipersist HRangeRequest_SortOrder_name', 'ipersist HRangeRequest_SortTarget_name',
                 'ipersist Hso', 'ipersist Hst', 'ipersist HAlarmType_name', 'ipersist Hatn'] +
                FIN_PRE[:6] + ['imodintro', 'unfold go_etcd_io.etcd.cache.v3.etcdserverpbInit go_etcd_io.etcd.cache.v3.etcdserverpbDescs go_etcd_io.etcd.cache.v3.pbDescIs',
                 'isplitl []', '· iexists _, _; iframe HRangeRequest_SortOrder_name Hso; ' + _PB_DOM(2),
                 'isplitl []', '· iexists _, _; iframe HRangeRequest_SortTarget_name Hst; ' + _PB_DOM(4),
                 'isplitl []', '· iexists _; iframe HAlarmType_name; unfold go_etcd_io.etcd.cache.v3.etcdserverpb.alarmTypeNames; iexact Hatn',
                 'iframe #',
                 'repeat (first | (isplitl []; · (ipureintro; simp (config := {decide := true}) [go.arrayLiteralSize, EtcdGrove.sint_nat_ofNat64])) | (ipureintro; simp (config := {decide := true}) [go.arrayLiteralSize, EtcdGrove.sint_nat_ofNat64]))'])

_C = SPECIAL['go_etcd_io.etcd.client.v3']
# (prove-smallinits, 2026-11-20) the package's other variables translated (until then `opaqueInitsOk`
# and the trust-boundary axioms `defaultCallOpts_init` and `defaultBackoffJitterFraction_init`): the
# three `errors.New` errors, the call options (grpc's `WaitForReady`, `MaxCallSendMsgSize`,
# `MaxCallRecvMsgSize`, translated: struct literals converted to `CallOption`), their slice
# `defaultCallOpts` and the float `defaultBackoffJitterFraction`.
newvars_cfg(_C, ['ErrNoAvailableEndpoints', 'ErrOldCluster', 'ErrMutuallyExclusiveCfg'])
_C['before']['defaultWaitForReady'] = (
    [l for x in ['ErrNoAvailableEndpoints', 'ErrOldCluster', 'ErrMutuallyExclusiveCfg'] for l in newvar_steps(x)] +
    ['try wp_auto'] + _C['before']['defaultWaitForReady'] + ['try wp_auto'] +
    # the three grpc option constructors (translated: a struct literal converted to `CallOption`)
    ['wp_func_call', 'wp_call', 'try wp_auto'] * 3 +
    # `defaultCallOpts`: the slice literal of the three options
    ['wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sco ⟨Sco, -⟩',
     'try wp_auto'])
del _C['before']['ErrNoAvailableEndpoints'], _C['before']['ErrOldCluster'], _C['before']['ErrMutuallyExclusiveCfg']
# (prove-ps2-rqb, 2026-11-22) `defaultOptions` translated (until then the trust-boundary axiom
# `defaultOptions_init`): `&options{..., backoffFunc: backoffLinearWithJitter(50ms, 0.10), ...}`, the
# backoff function by its proof (over `jitterUp`'s and the trust boundary's `rand.Float64`)
_C['before']['defaultOptions'] = [
    'try wp_auto',
    'wp_apply (EtcdGrove.backoffLinearWithJitter.wp_proof (EtcdGrove.jitterUp.wp_proof EtcdGrove.rand.Float64.wp_proof)) as %bfdo #BdefaultOptions',
    'try wp_auto']
_C['alloc_types'].update({'clientTargetSeq': '_root_.Perennial.sync.atomic.Uint64',
                          'defaultWaitForReady': 'GoInterface', 'defaultMaxCallSendMsgSize': 'GoInterface',
                          'defaultMaxCallRecvMsgSize': 'GoInterface', 'defaultCallOpts': 'GoSlice',
                          'defaultBackoffJitterFraction': 'w64'})
_C['finish'] = (['ipersist Hsnp', 'ipersist HnoPrefixEnd', 'ipersist HdefaultOptions', 'ipersist «$r0»', 'ipersist HdefaultCallOpts',
                 'ipersist HdefaultUnaryMaxRetries', 'ipersist HdefaultBackoffWaitBetween',
                 'ipersist HdefaultBackoffJitterFraction', 'ipersist HvalCtxCh', 'ipersist HzeroTime',
                 'ipersist HmaxBackoff', 'ipersist HLeaseResponseChSize', 'ipersist Sco'] +
                # (real fmt stage 1, 2026-11-24) `clientTargetSeq`'s invariant (`Client.dial`'s counter)
                ['ihave Hcts : _root_.Perennial.sync.atomic.ownUint64 (GF := GF) (globalAddr go_etcd_io.etcd.client.v3.clientTargetSeq) (DFrac.own 1) (W64 0) $$ [HclientTargetSeq]',
                 '· rw [_root_.Perennial.sync.atomic.ownUint64_unseal]',
                 '  unfold _root_.Perennial.sync.atomic.ownUint64Def',
                 "  have e : (zero_val _root_.Perennial.sync.atomic.Uint64) =",
                 "      ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : _root_.Perennial.sync.atomic.Uint64) := rfl",
                 '  rw [← e]; iexact HclientTargetSeq',
                 'imod inv_alloc go_etcd_io.etcd.cache.v3.clientTargetSeqN ⊤ (∃ n : w64, _root_.Perennial.sync.atomic.ownUint64 (GF := GF) (globalAddr go_etcd_io.etcd.client.v3.clientTargetSeq) (DFrac.own 1) n) $$ [Hcts] with #Hcts',
                 '· inext; iexists _; iexact Hcts'] + FIN_PRE[:6] +
                ['imodintro', 'unfold go_etcd_io.etcd.cache.v3.clientv3Init', 'iframe #',
                 'ipureintro',
                 # `defaultOptions`' policy (its struct literal's), `defaultCallOpts`' slice
                 'refine ⟨rfl, rfl, fun v hv => ?_⟩',
                 'have h1 : sint.nat (W64 (0 + 1)) = 1 := rfl',
                 'have h2 : sint.nat (W64 (0 + 1 + 1)) = 2 := rfl',
                 'rw [h1, h2] at hv',
                 'simp only [List.set_cons_succ, List.set_cons_zero, List.mem_cons, List.not_mem_nil, _root_.or_false] at hv',
                 'rcases hv with rfl | rfl | rfl <;> exact ⟨_, _, rfl, by simp⟩'])

_S = SPECIAL['go_etcd_io.etcd.server.v3.storage.schema']
# (2026-11-19) `AllBuckets` and the compaction's two key names are translated (they were the
# trust-boundary axioms `<X>_init`)
_S['doc'] = _S['doc'].replace("and the consistent index's two key names (`cindex.go`).", "the consistent index's two key names (`cindex.go`), `AllBuckets` and the compaction's two key\nnames.")
_S['finish'] = (_S['finish'][:8] + ['ipersist HAllBuckets', 'ipersist HScheduledCompactKeyName', 'ipersist HFinishedCompactKeyName',
                                    'ipersist Hssc', 'ipersist Hsfc']
                + _S['finish'][8:])


def errVarFrom(pkg, X, msg, hd, tag):
    """Lines taking `X`'s `errorsNewVar` from `etcdserver/errors`' fact (`errorsInit`) at `hd`."""
    return [f'ihave Hei{tag} : ({pkg}.errorsInit : IProp GF) $$ []',
            f'· iapply isPkgInit_access $$ {hd}',
            f'icases Hei{tag} with ⟨-, #Hev{tag}, -⟩',
            f'ihave #N{tag} := EtcdGrove.errorsNewVars_mem (X := {pkg}.{X}) (m := go!"{msg}")'
            f' (by unfold {pkg}.errorsMsgs; mem_tac) $$ Hev{tag}']

# Item 8, step 4 (2026-10-17): mvcc, txn, apply.
def _metric(x, kind, preds, file='metrics.go'):
    post = f'∃ m : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok m ∗ ' + ' ∗ '.join(f'{q} m' for q in preds)
    pat = '⟨%m@, H@' + ''.join(f', #S{i}@' for i in range(len(preds))) + '⟩'
    what = {'counter': 'a `Counter`: `Inc` returns, and `Add` of a non-negative value',
            'gauge': 'a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return',
            'hist': 'a `Histogram`, whose `Observe` returns'}[kind]
    ctor = {'counter': 'NewCounter', 'gauge': 'NewGauge', 'hist': 'NewHistogram'}[kind]
    return dict(doc=f'/-- `{x} = prometheus.{ctor}(...)` (`{file}`): {what}. -/', post=post, pat=pat)

_MV_CNT = ['rangeCounter', 'putCounter', 'deleteCounter', 'txnCounter', 'dbCompactionKeysCounter']
_MV_GAU = ['watchStreamGauge', 'watcherGauge', 'pendingEventsGauge', 'totalPutSizeGauge']
_MV_HIS = ['indexCompactionPauseMs', 'dbCompactionPauseMs', 'dbCompactionTotalMs']
# (metric-inits, 2026-11-19) its metrics' initializers are translated (`metric_steps`): until then
# the trust-boundary axioms `<X>_init`
_MV_GAU += ['slowWatcherGauge', 'keysGauge', 'dbCompactionLast']
_MV_METRICS = ([(x, 'counter') for x in _MV_CNT] + [(x, 'gauge') for x in _MV_GAU] +
               [(x, 'hist') for x in _MV_HIS])
# (prove-initmisc, 2026-11-20) the metrics no fact names, translated too (until then `opaqueInitsOk`):
# a counter and two histograms (`metric_steps`) and the `NewGaugeFunc` gauges (`gaugefunc_steps`)
_MV_OTHER = [('totalEventsCounter', 'counter'), ('hashSec', 'hist'), ('hashRevSec', 'hist')]
_MV_GFUNC = ['dbTotalSize', 'dbTotalSizeInUse', 'dbOpenReadTxN', 'currentRev', 'compactRev']

_mv_custom = {}
_MV_ERR = {'ErrRevisionNotFound': 'RNF', 'ErrCompacted': 'CP', 'ErrFutureRev': 'FR',
           'ErrWatcherNotExist': 'WNE', 'ErrEmptyWatcherRange': 'EWR', 'ErrWatcherDuplicateID': 'WDI'}
# (R2 of the restore plan) the metrics reporters `setupMetricsReporter` sets, each under its lock.
_MV_REPORT = ['reportDbTotalSizeInBytes', 'reportDbTotalSizeInUseInBytes', 'reportDbOpenReadTxN',
              'reportCurrentRev', 'reportCompactRev']

SPECIAL['go_etcd_io.etcd.server.v3.storage.mvcc'] = dict(
    doc="""Its fact (`mvccInit`, `Base.lean`): its error variables (translated `errors.New` calls), its
metrics (`metrics.go`, translated: `prometheus.NewCounter`, `NewGauge` and `NewHistogram` of an
options literal, the trust-boundary axioms of those constructors and `ExponentialBuckets`'s spec; a
counter's `Add` only of a non-negative value), its constants, and `schema`'s two compaction key names (from `schema`'s
fact). (prove-initmisc, 2026-11-20) Its other metrics (`totalEventsCounter`, `hashSec`,
`hashRevSec`, and the `NewGaugeFunc` gauges, over that constructor's spec) and `_` (`var _
WatchableKV = (*watchableStore)(nil)`) are translated too (until then the trust-boundary axiom
`opaqueInitsOk`).""",
    imports=['Perennial.Proof.context.NewErrorString', 'Perennial.Proof.errors.NewVar', 'Proof.errors.NewVarCell',
             'Perennial.Proof.sync.RWMutexGuard'] + PROM_CTORS +
            ['Proof.github_com.prometheus.client_golang.prometheus.NewGaugeFunc'],
    custom=_mv_custom,
    alloc_types={**{f'{x}Mu': '_root_.Perennial.sync.RWMutex' for x in _MV_REPORT},
                 **{x: 'GoInterface' for x, _ in _MV_METRICS + _MV_OTHER},
                 **{x: 'GoInterface' for x in _MV_GFUNC},
                 **{x: 'GoFunc' for x in _MV_REPORT},
                 'watchBatchMaxRevs': 'w64', 'ErrWatcherDuplicateID': 'GoInterface',
                 'ErrEmptyWatcherRange': 'GoInterface', 'ErrWatcherNotExist': 'GoInterface',
                 'watchResyncPeriod': 'w64', 'defaultCompactionBatchLimit': 'w64',
                 'defaultCompactionSleepInterval': 'w64', 'maxWatchersPerSync': 'w64', 'chanBufLen': 'w64',
                 'ErrFutureRev': 'GoInterface', 'ErrCompacted': 'GoInterface',
                 'ErrRevisionNotFound': 'GoInterface', 'restoreChunkKeys': 'w64'},
    before={'defaultCompactionBatchLimit': ['wp_apply _root_.Perennial.context.wp_New_errorString as %xRNF ⟨-, #MRNF⟩'] +
                                [f'wp_apply EtcdGrove.wp_New_errorString_cell as %x{t} ⟨#M{t}, #C{t}⟩'
                                 for t in ['CP', 'FR']],
            # (mvccfull's Freeze, 2026-11-10) `ErrWatcherNotExist`'s and `ErrEmptyWatcherRange`'s
            # message cells too, for `errVars.law`'s apartness (`mvccInit`'s last conjunct)
            '$inits': [f'wp_apply EtcdGrove.wp_New_errorString_cell as %x{t} ⟨#M{t}, #C{t}⟩'
                       for t in ['WNE', 'EWR']] +
                      [f'wp_apply _root_.Perennial.context.wp_New_errorString as %x{t} ⟨-, #M{t}⟩'
                       for t in ['WDI']],
            **{x: metric_steps(x, k) for x, k in _MV_METRICS + _MV_OTHER},
            **{x: gaugefunc_steps(x) for x in _MV_GFUNC}},
    finish=([f'ipersist H{x}' for x in _MV_ERR] +
            [f'ipersist H{x}' for x in list(_mv_custom)] + [f'ipersist H{x}' for x, _ in _MV_METRICS] +
            # (prove-ps2-metrics, 2026-11-22) `ReportEventReceived`'s counter, in the fact's last conjunct
            ['ipersist HtotalEventsCounter'] +
            ['ipersist HdefaultCompactionBatchLimit', 'ipersist HdefaultCompactionSleepInterval'] +
            ['ipersist HchanBufLen', 'ipersist HmaxWatchersPerSync', 'ipersist HwatchResyncPeriod',
             'ipersist HwatchBatchMaxRevs', 'ipersist HrestoreChunkKeys',
             'ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.server.v3.storage.schema}',
             'icases Hsi with ⟨-, -, -, -, -, #HSK, #HFK, -⟩',
             'ihave #VCP : (EtcdGrove.errVarCell ErrCompacted go!"mvcc: required revision has been compacted" : IProp GF) $$ []',
             '· unfold EtcdGrove.errVarCell; iexists _; iframe HErrCompacted CCP',
             'ihave #VFR : (EtcdGrove.errVarCell ErrFutureRev go!"mvcc: required revision is a future revision" : IProp GF) $$ []',
             '· unfold EtcdGrove.errVarCell; iexists _; iframe HErrFutureRev CFR',
             'ihave #VEWR : (EtcdGrove.errVarCell ErrEmptyWatcherRange go!"mvcc: watcher range is empty" : IProp GF) $$ []',
             '· unfold EtcdGrove.errVarCell; iexists _; iframe HErrEmptyWatcherRange CEWR',
             'ihave #VWNE : (EtcdGrove.errVarCell ErrWatcherNotExist go!"mvcc: watcher does not exist" : IProp GF) $$ []',
             '· unfold EtcdGrove.errVarCell; iexists _; iframe HErrWatcherNotExist CWNE',
             '-- (R2) the metrics reporters\' locks, each over its reporter (any closure)'] +
            [l for i, x in enumerate(_MV_REPORT) for l in [
                f'imod (sync.init_RWMutex (go_etcd_io.etcd.server.v3.storage.mvcc.reportP {x}) (globalAddr {x}Mu) (E := ⊤)) $$ [H{x}] H{x}Mu with HRP{i}',
                '· inext',
                '  unfold go_etcd_io.etcd.server.v3.storage.mvcc.reportP',
                f'  iexists _; iframe H{x}',
                f'ihave ⟨-, #GRP{i}⟩ := sync.ownRWMutex_slots_guard _ _ $$ HRP{i}']] + FIN_PRE[:6] +
           ['imodintro', 'unfold mvccInit EtcdGrove.errorsNewVar', 'iframe #',
            'rw [show (W64 100000000 : w64) = W64 100 * W64 1000000 by rfl]', 'iexact HwatchResyncPeriod']),
)

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.txn'] = dict(
    doc="""Its fact (`txnInit`, `Base.lean`): `lease.ErrLeaseNotFound` and `etcdserver/errors.ErrKeyNotFound`
(from their packages' facts) and its counter `slowApplies` (`metrics.go`, translated: `NewCounter`'s
spec; until 2026-11-19 the trust-boundary axiom `slowApplies_init`). `opaqueInitsOk` states its other untranslated
initializers run.""",
    imports=PROM_CTORS,
    alloc_types={'slowApplies': 'GoInterface'},
    before={'slowApplies': metric_steps_to('slowApplies', 'counter', 'go_etcd_io.etcd.server.v3.lease.counterSpec')},
    finish=['ipersist HslowApplies',
            'ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []',
            '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.server.v3.lease}',
            'icases Hli with ⟨#HLNF0, -⟩',
            'iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at HLNF0',
            'icases HLNF0 with ⟨%eLNF, #HLNF, -⟩'] +
           errVarFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrKeyNotFound', 'etcdserver: key not found', '{Hd:go_etcd_io.etcd.server.v3.etcdserver.errors}', 'KNF') +
           ['iunfold EtcdGrove.errorsNewVar at NKNF', 'icases NKNF with ⟨%xKNF, #HKNF, -⟩'] +
           FIN_PRE[:6] + ['imodintro', 'unfold txnInit', 'iframe #'],
)

_ERRLEAF_PRE = [
    'section errVarLeafOfNew',
    'variable [GooseExts] [GooseSemantics] [GooseInterp]',
    'variable [go_gctx : GoGlobalContext]',
    'variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]',
    'variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions]',
    '',
    '/-- An `errors.New` variable (`errorsNewVar`) holds a leaf pointer error without `Is` whose',
    '`Error()` returns (`errVarLeaf`), by `ErrorStringLeaf`. -/',
    'theorem EtcdGrove.errVarLeaf_of_newVar (X msg : GoString) :',
    '    EtcdGrove.errorsNewVar (GF := GF) X msg ⊢ EtcdGrove.errVarLeaf X := by',
    '  unfold EtcdGrove.errorsNewVar EtcdGrove.errVarLeaf',
    '  iintro ⟨%x, #Hx, #Hm⟩',
    '  iexists _',
    '  iframe Hx',
    '  isplitr',
    '  · ipureintro; first | exact EtcdGrove.errorString_errLeaf x | exact EtcdGrove.errorString_leaf x',
    '  unfold EtcdGrove.errMsgOk',
    '  iapply EtcdGrove.errorMsg_triple',
    '  iexact Hm',
    '',
    'end errVarLeafOfNew',
    '']

def errLeafFrom(pkg, X, msg, hd, tag):
    """`X`'s `errVarLeaf` (`#L<tag>`) and points-to (`#H<tag>`), from `etcdserver/errors`' fact."""
    return errVarFrom(pkg, X, msg, hd, tag) + [
        f'ihave #L{tag} := EtcdGrove.errVarLeaf_of_newVar _ _ $$ N{tag}',
        f'iunfold EtcdGrove.errorsNewVar at N{tag}', f'icases N{tag} with ⟨%x{tag}, #H{tag}, -⟩']

def _noSpaceApart():
    """D19k: `ErrNoSpace` apart from the backend's errors (`applyErrVars`' last four), from the
    message cells of `etcdserver/errors`' (`Hd19`), `lease`'s (`CLNF`) and `mvcc`'s (`CMC`, `CMF`)."""
    E = 'go_etcd_io.etcd.server.v3.etcdserver.errors'
    def cell(X, msg, tag):
        return (f'ihave #C{tag} := EtcdGrove.errVarCells_mem (X := {E}.{X}) (m := go!"{msg}")'
                f' (by unfold {E}.errorsMsgs; mem_tac) $$ HcE')
    def apart(h, mh, tag):
        return (f'ihave #A{tag} := EtcdGrove.errVarApart_of {E}.ErrNoSpace {h} go!"etcdserver: no space"'
                f' go!"{mh}" (by decide) $$ CNSP C{tag}')
    return [f'ihave HeiE : ({E}.errorsInit : IProp GF) $$ []',
            '· iapply isPkgInit_access $$ Hd19',
            'icases HeiE with ⟨-, -, #HcE⟩',
            cell('ErrNoSpace', 'etcdserver: no space', 'NSP'),
            cell('ErrKeyNotFound', 'etcdserver: key not found', 'KNF'),
            apart(f'{E}.ErrKeyNotFound', 'etcdserver: key not found', 'KNF'),
            apart('go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound', 'lease not found', 'LNF'),
            # (lease-grant amendment (E)) the grant's backend errors
            apart('go_etcd_io.etcd.server.v3.lease.ErrLeaseExists', 'lease already exists', 'LEx'),
            apart('go_etcd_io.etcd.server.v3.lease.ErrLeaseTTLTooLarge', 'too large lease TTL', 'LTL'),
            apart('go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev',
                  'mvcc: required revision is a future revision', 'MF'),
            apart('go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted',
                  'mvcc: required revision has been compacted', 'MC')]

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.apply'] = dict(
    doc="""Its fact (`applyInit`, `Base.lean`): its gauge vector `alarms` with its label names
(`metrics.go`, translated, over prometheus's `NewGaugeVec` spec; until 2026-11-19 the
trust-boundary axiom `alarms_init`), and the error variables it returns or compares with
(`applyErrVars`), from their packages' facts (`etcdserver/errors`', `lease`'s, `mvcc`'s), leaf
errors by `EtcdGrove.ErrorStringLeaf`.""",
    pre=_ERRLEAF_PRE,
    finish=(['ipersist Halarms'] +
            errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrCorrupt', 'etcdserver: corrupt cluster', 'Hd19', 'COR') +
            errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrNoSpace', 'etcdserver: no space', 'Hd19', 'NSP') +
            errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrKeyNotFound', 'etcdserver: key not found', 'Hd19', 'KNF') +
            ['ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd10',
             'icases Hli with ⟨#HLNF0, -, -, -, -, -, -, #CLNF, #CLEx, #CLTL, -⟩',
             'ihave #LLNF : (EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound : IProp GF) $$ []',
             '· unfold EtcdGrove.errVarLeaf EtcdGrove.errLeaf EtcdGrove.errMsgOk',
             '  iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at HLNF0',
             '  iexact HLNF0',
             'ihave Hmi : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd18',
             'icases Hmi with ⟨' + '-, ' * 30 + '#NMC, #NMF, -, -, #CMC, #CMF, -⟩',
             'ihave #LMC := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NMC',
             'ihave #LMF := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NMF'] +
            _noSpaceApart() +
            # (the auth plan's E3i, 2026-10-27) `ErrNoSpace` apart from the auth package's error
            # variables, from their message cells (`authInit`'s last conjunct)
            ['ihave Hau : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.server.v3.auth}',
             'icases Hau with ⟨' + '-, ' * 23 + '#AUC⟩',
             'ihave #AAU := EtcdGrove.errVarApart_cells go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace'
             ' go!"etcdserver: no space" go_etcd_io.etcd.server.v3.auth.authErrMsgs'
             ' (go_etcd_io.etcd.server.v3.auth.authErrMsgs_ne_of _ (by decide)) $$ CNSP AUC'] +
            FIN_PRE[:6] + ['imodintro', 'unfold applyInit applyErrVars authErrsApart', 'iframe #']),
)

promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.apply'], 'alarms', 'Gauge', ['server_id', 'alarm_type'])

_SRV_ERRS = [('ErrTooManyRequests', 'etcdserver: too many requests', 'TMR'),
             ('ErrRequestTooLarge', 'etcdserver: request is too large', 'RTL'),
             ('ErrStopped', 'etcdserver: server stopped', 'STP'),
             ('ErrCanceled', 'etcdserver: request cancelled', 'CAN'),
             ('ErrTimeout', 'etcdserver: request timed out', 'TMO'),
             ('ErrTimeoutDueToLeaderFail', 'etcdserver: request timed out, possibly due to previous leader failure', 'TLF'),
             ('ErrTimeoutDueToConnectionLost', 'etcdserver: request timed out, possibly due to connection lost', 'TCL')]
# (metric-inits, 2026-11-19) its gauges and counters translated (`metric_steps`): until then the
# trust-boundary axioms `<X>_init`
_SRV_SET = ['hasLeader', 'isLeader', 'proposalsCommitted', 'proposalsApplied']
_SRV_METRICS = ([(x, 'gauge') for x in _SRV_SET + ['proposalsPending', 'applySnapshotInProgress']] +
                [(x, 'counter') for x in ['leaderChanges', 'heartbeatSendFailures', 'proposalsFailed']])
_srv_steps = {x: (metric_steps_to(x, k, 'go_etcd_io.etcd.server.v3.etcdserver.gaugeSetSpec')
                  if x in _SRV_SET else metric_steps(x, k)) for x, k in _SRV_METRICS}
# the construction's gauge vectors (unit N4, 2026-10-17: `NewServer` reads them) and the request
# path's histogram vector (translated since 2026-11-19, `promvec` below)
_SRV_VECS = [('serverFeatureEnabled', 'Gauge', ['name', 'stage']), ('serverID', 'Gauge', ['server_id']),
             ('requestDurationSec', 'Histogram', ['type', 'success'])]
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver'] = dict(
    doc="""Its fact (`srvInit`, `BaseApply.lean`): its metrics (`metrics.go`: the gauges and counters
translated, over prometheus's constructor specs, until 2026-11-19 the trust-boundary axioms
`<X>_init`; the vectors, with their label names, translated over the `New<Kind>Vec` specs, until
2026-11-19 the axioms `<X>_init`), and from its imports' facts `traceutil.Tracer`, `schema`'s
`AllBuckets` and the error variables of `etcdserver/errors`, `auth` and raft it returns (leaf
errors by `EtcdGrove.ErrorStringLeaf`). Its precondition has the
registration rights of the metric names of its import closure (`namesFree initNames`, decision D16;
the read package's, `EtcdGrove.read.readRegPerm`, until mustreg, 2026-11-20), which it passes on to
the registering packages' initializers. (D19r (C), 2026-10-18) And `raftStatusMu` (`raft.go`), initialized here,
guarding `raftStatus` (`rnRaftStatusOk`; the `init()` of `raft.go` registers an `expvar` closure that
reads `raftStatus` under the mutex: a trusted no-op model since etcd-grove#39, 2026-11-23, as `server.go`'s,
since no verified code reads `expvar`'s registry; `metrics.go`'s, which registers the metrics, stays
names-only, the trust-boundary axiom `initFuncsOk`: translating it needs Perennial's `runtime.Version`). (revoke-open, 2026-11-06) And the counter `leaseExpired`
(`metrics.go`, translated: `prometheus.NewCounter` of a `CounterOpts` literal, the trust-boundary
axiom `NewCounter.wp_proof`), which
`revokeExpiredLeases` increments. (auth-mediation M2, 2026-11-20) And `PromoteMember`'s metrics,
the counter `learnerPromoteSucceed` and the counter vector `learnerPromoteFailed`.""",
    imports=PROM_CTORS,
    alloc_types={'raftStatusMu': '_root_.Perennial.sync.Mutex', 'raftStatus': 'GoFunc',
                 'leaseExpired': 'GoInterface', **{x: 'GoInterface' for x, _ in _SRV_METRICS}},
    # (revoke-open, 2026-11-06) `leaseExpired`'s translated initializer: the literal, `NewCounter`
    before={'leaseExpired': [
        'wp_apply EtcdGrove.prometheus.NewCounter.wp_proof _ _ _ _ _ rfl (by decide) as %cLE ⟨#CLE, -⟩',
        'try wp_auto'], **_srv_steps},
    finish=([f'ipersist H{x}' for x, _, _ in _SRV_VECS] + [f'ipersist H{x}' for x, _ in _SRV_METRICS] +
            ['ipersist HleaseExpired', 'ipersist HlearnerPromoteSucceed', 'ipersist HlearnerPromoteFailed',
             'ipersist HfdUsed', 'ipersist HfdLimit'] +
            # (claim #34, 2026-11-23) `bootstrap`'s request-size warning reads the string
            ['ipersist HrecommendedMaxRequestBytesString'] +
            ['imod sync.init_Mutex (iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f)) ⊤ (globalAddr raftStatusMu) $$ HraftStatusMu [HraftStatus] with #HRSM',
             '· inext', '  iexists _', '  iframe HraftStatus'] +
            sum([errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', x, m,
                             '{Hd:go_etcd_io.etcd.server.v3.etcdserver.errors}', t)
                 for (x, m, t) in _SRV_ERRS], []) +
            ['ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.server.v3.auth}',
             'icases Hai with ⟨-, -, -, #HAOR0, -⟩',
             'ihave #LAOR : (EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.auth.ErrAuthOldRevision : IProp GF) $$ []',
             '· unfold EtcdGrove.errVarLeaf EtcdGrove.errLeaf EtcdGrove.errMsgOk',
             '  iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HAOR0',
             '  iexact HAOR0',
             'ihave Hri : (go_etcd_io.raft.v3.isInitialized : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ {Hd:go_etcd_io.raft.v3}',
             'iunfold go_etcd_io.raft.v3.isInitialized at Hri',
             'icases Hri with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, Hrr⟩',
             'iNamed Hrr',
             'ihave #LPD := EtcdGrove.errVarLeaf_of_newVar _ _ $$ ErrPropDroppedNew',
             'ihave Hti : (go_etcd_io.etcd.pkg.v3.traceutil.traceutilInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.pkg.v3.traceutil}',
             'icases Hti with ⟨%tr, #HTr⟩',
             'ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []',
             '· iPkgInit',
             'ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hsch',
             'icases Hsi with ⟨-, -, -, -, #HAB, -, -⟩'] +
            FIN_PRE[:6] +
            ['imodintro', 'unfold srvInit srvRaftInit srvReqInit srvApplyLoopInit srvErrVars', 'iframe #',
             'ipureintro', 'first | exact fun x => EtcdGrove.errorString_errLeaf x | exact fun x => EtcdGrove.errorString_leaf x']),
)
for _x, _k, _l in _SRV_VECS:
    promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver'], _x, _k, _l)
# (prove-errinits, 2026-11-19) its other metrics, `recommendedMaxRequestBytesString`
# (`humanize.Bytes`, over its spec) translated (until then `opaqueInitsOk`, which keeps
# `monitorVersionInterval`, which reads rafthttp's `ConnWriteTimeout`, not in rafthttp's fact, and
# `_`, an interface conversion `wp_auto` does not step)
_SV = SPECIAL['go_etcd_io.etcd.server.v3.etcdserver']
for _x, _k, _l in [('learnerPromoteFailed', 'Counter', ['Reason']), ('currentVersion', 'Gauge', ['server_version']),
                   ('currentGoVersion', 'Gauge', ['server_go_version'])]:
    promvec(_SV, _x, _k, _l)
_SV['alloc_types'].update({'learnerPromoteSucceed': 'GoInterface', 'fdUsed': 'GoInterface',
                           'fdLimit': 'GoInterface', 'recommendedMaxRequestBytesString': 'GoString'})
_SV['before'].update({'learnerPromoteSucceed': metric_steps('learnerPromoteSucceed', 'counter'),
                      # (prove-ps2-srvgoroutines, 2026-11-24) in the fact (`srvApplyLoopInit`'s last two):
                      # `monitorFileDescriptor`'s gauges (`Set`)
                      'fdUsed': metric_steps_to('fdUsed', 'gauge', 'go_etcd_io.etcd.server.v3.etcdserver.gaugeSetSpec'),
                      'fdLimit': metric_steps_to('fdLimit', 'gauge', 'go_etcd_io.etcd.server.v3.etcdserver.gaugeSetSpec'),
                      'recommendedMaxRequestBytesString': ['try wp_auto',
                          'wp_apply EtcdGrove.go_humanize.Bytes.wp_proof $$ {Hd:github_com.dustin.go_humanize} as %sRMR -',
                          'try wp_auto']})
_SV['imports'] = _SV['imports'] + ['Proof.github_com.dustin.go_humanize.Bytes']
# (prove-etcdserver, 2026-11-20) `monitorVersionInterval = rafthttp.ConnWriteTimeout - time.Second`,
# translated: `ConnWriteTimeout` from rafthttp's fact (its last part); and `_`, the adapter's
# interface conversion (`serverversion.Server` translated): `opaqueInitsOk` is empty
_SV['alloc_types']['monitorVersionInterval'] = 'w64'
_SV['before']['monitorVersionInterval'] = [
    'ihave Hrhi : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []',
    '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp}',
    'icases Hrhi with ⟨' + '-, ' * 34 + '#HCWT⟩',
    'try wp_auto']
_SV['doc'] += """ (prove-errinits, 2026-11-19) Its other metrics (`learnerPromoteFailed`,
`learnerPromoteSucceed`, `currentVersion`, `currentGoVersion`, `fdUsed`, `fdLimit`),
and `recommendedMaxRequestBytesString` (`humanize.Bytes`, over its spec) are translated too;
(prove-etcdserver, 2026-11-20) and `monitorVersionInterval` (`rafthttp.ConnWriteTimeout - time.Second`,
from rafthttp's fact) and `_` (`var _ serverversion.Server = ...`, a conversion): no untranslated
initializer is left."""

_V_ERRS = ['ErrGRPCEmptyKey', 'ErrGRPCInvalidSortOption', 'ErrGRPCValueProvided', 'ErrGRPCLeaseProvided',
           'ErrGRPCTooManyOps', 'ErrGRPCDuplicateKey', 'ErrGRPCKeyNotFound', 'ErrGRPCNoSpace',
           'ErrGRPCNotCapable', 'ErrGRPCInvalidClientAPIVersion', 'ErrGRPCNoLeader']
_V_HIST = ['watchSendLoopWatchStreamDuration', 'watchSendLoopWatchStreamDurationPerEvent',
           'watchSendLoopControlStreamDuration', 'watchSendLoopProgressDuration']
_V_WERRS = ['ErrGRPCInvalidAuthToken', 'ErrGRPCAuthOldRevision', 'ErrGRPCUserEmpty',
            'ErrGRPCPermissionDenied', 'ErrGRPCWatchCanceled']
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc'] = dict(
    doc="""Its fact (`v3rpcInit`, `Base.lean`): its error map `toGRPCErrorMap` and counter vector
`clientRequests` with its label names (the map untranslated: the trust-boundary axiom
`toGRPCErrorMap_init`; the vector translated, over `NewCounterVec`'s spec, until 2026-11-19 an
axiom `<X>_init`), `metricsServerLock` (an
unlocked mutex guarding `metricsServerCached`, `nil`: `metricsVars`), `rpctypes`' errors and
metadata keys and `etcdserverpb`'s sort-name maps and six `ServiceDesc`s (`svcDescsOk`, from their
facts), and `context.Canceled` a
pointer error (`EtcdGrove.ContextReadErrs.errs_strong`, from Perennial's `context.isInit`).
Its precondition has the registration rights of the metric
names of its import closure (`namesFree initNames`, decision D16; mustreg, 2026-11-20), which it
passes on to its imports' initializers.
(D19j, 2026-10-18) And what `watch.go` reads but `io.EOF` (`watchPkgVars`): `auth`'s and `mvcc`'s
errors (from their facts), `rpctypes`' (from its), its metrics `streamFailures` (with its label
names; translated, over `NewCounterVec`'s spec, until 2026-11-19 an axiom) and the four
`watchSendLoop*` histograms (translated, over prometheus's `NewHistogram` and `ExponentialBuckets`
specs; until 2026-11-19 the trust-boundary axioms `<X>_init`),
`traceutil.Tracer`, and `progressReportIntervalMu`, initialized here, guarding
`progressReportInterval` (`10 * time.Minute`: `intervalP`).""",
    imports=['Perennial.Proof.sync.RWMutexGuard'] + PROM_CTORS,
    before={x: metric_steps(x, 'hist') + [f'iunfold EtcdGrove.prometheus.metric.histSpec at C{x}'] for x in _V_HIST},
    alloc_types={**{x: 'GoInterface' for x in _V_HIST},
                 'progressReportIntervalMu': '_root_.Perennial.sync.RWMutex',
                 'progressReportInterval': 'w64', 'metricsServerCached': 'Loc',
                 'metricsServerLock': '_root_.Perennial.sync.Mutex'},
    custom={
        'toGRPCErrorMap': dict(
            doc='/-- `toGRPCErrorMap = map[error]error{...}` (`util.go`): a map whose values are `rpctypes.ErrGRPC*` errors (and `ErrTooManyRequests`, `ErrMemberNotEnoughStarted`), non-nil; mvcc\'s `ErrFutureRev` and `ErrCompacted` (the values of their cells) map to `ErrGRPCFutureRev` and `ErrGRPCCompacted`, and no other key maps to an error with one of those two descriptions, nor has one itself (k8s etcd3 7c: `grpcErrMapOk`), and the two have their `errors.New` descriptions (`kvstore.go:38-39`; k8s etcd3 7c-2 part 2, G2-a); every value is one grpc\'s `status.FromError` accepts (`statusErrOk`; k8s etcd3 7c, HS-6: the `status.Error`s and the two `EtcdError`s, leaves with only `Code` and `Error`); the value of each variable of `grpcErrKeyGlobals` (the literal\'s 53 keys) is a key (k8s etcd3 7c-2 part 2, S2: stated as a persistent wand on the variable\'s persisted cell, asserting no cell of another package). -/',
            post='∃ (mp : Loc) (M : GMap GoInterface GoInterface) (kf kc : GoInterface), globalAddr toGRPCErrorMap ↦ mp ∗ mp ↦$□ M ∗ globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ kf ∗ globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ kc ∗ □ (∀ (k v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗ □ (∀ (g : GoString) (k : GoInterface), ⌜g ∈ grpcErrKeyGlobals⌝ → globalAddr g ↦□ k -∗ ⌜(M !! k).isSome⌝) ∗ grpcErrMapOk M kf kc',
            pat='⟨%mp@, %M@, %kf@, %kc@, H@, #S@, #F@, #C@, #V@, #K@, #P@⟩'),
    },
    finish=(['ipersist HtoGRPCErrorMap', 'ipersist HclientRequests',
             'ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd22',
             'icases Hri with ⟨-, ⟨%eRCP, #RCPa, #RCPs, -⟩, -, -, -, -, -, -, ⟨%eNSL, #HNSL, -, -, #SNSL⟩, -, -, ' +
             ', '.join(f'#V{i}' for i in range(len(_V_ERRS) + 3)) + ', ' +
             ', '.join(f'#RW{i}' for i in range(len(_V_WERRS))) + ', -⟩',
             'ihave Hpi : (go_etcd_io.etcd.cache.v3.etcdserverpbInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd2',
             'icases Hpi with ⟨#HSO, #HST, -, #HDescs⟩',
             'ihave ⟨#HCL, -⟩ := EtcdGrove.ContextReadErrs.errs_strong $$ Hd1', "-- (incomingof Part B) the context errors are keys of the map, so neither read error's description", 'ihave #HCD : (ctxErrDescs : IProp GF) $$ []', '· ihave #Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []', '  · iapply _root_.Perennial.context.isInit_access $$ Hd1', '  iNamed Hci', '  icases HCanceledCell with ⟨%xc, #Hxc, -⟩', '  unfold ctxErrDescs', '  isplitl []', '  · iexists _; iframe Hxc', '    ihave %hs := KtoGRPCErrorMap $$ %_root_.Perennial.context.Canceled %_ %(by mem_tac) Hxc', '    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs', '    ihave ⟨%m1, #D1, %h1⟩ := grpcErrMapOk_key $$ PtoGRPCErrorMap %hv', '    iexists m1; iframe D1; ipureintro; exact h1', '  · iexists _; iframe HDeadlineExceededTy', '    ihave %hs := KtoGRPCErrorMap $$ %_root_.Perennial.context.DeadlineExceeded %_ %(by mem_tac)', '      HDeadlineExceededTy', '    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs', '    ihave ⟨%m1, #D1, %h1⟩ := grpcErrMapOk_key $$ PtoGRPCErrorMap %hv', '    iexists m1; iframe D1; ipureintro; exact h1',
             'ihave #HCP : (∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok e ∗',
             '    ⌜_root_.Perennial.errors.IsPointerError e⌝ : IProp GF) $$ []',
             '· iunfold EtcdGrove.errVarLeaf at HCL', '  icases HCL with ⟨%e, #He, %Hl, -⟩',
             '  iexists e', '  iframe He', '  ipureintro; exact Hl.1',
             '-- `getServerMetrics`\' lock and what it guards (`metricsServerCached`, `nil`)',
             '-- (prom-registry, 2026-11-22) and, until it registers, the rights to the server metrics\' IDs',
             '-- (`grpcKeys`, this package\'s `regKeys`) with prometheus\'s fact at their registry name',
             'imod sync.init_Mutex EtcdGrove.v3rpc.metricsP ⊤ EtcdGrove.v3rpc.metricsMu $$ HmetricsServerLock [HmetricsServerCached HRK] with #HMV',
             '· inext', '  unfold EtcdGrove.v3rpc.metricsP', '  iexists _', '  iframe HmetricsServerCached',
             '  ileft', '  isplitr', '  · ipureintro; rfl', '  iexists promreg_gs',
             '  iunfold _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.regKeys at HRK',
             '  iframe HRK', '  iexact {Hd:github_com.prometheus.client_golang.prometheus}',
             '-- the six `ServiceDesc`s, from `etcdserverpb`\'s fact',
             'icases HDescs with ⟨#HK, ⟨%wm, %ws, #HW, %HWp⟩, #HL, #HC, #HA, #HM, -⟩',
             'obtain ⟨rfl, HWp, HWc⟩ := HWp',
             'ihave #HSD : (EtcdGrove.v3rpc.svcDescsOk : IProp GF) $$ []',
             '· unfold EtcdGrove.v3rpc.svcDescsOk EtcdGrove.v3rpc.handlerTy EtcdGrove.v3rpc.kvDescMethods EtcdGrove.v3rpc.authDescMethods EtcdGrove.v3rpc.leaseDescMethods EtcdGrove.v3rpc.clusterDescMethods EtcdGrove.v3rpc.maintDescMethods',
            
            
             '  iframe HK HL HC HA HM',
             '  iexists ws',
             '  iframe HW',
             '  ipureintro; exact ⟨HWp, HWc⟩',
             '-- (D19j) what `watch.go` reads but `io.EOF` (`watchPkgVars`): `auth`\'s errors',
             'ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd3',
             'icases Hai with ⟨#AUE, -, #APD, #AAO, #AIA, -⟩',
             'ihave #WUE := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ AUE',
             'ihave #WPD := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ APD',
             'ihave #WAO := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ AAO',
             'ihave #WIA := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ AIA',
             '-- mvcc\'s',
             'ihave Hmi : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd37',
             'icases Hmi with ⟨' + '-, ' * 32 + '#NEWR, #NWDI, -⟩',
             'ihave #WEWR := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NEWR',
             'ihave #WWDI := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NWDI',
             '-- `rpctypes`\'',
             'ihave #RCP : iprop(∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ↦□ GoInterface.ok e ∗',
             '    go_etcd_io.etcd.cache.v3.errorStringSpec e) $$ []',
             '· iexists eRCP; iframe #',
             'ihave #MCP := EtcdGrove.v3rpc.msgErrVar_of_spec _ $$ RCP'] +
            [f'ihave #MRW{i} := EtcdGrove.v3rpc.{"statusMsgErrVar" if x == "ErrGRPCWatchCanceled" else "msgErrVar"}_of_spec _ $$ RW{i}' for i, x in enumerate(_V_WERRS)] +
            ['-- the metrics',
             'ipersist HstreamFailures'] +
            [f'ipersist H{x}' for x in _V_HIST] +
            [f'ihave #WH{i} : (EtcdGrove.v3rpc.histVar {x} : IProp GF) $$ []\n  · iunfold EtcdGrove.v3rpc.histVar; iexists _; iframe H{x} C{x}'
             for i, x in enumerate(_V_HIST)] +
            ['-- `traceutil.Tracer`',
             'ihave Hti : (go_etcd_io.etcd.pkg.v3.traceutil.traceutilInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ {Hd:go_etcd_io.etcd.pkg.v3.traceutil}',
             'icases Hti with #HTR',
             '-- the progress interval\'s lock and what it guards (`progressReportInterval`, `10 * time.Minute`)',
             'imod (sync.init_RWMutex EtcdGrove.v3rpc.intervalP EtcdGrove.v3rpc.intervalMu (E := ⊤)) $$ [HprogressReportInterval] HprogressReportIntervalMu with HIS',
             '· inext',
             '  unfold EtcdGrove.v3rpc.intervalP',
             '  iexists _',
             '  iframe HprogressReportInterval',
             '  ipureintro',
             '  first | decide | (simp [_root_.Perennial.time.Minute]; decide) | word',
             'ihave ⟨HIS, #HIG⟩ := sync.ownRWMutex_slots_guard _ _ $$ HIS',
             '-- (2026-10-20, watchkv) its reader slots pooled, for the watch streams\' send loops',
             'imod (EtcdGrove.v3rpc.intervalPool_alloc ⊤) $$ [HIS] with #HIP',
             '· iframe HIG; iexact HIS'] +
            FIN_PRE[:6] +
            ['imodintro', 'unfold v3rpcInit EtcdGrove.v3rpc.watchPkgVars grpcErrMap checkErrVars sortNameMaps ctxCanceledPtr ctxErrDescs interceptorVars errVarSet EtcdGrove.v3rpc.metricsVars',
             'iframe #']),
)
promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc'], 'clientRequests', 'Counter',
        ['type', 'client_api_version'])
# (D19j, 2026-10-18) the watch server's metrics (`metrics.go`)
promvec(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc'], 'streamFailures', 'Counter', ['Type', 'API'])


# Item 8 (2026-10-17): the read package, its `init()`'s `MustRegister` given the registration
# rights (`PRE_RES`; decision D16; until mustreg, 2026-11-20, `EtcdGrove.read.readRegPerm`).
_RD = 'go_etcd_io.etcd.server.v3.etcdserver.read'
_RD_CTX_PRE = [
    'section ctxFacts',
    'variable [GooseExts] [GooseSemantics] [GooseInterp]',
    'variable [go_gctx : GoGlobalContext]',
    'variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]',
    'variable [sem : go.Semantics]',
    '',
    '/-- **`context.Canceled` and `context.DeadlineExceeded` as Go defines them** (item 8, 2026-10-17;',
    'a premise, the class `ContextReadErrs`, until ctx-leaf-fix, 2026-11-25): `Canceled =',
    'errors.New("context canceled")`, a leaf pointer error without `Is` or `GRPCStatus` whose `Error()`',
    'returns its message, and `DeadlineExceeded = deadlineExceededError{}`, a leaf non-pointer error',
    "without `Is` or `GRPCStatus`, a key of `togRPCError`'s map (`errKeyOk`), whose `Error()` returns",
    "(`context.go`: its methods are `Error`, `Timeout` and `Temporary`). From Perennial's",
    "`context.isInit` (`\"#HCanceledCell\"`, `\"#HDeadlineExceededTy\"`) and the method sets goose emits.",
    "The premise had become unsatisfiable with Perennial's P8c (`DeadlineExceeded`'s value a",
    '`SafeMapKey`, which no non-pointer is): `notes/axiom-review/ctx-readerrs-vacuity.md`. -/',
    'theorem EtcdGrove.ContextReadErrs.errs [ctx_sem : _root_.Perennial.context.Assumptions]',
    '    [_root_.Perennial.errors.Assumptions] :',
    '    isPkgInit (PROP := IProp GF) pkg_id.context ⊢',
    '      EtcdGrove.errVarLeafW _root_.Perennial.context.Canceled ∗',
    '        go_etcd_io.etcd.server.v3.etcdserver.read.ctxDeadlineLeafW := by',
    '  iintro #Hp',
    '  ihave Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []',
    '  · iapply _root_.Perennial.context.isInit_access $$ Hp',
    '  iNamed Hci',
    '  icases HCanceledCell with ⟨%x, #Hx, #Hs⟩',
    '  isplitl',
    '  · iunfold EtcdGrove.errVarLeafW',
    '    iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩',
    '    iframe Hx',
    '    isplitr',
    '    · ipureintro',
    '      have h := EtcdGrove.errorString_errLeaf x',
    '      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩',
    '    · iunfold EtcdGrove.errMsgOk',
    '      iexists go!"context canceled"',
    '      iintro !> %Φ HΦ',
    '      rw [method_unfold]',
    '      wp_auto',
    '      iexact HΦ',
    '  · have h := fun m => go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) m',
    '    have hG := h go!"GRPCStatus"',
    '    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hG',
    '    have hl := EtcdGrove.deadlineExceededError_leaf (ctx_sem := ctx_sem)',
    '      (#(zero_val _root_.Perennial.context.deadlineExceededError) : val)',
    '    iexists ⟨_root_.Perennial.context.deadlineExceededError.ty,',
    '      #(zero_val _root_.Perennial.context.deadlineExceededError)⟩',
    '    iframe HDeadlineExceededTy',
    '    isplitr',
    '    · ipureintro',
    '      exact ⟨hl.1, hl.2, _root_.Perennial.context.deadlineExceededError_ne_ptr,',
    '        Or.inr (Or.inr (Or.inl rfl)), hG⟩',
    '    · iunfold EtcdGrove.errMsgOk',
    '      iexists go!"context deadline exceeded"',
    '      iintro !> %Φ HΦ',
    '      wp_method_call',
    '      unfold _root_.Perennial.context.deadlineExceededError.Error.impl',
    '      wp_auto',
    '      iexact HΦ',
    '',
    '/-- `ContextReadErrs.errs` with the two errors\' `Format` facts (premise-fixes-4: `errVarLeaf`,',
    '`ctxDeadlineLeaf`): neither has a `Format` method, from Perennial\'s `context.isInit` (`Canceled`\'s',
    'value is a `*errors.errorString`, `EtcdGrove.ErrorStringLeaf`; `DeadlineExceeded`\'s a',
    '`deadlineExceededError`, whose method set goose emits). -/',
    'theorem EtcdGrove.ContextReadErrs.errs_strong',
    '    [_root_.Perennial.context.Assumptions] [_root_.Perennial.errors.Assumptions] :',
    '    isPkgInit (PROP := IProp GF) pkg_id.context ⊢',
    '      EtcdGrove.errVarLeaf _root_.Perennial.context.Canceled ∗',
    '        go_etcd_io.etcd.server.v3.etcdserver.read.ctxDeadlineLeaf := by',
    '  iintro #Hp',
    '  ihave ⟨#HC, #HD⟩ := EtcdGrove.ContextReadErrs.errs $$ Hp',
    '  ihave Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []',
    '  · iapply _root_.Perennial.context.isInit_access $$ Hp',
    '  iNamed Hci',
    '  icases HCanceledCell with ⟨%x, #Hx, -⟩',
    '  iunfold EtcdGrove.errVarLeafW at HC',
    '  icases HC with ⟨%e, #He, %Hl, #Hm⟩',
    '  icombine He Hx gives %Heq',
    '  icases HD with ⟨%d, #Hd, %Hdl, #Hdm⟩',
    '  icombine Hd HDeadlineExceededTy gives %Heq2',
    '  have hF : methodSet e.ty !! go!"Format" = none := by',
    '    cases Heq; exact EtcdGrove.ErrorStringLeaf.noFormat',
    '  have hE : methodSet e.ty !! go!"Error" = some (go.signature.Signature [] false [go.string]) := by',
    '    cases Heq; exact EtcdGrove.ErrorStringLeaf.errorSig',
    '  have hF2 : methodSet d.ty !! go!"Format" = none := by',
    '    cases Heq2',
    '    have h := go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Format"',
    '    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h',
    '    exact h',
    '  have hE2 : methodSet d.ty !! go!"Error" = some (go.signature.Signature [] false [go.string]) := by',
    '    cases Heq2',
    '    have h := go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Error"',
    '    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h',
    '    exact h',
    '  isplitl',
    '  · iunfold EtcdGrove.errVarLeaf',
    '    iexists e; iframe He Hm',
    '    ipureintro; exact ⟨Hl.1, Hl.2.1, Hl.2.2.1, Hl.2.2.2, hF, hE⟩',
    '  · iexists d; iframe Hd Hdm',
    '    ipureintro; exact ⟨Hdl.1, Hdl.2.1, Hdl.2.2.1, Hdl.2.2.2.1, Hdl.2.2.2.2, hF2, hE2⟩',
    '',
    'end ctxFacts',
    '']
_RD_ERRS = [('ErrStopped', 'etcdserver: server stopped', 'STP'),
            ('ErrLeaderChanged', 'etcdserver: leader changed', 'LCH'),
            ('ErrTimeout', 'etcdserver: request timed out', 'TMO')]
_RD_PROM = 'EtcdGrove.prometheus'
SPECIAL[_RD] = dict(
    doc="""Its fact (`readInit`, `BaseApply.lean`): its counters `slowReadIndex` and `readIndexFailed`
(`metrics.go`, translated: `prometheus.NewCounter` of a `CounterOpts` literal, the trust-boundary
axiom `NewCounter.wp_proof`), `readIndexRetryTime`,
the error variables it returns or compares with, from their packages' facts (`etcdserver/errors`'
and raft's, leaf errors by `EtcdGrove.ErrorStringLeaf`), and `context`'s
(`EtcdGrove.ContextReadErrs.errs`, from Perennial's `context.isInit`; a premise until ctx-leaf-fix,
2026-11-25). Its translated
`init()` registers the two counters (`prometheus.MustRegister`, the trust-boundary axiom
`MustRegister.wp_proof`), which takes the right to register each name: the precondition
`namesFree regNames` (decision D16; until mustreg, 2026-11-20, `EtcdGrove.read.readRegPerm`).""",
    imports=['Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Metrics',
             'Proof.github_com.prometheus.client_golang.prometheus.NewCounter',
             'Proof.github_com.prometheus.client_golang.prometheus.MustRegister',
             'Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init'],
    pre=_RD_CTX_PRE,
    alloc_types={'slowReadIndex': 'GoInterface', 'readIndexFailed': 'GoInterface',
                 'readIndexRetryTime': '_root_.Perennial.time.Duration'},
    before={'$inits': [
        'wp_apply EtcdGrove.prometheus.NewCounter.wp_proof _ _ _ _ _ rfl (by decide) as %c1 ⟨#C1, #N1⟩',
        'try wp_auto',
        'wp_apply EtcdGrove.prometheus.NewCounter.wp_proof _ _ _ _ _ rfl (by decide) as %c2 ⟨#C2, #N2⟩',
        'try wp_auto']},
    finish=(['ipersist HslowReadIndex', 'ipersist HreadIndexFailed', 'ipersist HreadIndexRetryTime'] +
            sum([errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', x, m,
                             '{Hd:go_etcd_io.etcd.server.v3.etcdserver.errors}', tg)
                 for (x, m, tg) in _RD_ERRS], []) +
            ['ihave Hri : (go_etcd_io.raft.v3.isInitialized : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ {Hd:go_etcd_io.raft.v3}',
             'iunfold go_etcd_io.raft.v3.isInitialized at Hri',
             'icases Hri with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, Hrr⟩',
             'iNamed Hrr',
             'ihave #LRS := EtcdGrove.errVarLeaf_of_newVar _ _ $$ ErrStoppedNew',
             'ihave ⟨#LCC, #LDL⟩ := EtcdGrove.ContextReadErrs.errs_strong $$ {Hd:context}'] +
            FIN_PRE[:6] +
            ['imodintro', 'unfold readInit', 'iframe #']),
)

RAFT_INIT = {'go_etcd_io.raft.v3', 'go_etcd_io.raft.v3.quorum', 'go_etcd_io.raft.v3.tracker',
             'go_etcd_io.raft.v3.confchange', 'go_etcd_io.raft.v3.raftpb',
             'google_golang_org.protobuf.proto'}
# (`os` was here until 2026-11-03: Perennial b3e996d84 translates some of its initializers, and bbolt
# imports it too; its `wp_initialize'` is generated, `Proof/os/Init.lean`, `SPECIAL['os']`.)
# (`strconv` was here until Perennial translated it, 24bef275e: its `wp_initialize'` is Perennial's.)

# (prove-errinits, 2026-11-19) the scalar metrics and constants left untranslated in the
# `opaqueInitsOk` lists of lease, backend, v3rpc, snap and storage: translated, the metrics over
# prometheus's constructor specs (`metric_steps`), `ErrNoDBSnapshot` an `errors.New` call, storage's
# quota strings `humanize.Bytes` calls (over its spec).
def _more_metrics(cfg, metrics, consts=()):
    cfg.setdefault('alloc_types', {}).update({x: 'GoInterface' for x, _ in metrics})
    cfg['alloc_types'].update({x: 'w64' for x in consts})
    cfg.setdefault('before', {}).update({x: metric_steps(x, k) for x, k in metrics})
    imps = cfg.setdefault('imports', [])
    imps += [m for m in PROM_CTORS if m not in imps]
    return cfg

_more_metrics(SPECIAL['go_etcd_io.etcd.server.v3.lease'], [],
              ['defaultLeaseRevokeRate', 'leaseCheckpointRate', 'defaultLeaseCheckpointInterval',
               'maxLeaseCheckpointBatchSize', 'defaultExpiredleaseRetryInterval'])
# (prove-ps2-renew, 2026-11-21) `leaseRenewed` is in the fact now (`Renew`'s `Inc()`): its steps
# (with the `counterSpec` conversion) are in the package's `before` above
SPECIAL['go_etcd_io.etcd.server.v3.lease']['doc'] = SPECIAL['go_etcd_io.etcd.server.v3.lease']['doc'].replace(
    """axioms `<X>_init`); `opaqueInitsOk` states the
other untranslated initializers run.""", """axioms `<X>_init`). Its other variables' initializers are translated too (2026-11-19, until then
`opaqueInitsOk`): the rate and interval constants (`lessor.go`).""")
_more_metrics(SPECIAL['go_etcd_io.etcd.server.v3.storage.backend'],
              [('defragSec', 'hist'), ('defragBlockingSec', 'hist'), ('isDefragActive', 'gauge')])
# (backend-snapshot B4, 2026-11-21) `snapshotTransferSec`'s histogram is a fact too: `Snapshot`'s
# goroutine observes it.
SPECIAL['go_etcd_io.etcd.server.v3.storage.backend']['alloc_types']['snapshotTransferSec'] = 'GoInterface'
SPECIAL['go_etcd_io.etcd.server.v3.storage.backend']['before']['snapshotTransferSec'] = metric_steps_to(
    'snapshotTransferSec', 'hist', 'go_etcd_io.etcd.server.v3.storage.backend.histSpec')
SPECIAL['go_etcd_io.etcd.server.v3.storage.backend']['doc'] = SPECIAL['go_etcd_io.etcd.server.v3.storage.backend']['doc'].replace(
    """trust-boundary axioms `<X>_init`), `opaqueInitsOk` states the others.""",
    """trust-boundary axioms `<X>_init`), and so are (2026-11-19, until then `opaqueInitsOk`) the others,
`defragSec`, `defragBlockingSec` and the gauge `isDefragActive`; (2026-11-21) `snapshotTransferSec`'s
histogram, which `Snapshot`'s goroutine observes, is in the fact, and so is `minSnapshotWarningTimeout`,
the floor of its ticker's interval.""")
_more_metrics(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc'],
              [('sentBytes', 'counter'), ('receivedBytes', 'counter')])
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.snap'] = newvars_cfg(_more_metrics(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (2026-11-19; until then untranslated, `opaqueInitsOk`): `ErrNoDBSnapshot`
(`db.go`, an `errors.New` call) and the histograms of `metrics.go` (over prometheus's `NewHistogram`
and `ExponentialBuckets` specs); its untranslated `init` function, which the trust-boundary axiom
`initFuncsOk` says returns.'''),
    [(x, 'hist') for x in ['snapMarshallingSec', 'snapSaveSec', 'snapFsyncSec', 'snapDBSaveSec',
                           'snapDBFsyncSec']]), ['ErrNoDBSnapshot'])
SPECIAL['go_etcd_io.etcd.server.v3.storage'] = _more_metrics(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (`quota.go`, 2026-11-19; until then untranslated, `opaqueInitsOk`): the
gauge `quotaBackendBytes` (over prometheus's `NewGauge` spec) and the strings `DefaultQuotaSize` and
`maxQuotaSize` (`humanize.Bytes` of the constant quotas, over its spec); and its untranslated `init`
function, which the trust-boundary axiom `initFuncsOk` says returns.''',
    imports=['Proof.github_com.dustin.go_humanize.Bytes'],
    alloc_types={'DefaultQuotaSize': 'GoString', 'maxQuotaSize': 'GoString'},
    before={x: ['try wp_auto',
                f'wp_apply EtcdGrove.go_humanize.Bytes.wp_proof $$ {{Hd:github_com.dustin.go_humanize}} as %s{x} -',
                'try wp_auto'] for x in ['DefaultQuotaSize', 'maxQuotaSize']}),
    [('quotaBackendBytes', 'gauge')])


# (prove-smallinits, 2026-11-20) small `opaqueInitsOk`/`initFuncsOk` lists translated: their
# initializers are `errors.New` calls, map and slice literals, scalar literals and (txn) metric vectors.
SPECIAL['path'] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates `ErrBadPattern` and runs
its translated initializer, an `errors.New` call (prove-smallinits, 2026-11-20; until then the
trust-boundary axiom `opaqueInitsOk`).'''), ['ErrBadPattern'])
SPECIAL['github_com.xiang90.probing'] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers: `ErrNotFound`, `ErrExist` (`errors.New` calls) and `α` (a float
constant) (prove-smallinits, 2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).''',
    alloc_types={'«α»': 'w64'}), ['ErrNotFound', 'ErrExist'])
_T = SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.txn']
_T['doc'] = _T['doc'].replace("`opaqueInitsOk` states its other untranslated\ninitializers run.",
    "Its histogram vectors `applySec` and\n`rangeSec` are translated too (`NewHistogramVec`'s spec; prove-smallinits, 2026-11-20, until then\n`opaqueInitsOk`).")
promvec(_T, 'applySec', 'Histogram', ['version', 'op', 'success'])
promvec(_T, 'rangeSec', 'Histogram', ['success'])
# (prove-etcdserver, 2026-11-20) the two vectors are in the fact (`txnInit`), for the observers
_T['finish'][0:0] = ['ipersist HapplySec', 'ipersist HrangeSec']
_T['doc'] = _T['doc'].replace("`opaqueInitsOk`).", "`opaqueInitsOk`), and in its fact with their label\nnames (prove-etcdserver, 2026-11-20: `metrics.go`'s observers, translated, read them).")

def map_lit_steps(h, K, V, kt, vt, n):
    """A map literal of `n` entries (`map[kt]vt{...}`, Lean types `K`, `V`): made (`%m<h> <h>`), then its
    entries inserted."""
    return ['try wp_auto',
            f'wp_apply (wp_map_make1 (K := {K}) (V := {V}) {kt} {vt}) as %m{h} {h}',
            'try wp_auto'] + [f'wp_apply (wp_mapInsert (K := {K}) (V := {V}) {kt}) $$ {h} as {h}', 'try wp_auto'] * n

_OC = 'go_opentelemetry_io.otel.codes'
SPECIAL[_OC] = dict(
    doc='''Its fact is `True`. Its initializer allocates its variables and runs their translated
initializers, the map literals `codeToStr` and `strToCode` (prove-smallinits, 2026-11-20; until then
the trust-boundary axiom `opaqueInitsOk`).''',
    alloc_types={'codeToStr': 'Loc', 'strToCode': 'Loc'},
    before={'codeToStr': map_lit_steps('Hcs', 'w32', 'GoString', f'{_OC}.Code.ty', 'go.string', 3),
            'strToCode': map_lit_steps('Hsc', 'GoString', 'w32', 'go.string', f'{_OC}.Code.ty', 3)},
)
# (phase7-inits, 2026-11-25, notes/phase7-endstate.md §4; the mechanism of phase 7 S2 core's
# `FromOutgoingContextRaw`, 2026-11-23, for every hook) grpc's `internal`: names only but its hook
# variables, which the translated `init`s of `metadata`, `codes` and grpc set and no translated code
# reads. Its fact (`internalInit`, `cache/v3/Base.lean`) is the hook cells' invariants
# (`grpc/internal/Hooks.lean`); a package initializer's store goes through them, lending its package state.
_GI = 'google_golang_org.grpc.internal'
_GI_ANY = ['FromOutgoingContextRaw', 'CanonicalString', 'AddGlobalDialOptions',
           'AddGlobalPerTargetDialOptions', 'JoinDialOptions', 'DisableGlobalDialOptions',
           'AcceptCompressors', 'GetServerCredentials', 'IsRegisteredMethod', 'ServerFromContext',
           'AddGlobalServerOptions', 'JoinServerOptions', 'XDSFilterWrapperOption',
           'RegisterClientHealthCheckListener']
_GI_FUNC = ['ClearGlobalDialOptions', 'ClearGlobalPerTargetDialOptions', 'ClearGlobalServerOptions',
            'HealthCheckFunc', 'BalancerUnregister']
_GI_BASE = '_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal'


def hook_fact_steps():
    """`internal`'s fact, from the importer's facts (an `init` storing in its hooks)."""
    return [f'ihave #Hfi : ({_GI_BASE}.internalInit (hG := hG) : IProp GF) $$ []',
            '· iapply isPkgInit_access $$ {Hd:google_golang_org.grpc.internal}']


def hook_store_steps(names):
    """A translated `init`'s stores in `internal`'s hooks `names`, in order."""
    out = []
    for n in names:
        assert n in _GI_ANY + _GI_FUNC, n
        kind, lst = ('Any', 'hooksAny') if n in _GI_ANY else ('Func', 'hooksFunc')
        out += ['try wp_auto',
                f'wp_apply (EtcdGrove.grpcInternal.wp_store_hook{kind} (hG := hG) _root_.Perennial.{_GI}.{n}',
                f'    (by unfold {_GI_BASE}.{lst}; mem_tac) _ _ _) $$ [Hfi Hown] as Hown',
                '· iframe Hown Hfi']
    return out + ['try wp_auto']


def _hook_alloc_steps(V, names):
    return [f'imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := {V}) ⊤ _ _) $$ H{n} with #C{n}' for n in names]


SPECIAL[_GI] = dict(
    doc='''Its fact (`internalInit`, `cache/v3/Base.lean`): the invariants of its hook cells (`hookCell`),
which a package initializer holding its package state opens for a plain store (`grpc/internal/Hooks.lean`).
Its initializer allocates the hook variables that the translated `init`s of `metadata`, `codes` and grpc
set (`internal.go`, `experimental.go`: no initializers, so each holds `nil`) and puts each cell in its
invariant (phase7-inits, 2026-11-25; `FromOutgoingContextRaw` first in phase 7 S2 core, 2026-11-23); its
other variables with initializers are goose `[[skip]]`s (literals), the rest names only.''',
    alloc_types={**{n: 'GoInterface' for n in _GI_ANY}, **{n: 'GoFunc' for n in _GI_FUNC}},
    imports=['Proof.google_golang_org.grpc.internal.Hooks'],
    finish=_hook_alloc_steps('GoInterface', _GI_ANY) + _hook_alloc_steps('GoFunc', _GI_FUNC)
        + FIN_PRE[:6] + ['try imodintro',
                         f'unfold {_GI_BASE}.internalInit {_GI_BASE}.hooksAny {_GI_BASE}.hooksFunc',
                         f'simp only [{_GI_BASE}.hookCells]', 'iframe #', 'try (imodintro; itrivial)'],
)
_GC = 'google_golang_org.grpc.codes'
SPECIAL[_GC] = dict(
    doc='''Its fact is `True`. Its initializer allocates `strToCode`, initializes its import (grpc's
`internal`), runs its translated initializer, a map literal (prove-smallinits, 2026-11-20; until then the
trust-boundary axiom `opaqueInitsOk`), and its translated `init` function (phase7-inits, 2026-11-25; until
then the trust-boundary axiom `initFuncsOk`), which stores `canonicalString`, converted to `any`, in
`internal.CanonicalString`, another package's variable: through `internal`'s invariants, lending the
initializer's package state (`grpc/internal/Hooks.lean`, `wp_store_hookAny`).''',
    alloc_types={'strToCode': 'Loc'},
    before={'strToCode': map_lit_steps('Hsc', 'GoString', 'w32', 'go.string', f'{_GC}.Code.ty', 17)},
    imports=['Proof.google_golang_org.grpc.internal.Hooks'],
    after={'init.«0»': hook_fact_steps() + hook_store_steps(['CanonicalString'])},
)
_GM = 'google_golang_org.grpc.metadata'
SPECIAL[_GM] = dict(
    doc='''Its fact is `True`. Its initializer allocates `loggableMetadataKeys`, initializes its imports, runs
its variable's translated initializer, a map literal of the keys `MD.String` prints (prove-grpcext,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`), and its translated `init` function
(phase7-inits, 2026-11-25, first phase 7 S2 core; until then the trust-boundary axiom `initFuncsOk`),
which stores `fromOutgoingContextRaw`, converted to `any`, in `internal.FromOutgoingContextRaw`, another
package's variable: through `internal`'s invariants, lending the initializer's package state
(`grpc/internal/Hooks.lean`, `wp_store_hookAny`).''',
    alloc_types={'loggableMetadataKeys': 'Loc'},
    before={'loggableMetadataKeys': map_lit_steps('Hlk', 'GoString', 'Bool', 'go.string', 'go.bool', 10)},
    imports=['Proof.google_golang_org.grpc.internal.Hooks'],
    after={'init.«0»': hook_fact_steps() + hook_store_steps(['FromOutgoingContextRaw'])},
)
# (phase7-inits, 2026-11-25) grpc's three `init`s translated (until then `initFuncsOk`): their stores of
# function values and closures in `internal`'s hooks, and the slices their closures append to
# (`globalDialOptions`, `globalPerTargetDialOptions`, `globalServerOptions`: no initializers, allocated)
_G = SPECIAL['google_golang_org.grpc']
_G['doc'] = _G['doc'].replace('''runs the
untranslated initializers of its other variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated `init`
functions, which the trust-boundary axiom `initFuncsOk` says return.''', '''runs the
untranslated initializers of its other variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its three translated `init`
functions (`dialoptions.go`, `rpc_util.go`, `server.go`; phase7-inits, 2026-11-25, until then the
trust-boundary axiom `initFuncsOk`), which store function values and closures in `internal`'s hook
variables, through `internal`'s invariants (`grpc/internal/Hooks.lean`); it allocates the slices the
closures append to (`globalDialOptions`, `globalPerTargetDialOptions`, `globalServerOptions`).''')
assert 'phase7-inits' in _G['doc']
_G.setdefault('alloc_types', {}).update({'globalDialOptions': 'GoSlice', 'globalPerTargetDialOptions': 'GoSlice',
                                         'globalServerOptions': 'GoSlice'})
_G.setdefault('imports', []).append('Proof.google_golang_org.grpc.internal.Hooks')
_G.setdefault('after', {}).update({
    'init.«0»': hook_fact_steps() + hook_store_steps(
        ['AddGlobalDialOptions', 'ClearGlobalDialOptions', 'AddGlobalPerTargetDialOptions',
         'ClearGlobalPerTargetDialOptions', 'JoinDialOptions', 'DisableGlobalDialOptions']),
    'init.«1»': hook_fact_steps() + hook_store_steps(['AcceptCompressors']),
    'init.«2»': hook_fact_steps() + hook_store_steps(
        ['GetServerCredentials', 'IsRegisteredMethod', 'ServerFromContext', 'AddGlobalServerOptions',
         'ClearGlobalServerOptions', 'JoinServerOptions', 'XDSFilterWrapperOption']),
})
_GL = 'google_golang_org.grpc.grpclog'
SPECIAL[_GL] = dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates `cache` and runs its
translated initializer, an empty map literal (prove-grpcext, 2026-11-20; until then the trust-boundary
axiom `opaqueInitsOk`), and its untranslated `init` function (`SetLoggerV2(newLoggerV2())`), which the
trust-boundary axiom `initFuncsOk` says returns.''',
    alloc_types={'cache': 'Loc'},
    before={'cache': map_lit_steps('Hc', 'GoString', 'Loc', 'go.string',
        f'(go.GoType.PointerType {_GL}.componentData.ty)', 0)},
)
# (phase7-inits batch 2, 2026-11-25) `grpclog`'s fact: `cache`'s map in an init-time invariant, for
# `Component` (translated), which the `logger`s of grpc, `credentials`, `health` and `connectivity` call
_GLB = '_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.grpclog'
SPECIAL[_GL]['doc'] = '''Its fact (`grpclogInit`, `cache/v3/Base.lean`; phase7-inits batch 2, 2026-11-25, until then
`True`): `cache` holds a map for good, whose contents are in an init-time invariant (`initInv`), for
`Component`, which package initializers call (`Spec/google_golang_org/grpc/grpclog/Component.lean`). Its
initializer initializes its imports, allocates `cache` and runs its translated initializer, an empty map
literal (prove-grpcext, 2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`), and its
untranslated `init` function (`SetLoggerV2(newLoggerV2())`), which the trust-boundary axiom
`initFuncsOk` says returns.'''
SPECIAL[_GL]['imports'] = ['Proof.google_golang_org.grpc.internal.Hooks']
SPECIAL[_GL]['finish'] = [
    'ipersist Hcache',
    f'imod (EtcdGrove.grpcInternal.initInv_alloc (hG := hG) {_GLB}.cacheN ⊤ iprop(∃ M : GMap GoString Loc, (mHc ↦$ M : IProp GF))) $$ [Hc] with ⟨%γC, #HC⟩',
    '· inext; iexists _; iexact Hc'] + FIN_PRE[:6] + [
    'try imodintro', f'unfold {_GLB}.grpclogInit', 'iexists mHc, γC', 'iframe #']


def logger_steps():
    """A `logger`'s translated initializer, `grpclog.Component(name)`: through `Component`'s proof."""
    return ['try wp_auto',
            'wp_apply (EtcdGrove.grpclog.Component.wp_proof (hG := hG) _ _ _) $$ [Hown] as %llogger ⟨Hown, -⟩',
            '· iframe Hown; try iexact {Hd:google_golang_org.grpc.grpclog}',
            'try wp_auto']


_LOGGER_DOC = '''runs its translated initializer of `logger`, `grpclog.Component(...)` (phase7-inits batch 2,
2026-11-25, until then the trust-boundary axiom `opaqueInitsOk`; `Component`'s proof, through
`grpclog`'s fact)'''
for _p in ['google_golang_org.grpc', 'google_golang_org.grpc.credentials', 'google_golang_org.grpc.health',
           'google_golang_org.grpc.connectivity', 'google_golang_org.grpc.balancer']:
    _c = SPECIAL.setdefault(_p, {})
    _c.setdefault('alloc_types', {})['logger'] = 'GoInterface'
    _c.setdefault('before', {})['logger'] = logger_steps()
    _c.setdefault('imports', []).append('Proof.google_golang_org.grpc.grpclog.Component')
    if 'doc' in _c:
        _c['doc'] = _c['doc'].rstrip('.') + '; it ' + _LOGGER_DOC + '.'
SPECIAL['google_golang_org.grpc.credentials']['doc'] = '''Its fact is `True`. Its initializer initializes its
imports, allocates `logger` and ''' + _LOGGER_DOC + '.'
SPECIAL['google_golang_org.grpc.balancer']['doc'] = '''Its fact is `True`. Its initializer initializes its
imports (`grpclog`, grpc's `internal`), allocates `logger`, ''' + _LOGGER_DOC + ''', and runs its translated
`init` (`balancer.go:77`), which stores `unregisterForTesting` in `internal.BalancerUnregister`, through
`internal`'s invariants (`grpc/internal/Hooks.lean`).'''
SPECIAL['google_golang_org.grpc.balancer']['imports'].append('Proof.google_golang_org.grpc.internal.Hooks')
SPECIAL['google_golang_org.grpc.balancer']['after'] = {
    'init.«0»': hook_fact_steps() + hook_store_steps(['BalancerUnregister'])}
SPECIAL['google_golang_org.grpc.connectivity']['doc'] = '''Its fact is `True`. Its initializer initializes its
import (`grpclog`), allocates `logger` and ''' + _LOGGER_DOC + '.'
# `health`: its `logger` and its two `init`s (until then `initFuncsOk`): `client.go`'s stores
# `clientHealthCheck` in `internal.HealthCheckFunc`; `producer.go`'s sets `producerBuilderSingleton` (its
# own variable) and stores `registerClientSideHealthCheckListener` in `internal.RegisterClientHealthCheckListener`
_GH = SPECIAL['google_golang_org.grpc.health']
_GH['doc'] = '''Its fact is `True`. Its initializer initializes its imports, allocates `logger` and
`producerBuilderSingleton`, ''' + _LOGGER_DOC + ''', and runs its two translated `init`s (phase7-inits
batch 2, 2026-11-25; until then the trust-boundary axiom `initFuncsOk`): `client.go`'s stores
`clientHealthCheck` in `internal.HealthCheckFunc` and `producer.go`'s sets `producerBuilderSingleton` to a
new `producerBuilder` and stores `registerClientSideHealthCheckListener` in
`internal.RegisterClientHealthCheckListener`, both through `internal`'s invariants (`grpc/internal/Hooks.lean`).'''
_GH['alloc_types']['producerBuilderSingleton'] = 'Loc'
_GH['imports'].append('Proof.google_golang_org.grpc.internal.Hooks')
_GH.setdefault('after', {}).update({
    'init.«0»': hook_fact_steps() + hook_store_steps(['HealthCheckFunc']),
    'init.«1»': hook_fact_steps() + ['try wp_auto'] + hook_store_steps(['RegisterClientHealthCheckListener']),
})
# (prove-http3, 2026-11-21) net/textproto: `CanonicalMIMEHeaderKey`'s interned keys
_TP = 'net.textproto'
def _tp_lit(x, n):
    return ['try wp_auto', f'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %s{x} ⟨S{x}, -⟩', 'try wp_auto'] if n else \
        ['try wp_auto', f'wp_apply wp_string_to_bytes _ as %s{x} ⟨S{x}, -⟩', 'try wp_auto']
SPECIAL[_TP] = dict(
    doc='''Its fact (`textprotoInit`, `Proof/net/textproto/Base.lean`; prove-http3, 2026-11-21):
`commonHeaderOnce` is the `sync.Once` of `initCommonHeader`, whose action owns the variable
`commonHeader`. Its initializer allocates its variables, initializes its imports and runs their
translated initializers: `errMessageTooLarge = errors.New(...)` (Perennial's `errors.wp_New`) and the
byte slices `colon`, `nl`, `crnl`, `dotcrnl`; the zero `commonHeaderOnce` and the variable
`commonHeader` then make the `Once` (Perennial's `sync.init_Once`).''',
    alloc_types={'errMessageTooLarge': 'GoInterface', 'colon': 'GoSlice', 'nl': 'GoSlice',
                 'commonHeader': 'Loc', 'commonHeaderOnce': '_root_.Perennial.sync.Once',
                 'crnl': 'GoSlice', 'dotcrnl': 'GoSlice'},
    before={'$end': ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New as %xE -']
            + _tp_lit('colon', False) + _tp_lit('nl', False) + _tp_lit('crnl', True)
            + _tp_lit('dotcrnl', True) + [
            'ihave HP : (net.textproto.commonHeaderVar : IProp GF) $$ [HcommonHeader]',
            '· unfold net.textproto.commonHeaderVar; iexists _; iexact HcommonHeader',
            'imod (_root_.Perennial.sync.init_Once _ _ net.textproto.commonHeaderOk ⊤) $$ [HcommonHeaderOnce HP] with #HOnce',
            '· iframe',
            'try wp_auto']},
    finish=FIN_PRE[:6] + ['imodintro', 'unfold net.textproto.textprotoInit net.textproto.textprotoInitLC',
                          'iexact HOnce'],
)
_OP = 'go_opentelemetry_io.otel.propagation'
SPECIAL[_OP] = dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-misc, 2026-11-20): the interface assertions (`var _
TextMapCarrier = MapCarrier{}`, ...) and `versionPart = fmt.Sprintf("%.2X", supportedVersion)`
(Perennial's `fmt.wp_Sprintf` of the real `Sprintf`, `fmt-stage15`'s `%.P`: some string, no panic).''',
    alloc_types={'versionPart': 'GoString', 'handleExtractErrOnce': '_root_.Perennial.sync.Once'},
    before={'versionPart': [
        'try wp_auto',
        'wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mmc -',
        'try wp_auto',
        'wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) go.string (go.GoType.SliceType go.string)) as %mhc1 -',
        'try wp_auto',
        'wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) go.string (go.GoType.SliceType go.string)) as %mhc2 -',
        'try wp_auto',
        'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %svp ⟨Svp, -⟩',
        'try wp_auto',
        'wp_apply EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%.2X" '
        '[.prec 2 _root_.Perennial.fmt.verb_X] _ _ _ _ (by fmt_encode) (by fmt_fits) '
        '(.int _ _ _ _ (.int _) .nil) $$ [$Svp] as %rvp -',
        'try wp_auto']},
    imports=['Proof.fmt.SprintfPure'],
)
_ZC = 'go_uber_org.zap.zapcore'
_ZCL = f'{_ZC}.Level.ty'
_ZCC = '_root_.Perennial.go_uber_org.zap.internal.color.Color.ty'
def _zc_pool(h):
    return ['try wp_auto', 'rw [recv_eq_func_mk BAnon BAnon]',
            f'wp_apply (EtcdGrove.zap.internal.pool.New.wp_proof (GF := GF) (hG := hG) _) as %{h} -',
            'try wp_auto']
# (zap-z2, 2026-11-23) `_cePool`: the pool `New` returns becomes an `isPool` of owned entries (zapcore's fact)
_zc_ce_pool = ['try wp_auto', 'rw [recv_eq_func_mk BAnon BAnon]',
    'wp_apply (EtcdGrove.zap.internal.pool.New.wp_proof (GF := GF) (hG := hG) _) as %pce Hpce',
    'imod (EtcdGrove.zap.internal.pool.ownPool_init _ pce _ EtcdGrove.zapcore.pooledEntry ⊤) $$ [$Hpce] with #Hpce',
    '· unfold EtcdGrove.zap.internal.pool.fnSpec',
    '  imodintro',
    '  iintro %Φ - HΦ',
    '  wp_auto',
    '  wp_apply wp_slice_make2 (V := GoInterface) as %sc ⟨Hsc, Hscap⟩',
    '  · ipureintro',
    '    word',
    '  iapply HΦ',
    '  unfold EtcdGrove.zapcore.pooledEntry',
    '  iexists _',
    '  iframe',
    '  iexists []',
    '  iapply ownSlice_nil',
    'try wp_auto']
SPECIAL[_ZC] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers and its translated `init` (prove-misc, 2026-11-20; until then the
trust-boundary axioms `opaqueInitsOk` and `initFuncsOk`): the pools (`pool.New`, proved), the interface
assertions, `nullLiteralBytes`, `errUnmarshalNilLevel` (`errors.New`), the level colors (a map literal)
and their two string maps, which `init` (`level_strings.go`) fills: each level's color formatted
around its name (`color.Add`, `fmt.Sprintf`; `Level.String`/`CapitalString` of the map's levels).''',
    alloc_types={'DefaultClock': f'{_ZC}.systemClock', '_sliceEncoderPool': 'Loc', '_cePool': 'Loc',
                 '_errArrayElemPool': 'Loc', '_jsonPool': 'Loc', 'nullLiteralBytes': 'GoSlice',
                 '_levelToColor': 'Loc', '_unknownLevelColor': 'w8',
                 '_levelToLowercaseColorString': 'Loc', '_levelToCapitalColorString': 'Loc'},
    before={'_sliceEncoderPool': _zc_pool('psl'), '_cePool': _zc_ce_pool,
            '_errArrayElemPool': _zc_pool('pea'), '_jsonPool': _zc_pool('pjs'),
            'nullLiteralBytes': ['try wp_auto', 'wp_apply wp_string_to_bytes _ as %snull ⟨Hsnull, -⟩', 'try wp_auto'],
            '_levelToColor': map_lit_steps('Hlc', 'w8', 'w8', _ZCL, _ZCC, 7),
            '_levelToLowercaseColorString': ['try wp_auto',
                f'wp_apply (wp_map_len (t := go.GoType.MapType {_ZCL} {_ZCC}) mHlc _ _) $$ [$Hlc] as Hlc',
                'try wp_auto',
                f'wp_apply (wp_map_make2 (K := w8) (V := GoString) _ {_ZCL} go.string) as %mlow Hlow',
                'try wp_auto'],
            '_levelToCapitalColorString': ['try wp_auto',
                f'wp_apply (wp_map_len (t := go.GoType.MapType {_ZCL} {_ZCC}) mHlc _ _) $$ [$Hlc] as Hlc',
                'try wp_auto',
                f'wp_apply (wp_map_make2 (K := w8) (V := GoString) _ {_ZCL} go.string) as %mcap Hcap',
                'try wp_auto']},
    after={'init.«0»': [
        'wp_func_lits',
        'wp_bind (App (App (Val (map.forRange _ _)) _) _)',
        'iapply (wp_map_for_range (K := w8) (V := w8) (fun _ _ => iprop(∃ (lv cv : w8) (L U : GMap w8 GoString), '
        'color_ptr ↦ cv ∗ level_ptr ↦ lv ∗ mlow ↦$ L ∗ mcap ↦$ U ∗ '
        'globalAddr _levelToLowercaseColorString ↦ mlow ∗ globalAddr _levelToCapitalColorString ↦ mcap))) $$ Hlc',
        'iintro %keys -',
        'isplitl [color level Hlow Hcap H_levelToLowercaseColorString H_levelToCapitalColorString]',
        '· iexists _, _, _, _; iframe',
        'isplitr',
        '· imodintro',
        '  iintro %i %key %vv ⟨-, %Hvv⟩ ⟨%lv, %cv, %L, %U, Hc, Hl, HL, HU, HgL, HgU⟩',
        '  wp_auto',
        '  have hk : ' + ' ∨ '.join(f'key = W8 {x}' for x in ['5', '4', '3', '2', '1', '0', '(-1)']) + ' := by',
        '    simp only [GMap.lookup_insert_eq_iff, GMap.lookup_empty] at Hvv',
        '    by_cases h0 : W8 5 = key; · exact Or.inl h0.symm',
        '    simp only [h0, ↓reduceIte] at Hvv',
        '    by_cases h1 : W8 4 = key; · exact Or.inr (Or.inl h1.symm)',
        '    simp only [h1, ↓reduceIte] at Hvv',
        '    by_cases h2 : W8 3 = key; · exact Or.inr (Or.inr (Or.inl h2.symm))',
        '    simp only [h2, ↓reduceIte] at Hvv',
        '    by_cases h3 : W8 2 = key; · exact Or.inr (Or.inr (Or.inr (Or.inl h3.symm)))',
        '    simp only [h3, ↓reduceIte] at Hvv',
        '    by_cases h4 : W8 1 = key; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4.symm))))',
        '    simp only [h4, ↓reduceIte] at Hvv',
        '    by_cases h5 : W8 0 = key; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5.symm)))))',
        '    simp only [h5, ↓reduceIte] at Hvv',
        '    by_cases h6 : W8 (-1) = key; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h6.symm))))))',
        '    simp only [h6, ↓reduceIte] at Hvv',
        '    simp at Hvv',
        '  iclear MerrUnmarshalNilLevel',
        '  haveI : go.NotInterface go.int8 := ⟨by unfold go.int8; trivial⟩',
        '  haveI : go.NotInterface go.uint8 := ⟨by unfold go.uint8; trivial⟩',
        '  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl',
        '  all_goals (repeat (first',
        '    | wp_apply (wp_mapInsert (K := w8) (V := GoString) _) $$ HL as HL',
        '    | wp_apply (wp_mapInsert (K := w8) (V := GoString) _) $$ HU as HU',
        '    | (wp_apply (wp_slice_literal (l := [_, _])); isplitr; (· ipureintro; rfl); iintro %sl ⟨Ssl, -⟩; '
        'try wp_auto; wp_apply EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"\\x1b[%dm%s\\x1b[0m" '
        '[.lit go!"\\x1b[", .dir none _root_.Perennial.fmt.verb_d, .lit go!"m", .dir none _root_.Perennial.fmt.verb_s, .lit go!"\\x1b[0m"] '
        '_ _ _ _ (by fmt_encode) (by fmt_fits) (.int _ _ _ _ (.uint8 _) (.str _ _ _ .nil)) $$ [$Ssl] as %r -)',
        '    | wp_method_call',
        '    | wp_auto',
        '    | wp_call))',
        '  all_goals (unfold forMapPostcondition; iright; ileft; isplitr; (· ipureintro; rfl); iexists _, _, _, _; iframe)',
        'iintro - -',
        'wp_auto',
        ]},
    imports=['Proof.go_uber_org.zap.internal.pool.New', 'Proof.fmt.SprintfPure'],
    heavy=True,
), ['errUnmarshalNilLevel'])
# (zap-z1, 2026-11-23) zap's internal buffer pool: `zap.Logger.check` reads `Get`
SPECIAL['go_uber_org.zap.internal.bufferpool'] = dict(
    doc='''Its fact is `True`. Its initializer allocates its variables, initializes `buffer` and runs their
translated initializers (zap-z1, 2026-11-23: zap's `Logger.check` reads `Get`): `_pool = buffer.NewPool()`
(`pool.New` of a function literal, proved) and `Get = _pool.Get` (a method value, not called).''',
    alloc_types={'_pool': '_root_.Perennial.go_uber_org.zap.buffer.Pool', 'Get': 'GoFunc'},
    before={'_pool': ['try wp_auto', 'wp_func_call', 'wp_call', 'try wp_auto',
                      'rw [recv_eq_func_mk BAnon BAnon]',
                      'wp_apply (EtcdGrove.zap.internal.pool.New.wp_proof (GF := GF) (hG := hG) _) as %pbuf -',
                      'try wp_auto']},
    imports=['Proof.go_uber_org.zap.internal.pool.New', 'Proof.fmt.SprintfPure'],
)
# (zap-z2, 2026-11-23) zap's `internal/exit`: `_exit = os.Exit`, held by its fact (`zapcore.WriteThenFatal`'s
# hook calls `With`, which calls it)
SPECIAL['go_uber_org.zap.internal.exit'] = dict(
    doc='''Its fact: `_exit` holds `os.Exit` for good (zap-z2, 2026-11-23: `zap.Logger.Fatal` reaches `With`, which
calls it; only the test helpers `Stub`/`WithStub`/`Unstub`, not translated, write it). Its initializer allocates
`_exit`, initializes `os` and stores the function value.''',
    alloc_types={'_exit': 'GoFunc'},
    before={'$end': ['try wp_auto']},
    finish=['ipersist H_exit'] + FIN_PRE[:6],
)
# (zap-z2, 2026-11-23) `multierr` (zapcore's `CheckedEntry.Write` names its `Append`): its variables
_ME_BYTES = ['try wp_auto', 'wp_apply wp_string_to_bytes _ as %_ ⟨_, -⟩', 'try wp_auto']
SPECIAL['go_uber_org.multierr'] = dict(
    doc='''Its fact is `True`. Its initializer allocates its variables, initializes `bytes` and `sync` and runs their
translated initializers (zap-z2, 2026-11-23: zapcore imports it): the separators (`[]byte` of string
constants) and `_bufferPool` (a `sync.Pool` literal whose `New` is a function literal, not called).''',
    alloc_types={'_singlelineSeparator': 'GoSlice', '_multilinePrefix': 'GoSlice',
                 '_multilineSeparator': 'GoSlice', '_multilineIndent': 'GoSlice',
                 '_bufferPool': '_root_.Perennial.sync.Pool'},
    before={'_singlelineSeparator': _ME_BYTES, '_multilinePrefix': _ME_BYTES,
            '_multilineSeparator': _ME_BYTES, '_multilineIndent': _ME_BYTES,
            '_bufferPool': ['try wp_auto', 'rw [recv_eq_func_mk BAnon BAnon]', 'try wp_auto'],
            '$end': ['try wp_auto']},
)
# (prove-initleft, 2026-11-21) zapcore's fact: `DefaultClock` holds a fixed `systemClock` (zap's `NewNop` loads it)
SPECIAL[_ZC]['doc'] = SPECIAL[_ZC]['doc'].replace("Its fact is `True`.", "Its fact: `DefaultClock` holds a fixed `systemClock` (zap's `NewNop`, which zap's\ninitializer runs, loads it; prove-initleft, 2026-11-21: until then `True`), and `_cePool` a fixed pool of\nowned entries (zap-z2, 2026-11-23: `CheckedEntry.Write` and `After` use it).")
SPECIAL[_ZC]['finish'] = ['ipersist HDefaultClock', 'ipersist H_cePool'] + FIN_PRE[:6] + [
    'imodintro', 'isplitl []', f'· iexists (zero_val {_ZC}.systemClock)', '  itrivial',
    'iexists pce', 'iframe #']
# (prove-initleft, 2026-11-21) zap's package variables, translated but `_minTimeInt64`/`_maxTimeInt64`
# (Perennial's `time.Unix` is names only) and `_sinkRegistry`; (prove-srvloops2, 2026-11-21)
# `_minTimeInt64`/`_maxTimeInt64` translated (`time.Unix`), held by zap's fact (`zap.Time` reads them)
_Z = 'go_uber_org.zap'
_ZENC = (f'(go.GoType.FunctionType (go.signature.Signature [_root_.Perennial.{_ZC}.EncoderConfig.ty] false '
         f'[_root_.Perennial.{_ZC}.Encoder.ty, go.error]))')
SPECIAL[_Z] = newvars_cfg(dict(
    doc='''Its fact: `_minTimeInt64` and `_maxTimeInt64` hold fixed times (prove-srvloops2, 2026-11-21: `zap.Time`
compares with them; until then `True`). Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-initleft, 2026-11-21; until then the trust-boundary axiom
`opaqueInitsOk` covered them all): `errNoEncoderNameSpecified` (`errors.New`), the encoder constructors (a
map literal of two func literals), `_errArrayElemPool` (`pool.New`, proved), `_globalL = NewNop()`
(`zapcore.NewNopCore()`, `zapcore.AddSync(io.Discard)` over any writer, `zapcore.DefaultClock` from
zapcore's fact), `_globalS = _globalL.Sugar()` (a copy of the logger) and the interface assertion
`var _ internal.LeveledEnabler = AtomicLevel{}`, and (prove-srvloops2) `_minTimeInt64`/`_maxTimeInt64`
(`time.Unix`); `_sinkRegistry` (`newSinkRegistry`) stays untranslated, `opaqueInitsOk`.''',
    alloc_types={'_encoderNameToConstructor': 'Loc', '_errArrayElemPool': 'Loc', '_globalL': 'Loc',
                 '_globalS': 'Loc', '_minTimeInt64': '_root_.Perennial.time.Time',
                 '_maxTimeInt64': '_root_.Perennial.time.Time'},
    finish=['ipersist H_minTimeInt64', 'ipersist H_maxTimeInt64'] + FIN_PRE[:6],
    before={
        '_minTimeInt64': ['try wp_auto', 'wp_apply _root_.Perennial.time.wp_Unix as %tmin -', 'try wp_auto'],
        '_maxTimeInt64': ['try wp_auto', 'wp_apply _root_.Perennial.time.wp_Unix as %tmax -', 'try wp_auto'],
        '_encoderNameToConstructor': map_lit_steps('Henc', 'GoString', 'GoFunc', 'go.string', _ZENC, 2),
        '_errArrayElemPool': _zc_pool('pea'),
        '_globalL': ['try wp_auto',
                     'ihave #HNN : (iprop(isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) '
                     'pkg_id.go_uber_org.zap.zapcore) : IProp GF) $$ []',
                     '· isplitl []', '  · iexact {Hd:io}', '  · iexact {Hd:go_uber_org.zap.zapcore}',
                     'wp_apply EtcdGrove.zap_wp_NewNop_init $$ HNN as %lgl ⟨%vgl, Hgl, -⟩', 'try wp_auto'],
        '_globalS': ['try wp_auto', 'wp_apply (EtcdGrove.zap_wp_Sugar_init lgl vgl) $$ Hgl as %sgl Hgl', 'try wp_auto'],
    },
    pre=[
        'section zapinit',
        'variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]',
        'variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]',
        'variable [package_sem : _root_.Perennial.go_uber_org.zap.Assumptions]',
        '',
        '/-- (prove-initleft) `zapcore.AddSync(w)` returns, whatever the writer (a type switch: `w` itself if',
        'it is a `WriteSyncer`, else `writerWrapper{w}`). -/',
        'theorem EtcdGrove.zap_wp_AddSync_init (w : GoInterface) :',
        '    {{ (True : IProp GF) }} (App (Val (@! _root_.Perennial.go_uber_org.zap.zapcore.AddSync)) (Val #w))',
        '    {{ (r : GoInterface), RET #r; True }} := by',
        '  wp_start',
        '  wp_auto',
        '  rcases w with wo | _',
        '  · wp_auto',
        '    cases hws : go.typeSetContains wo.ty _root_.Perennial.go_uber_org.zap.zapcore.WriteSyncer.ty',
        '    all_goals (wp_auto; iapply HΦ; itrivial)',
        '  · wp_auto',
        '    iapply HΦ',
        '    itrivial',
        '',
        '/-- (prove-initleft) `zap.NewNop()` before zap\'s `isPkgInit`: a new `Logger` (its body: `NewNopCore()`,',
        '`AddSync(io.Discard)`, `zapcore.DefaultClock`, from io\'s and zapcore\'s facts), a `nopLoggerVal`',
        '(prove-zap3: `zap.NewNop`\'s spec is proved from it). -/',
        'theorem EtcdGrove.zap_wp_NewNop_init :',
        '    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore }}',
        '      (App (Val (@! _root_.Perennial.go_uber_org.zap.NewNop)) (Val #()))',
        '    {{ (l : Loc), RET #l; ∃ v : _root_.Perennial.go_uber_org.zap.Logger, l ↦ v ∗',
        '        ⌜EtcdGrove.zap.nopLoggerVal v⌝ }} := by',
        '  wp_start',
        '  ihave #IO : (_root_.Perennial.io.isInit : IProp GF) $$ []',
        '  · iapply isPkgInit_access $$ Hpkg',
        '  iNamed IO',
        '  icases HDiscard with ⟨%wd, #HDiscard⟩',
        '  ihave #ZC := _root_.Perennial.go_uber_org.zap.zapcore.isInit_access $$ Hpkg2',
        '  icases ZC with ⟨⟨%dc, #HDC⟩, -⟩',
        '  wp_auto',
        '  wp_func_call',
        '  wp_call',
        '  wp_auto',
        '  wp_apply EtcdGrove.zap_wp_AddSync_init as %ws -',
        '  try wp_auto',
        '  iapply HΦ',
        '  iexists _',
        '  iframe',
        '  ipureintro',
        '  exact ⟨rfl, rfl, rfl, rfl, rfl, dc, rfl⟩',
        '',
        '/-- (prove-initleft) `l.Sugar()` on a `Logger`: a copy of it (`clone`), its caller skip plus 2. -/',
        'theorem EtcdGrove.zap_wp_Sugar_init (l : Loc) (v : _root_.Perennial.go_uber_org.zap.Logger) :',
        '    {{ (l ↦ v : IProp GF) }}',
        '      (App (Val (l @!! go.GoType.PointerType _root_.Perennial.go_uber_org.zap.Logger.ty @!! go!"Sugar")) (Val #()))',
        '    {{ (s : Loc), RET #s; l ↦ v }} := by',
        '  wp_start as Hl',
        '  wp_auto',
        '  wp_method_call',
        '  wp_call',
        '  wp_auto',
        '  iapply HΦ',
        '  iframe',
        '',
        'end zapinit'],
    imports=['Proof.go_uber_org.zap.internal.pool.New', 'Proof.fmt.SprintfPure'],
), ['errNoEncoderNameSpecified'])
# (prove-zap3, 2026-11-21) zap's last package variable, `_sinkRegistry` (`newSinkRegistry`: the file sink registered,
# `normalizeScheme("file")` over `strings.ToLower`'s spec); `opaqueInitsOk` is gone
SPECIAL[_Z]['doc'] = SPECIAL[_Z]['doc'].replace('''`_sinkRegistry` (`newSinkRegistry`) stays untranslated, `opaqueInitsOk`.''',
'''and (prove-zap3, 2026-11-21) `_sinkRegistry = newSinkRegistry()`: a registry whose fresh mutex is locked
around the registration of the file sink, `normalizeScheme("file")` being `"file"` by `strings.ToLower`'s
spec.''')
SPECIAL[_Z]['alloc_types'].update({'_sinkRegistry': 'Loc'})
SPECIAL[_Z]['before'].update({
    '_sinkRegistry': ['try wp_auto',
                      'wp_apply (EtcdGrove.zap_wp_newSinkRegistry_init EtcdGrove.strings.ToLower.wp_proof) $$ '
                      '{Hd:sync} as %srl -',
                      'try wp_auto'],
})
_i = SPECIAL[_Z]['pre'].index('end zapinit')
SPECIAL[_Z]['pre'][_i:_i] = [
    '/-- (prove-zap3) `normalizeScheme("file")` is `("file", nil)`: `strings.ToLower` of an ASCII word with',
    'no upper-case letter is the word itself (its spec, `strings.lowersTo`), whose first byte is a letter and',
    'whose other bytes are letters. -/',
    'theorem EtcdGrove.zap_wp_normalizeScheme_file (hTL : EtcdGrove.strings.ToLower.spec (GF := GF) (hG := hG)) :',
    '    {{ (True : IProp GF) }}',
    '      (App (Val (@! _root_.Perennial.go_uber_org.zap.normalizeScheme)) (Val #(go!"file")))',
    '    {{ RET (PairV #(go!"file") #interface.nil); True }} := by',
    '  wp_start',
    '  wp_auto',
    '  wp_apply hTL as %r %Hr',
    '  have hr : r = go!"file" := (Hr go!"file" (by decide)).mpr (by decide)',
    '  subst hr',
    '  wp_auto',
    '  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜1 ≤ sint.Z i ∧ sint.Z i ≤ 4⌝ : IProp GF) $$ [i]',
    '  · iexists W64 1; iframe; ipureintro; decide',
    '  wp_for HI',
    '  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-',
    '  try wp_auto',
    '  wp_if_destruct',
    '  · have hi : i = W64 1 ∨ i = W64 2 ∨ i = W64 3 := by',
    '      have : sint.Z i < 4 := by have h := go.intoVal_inj Hif; simp at h; word',
    '      rcases (show sint.Z i = 1 ∨ sint.Z i = 2 ∨ sint.Z i = 3 by omega) with h | h | h',
    '      · left; word',
    '      · right; left; word',
    '      · right; right; word',
    '    rcases hi with rfl | rfl | rfl',
    '    all_goals (wp_auto; wp_for_post; iframe; iexists _; iframe; ipureintro; word)',
    '  · rw [ite_eq_right_of_eq_false _ _ (by',
    '      cases h : decide (sint.Z i < sint.Z (W64 ↑[W8 102, W8 105, W8 108, W8 101].length)) <;> simp_all)]',
    '    wp_auto',
    '    iapply HΦ',
    '    itrivial',
    '',
    '/-- (prove-zap3) `newSinkRegistry()` returns (a new registry: an empty factory map, `os.OpenFile`, and the',
    'file sink registered by `RegisterSink`, under the registry\'s fresh mutex, `normalizeScheme("file")`',
    'succeeding and the map holding no factory yet). -/',
    'theorem EtcdGrove.zap_wp_newSinkRegistry_init (hTL : EtcdGrove.strings.ToLower.spec (GF := GF) (hG := hG)) :',
    '    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}',
    '      (App (Val (@! _root_.Perennial.go_uber_org.zap.newSinkRegistry)) (Val #()))',
    '    {{ (sr : Loc), RET #sr; True }} := by',
    '  wp_start as #Hsync',
    '  wp_auto',
    '  wp_apply wp_map_make1 (K := GoString) (V := GoFunc) as %m Hm',
    '  try wp_auto',
    '  iStructNamed «$r0»',
    '  imod sync.init_Mutex iprop(True) ⊤ («$r0_ptr».[_root_.Perennial.go_uber_org.zap.sinkRegistry, go!"mu"])',
    '    $$ mu [] with #Hmu',
    '  · inext; itrivial',
    '  try wp_auto',
    '  wp_method_call',
    '  wp_call',
    '  rw [show _root_.Perennial.go_uber_org.zap.schemeFile = #(go!"file") from rfl]',
    '  try wp_auto',
    '  wp_apply wp_with_defer as %defer defer',
    '  try wp_auto',
    '  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, -⟩',
    '  try wp_auto',
    '  wp_apply (EtcdGrove.zap_wp_normalizeScheme_file hTL)',
    '  try wp_auto',
    '  wp_apply wp_map_lookup2 $$ [$Hm] as Hm',
    '  try wp_auto',
    '  wp_apply (wp_mapInsert (K := GoString) (V := GoFunc) _) $$ Hm as Hm',
    '  try wp_auto',
    '  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked]',
    '  · itrivial',
    '  try wp_auto',
    '  iapply HΦ',
    '  itrivial',
    '',
]
for _m in ['Spec.strings.ToLower', 'Proof.strings.ToLower', 'Spec.go_uber_org.zap.Defs']:
    if _m not in SPECIAL[_Z]['imports']:
        SPECIAL[_Z]['imports'].append(_m)
_FG = 'go_etcd_io.etcd.pkg.v3.featuregate'
# (featuregate-3, 2026-11-23) featuregate's `defaultFeatures` and `specialFeatures` (map literals of
# constants and function values), translated; fact `featuregateInit` (`featuregate/PkgInit.lean`):
# `defaultFeatures`' map read-only, `specialFeatures` some map
SPECIAL[_FG] = dict(
    doc='''Its fact (`featuregateInit`, `featuregate/Defs.lean`; featuregate-3, 2026-11-23, until then `True`):
`defaultFeatures` holds a read-only map of `AllAlpha` and `AllBeta` (`defaultKnown`), `specialFeatures`
some map, both for good. Its initializer initializes its imports, allocates the two and runs their
translated initializers, map literals of constants and function values.''',
    alloc_types={'defaultFeatures': 'Loc', 'specialFeatures': 'Loc'},
    before={'defaultFeatures': map_lit_steps('Hdf', 'GoString', f'{_FG}.FeatureSpec', f'{_FG}.Feature.ty',
                                             f'{_FG}.FeatureSpec.ty', 2),
            'specialFeatures': map_lit_steps('Hsf', 'GoString', 'GoFunc', f'{_FG}.Feature.ty', '_', 2)},
    finish=['ipersist HdefaultFeatures', 'ipersist HspecialFeatures', 'ipersist Hdf',
            'iframe Hown', 'is_pkg_init_finish', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
            'imodintro', 'imodintro', 'unfold EtcdGrove.featuregate.featuregateInit',
            'iexists mHdf, mHsf', 'iframe HdefaultFeatures HspecialFeatures',
            'unfold EtcdGrove.featuregate.defaultKnown EtcdGrove.featuregate.spec', 'iexact Hdf'],
)
SPECIAL['go_etcd_io.etcd.server.v3.features'] = dict(
    doc='''Its fact (`featuresInit`, `features/Defs.lean`; featuregate-3, 2026-11-23, until then `True`):
`DefaultEtcdServerFeatureGates` holds a read-only map of the server's features (`serverFeatureSpecs`),
for good. Its initializer initializes its imports, allocates `DefaultEtcdServerFeatureGates` and runs
its translated initializer, a map literal of `featuregate.FeatureSpec` literals (prove-smallinits,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).''',
    alloc_types={'DefaultEtcdServerFeatureGates': 'Loc'},
    before={'DefaultEtcdServerFeatureGates': map_lit_steps('Hfg', 'GoString', f'{_FG}.FeatureSpec',
        f'{_FG}.Feature.ty', f'{_FG}.FeatureSpec.ty', 10)},
    finish=['ipersist HDefaultEtcdServerFeatureGates', 'ipersist Hfg',
            'iframe Hown', 'is_pkg_init_finish', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
            'imodintro', 'imodintro', 'unfold EtcdGrove.featuresInit',
            'iexists mHfg', 'iframe HDefaultEtcdServerFeatureGates',
            'unfold EtcdGrove.serverFeatureSpecs EtcdGrove.featuregate.spec', 'iexact Hfg'],
)
_API = 'go_etcd_io.etcd.server.v3.etcdserver.api'
SPECIAL[_API] = dict(
    doc='''Its fact (`capInit`, `CapPool.lean`; prove-ps2-cap, 2026-11-23, until then `True`):
`enableMapMu`'s guard and its reader slots, pooled at level 0, over `enabledMap` holding `nil` or a
read-only map. Its initializer initializes its imports, allocates its variables and runs the
translated initializer of `capabilityMaps` (a map literal of map literals) and its translated `init`
function, which sets `enabledMap` to a map literal (prove-smallinits, 2026-11-20; until then the
trust-boundary axioms `opaqueInitsOk` and `initFuncsOk`), and makes the fact from the map, made
read-only, and the fresh lock (`capInit_alloc`).''',
    alloc_types={'capabilityMaps': 'Loc', 'enabledMap': 'Loc',
                 # (prove-ps2-cap, 2026-11-23) the lock `IsCapabilityEnabled` read-locks
                 'enableMapMu': '_root_.Perennial.sync.RWMutex'},
    before={'capabilityMaps': ['try wp_auto',
        f'wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string (go.GoType.MapType {_API}.Capability.ty go.bool)) as %mcm Hcm',
        'try wp_auto'] + [l for k in range(9) for l in
        [f'wp_apply (wp_map_make1 (K := GoString) (V := Bool) {_API}.Capability.ty go.bool) as %mc{k} Hc{k}', 'try wp_auto'] +
        [f'wp_apply (wp_mapInsert (K := GoString) (V := Bool) {_API}.Capability.ty) $$ Hc{k} as Hc{k}', 'try wp_auto'] * 2 +
        ['wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string) $$ Hcm as Hcm', 'try wp_auto']]},
    # `enabledMap = map[Capability]bool{AuthCapability: true, V3rpcCapability: true}`
    after={'init.«0»': [f'wp_apply (wp_map_make1 (K := GoString) (V := Bool) {_API}.Capability.ty go.bool) as %me He',
        'try wp_auto'] + [f'wp_apply (wp_mapInsert (K := GoString) (V := Bool) {_API}.Capability.ty) $$ He as He', 'try wp_auto'] * 2},
    # (prove-ps2-cap, 2026-11-23) the fact `capInit`: `init()`'s map read-only, `enableMapMu`'s guard
    # and its reader slots pooled (`capInit_alloc`)
    finish=['ipersist He',
            f'imod ({_API}.capInit_alloc ⊤ _ _) $$ [HenabledMap HenableMapMu] with #HCI',
            '· iframe HenabledMap HenableMapMu; iexact He'] + FIN_PRE[:6],
)

# (prove-smallinits, 2026-11-20) k8s's single-item lists: a func literal, an `errors.New` call, empty
# struct literals, an integer constant and `var _ I = &T{}` checks, translated (until then each
# package's `opaqueInitsOk`); their facts are `True`.
_K8S_ALLOCS = {'k8s_io.utils.clock', 'k8s_io.apimachinery.pkg.util.validation.field'}
for _p, _what in [('k8s_io.apimachinery.pkg.conversion', '`DefaultNameFunc`, a func literal'),
                  ('k8s_io.apimachinery.pkg.runtime.schema', '`EmptyObjectKind`, an empty struct literal'),
                  ('k8s_io.utils.clock', 'its `var _` conversions')]:
    # (merge, 2026-11-20) `util/validation/field` is k8s-authz's SPECIAL entry above (its fact
    # `fieldInit`), which allocates the `var _ error = &Error{}` check as these do
    assert _p not in SPECIAL, _p
    SPECIAL[_p] = dict(doc=f'''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers: {_what} (prove-smallinits, 2026-11-20; until then the trust-boundary
axiom `opaqueInitsOk`).''', alloc_types=_ALLOC_ANY,
        # the `&T{}` allocations
        before={'$end': ['try wp_auto', 'repeat (wp_alloc_anon; try wp_auto)']} if _p in _K8S_ALLOCS else {})
# (klog-leaves, 2026-11-23; etcd-grove#25) klog's `logging`, translated (zero: no initializer) for `V`
SPECIAL['k8s_io.klog.v2'] = dict(doc='''Its fact (`klogInit`, `storage/etcd3/Base.lean`): of the global `logging`, `verbosity` holds
some level, `filterLength` is 0 and `logger` is `nil`, read-only for good. Its initializer
initializes its imports, allocates `logging` (zero: it has no initializer; the allocation gives its
fields' points-tos) and runs its `init` functions (trusted no-ops, `TrustedCode/k8s_io/klog/v2.lean`:
`init.1` writes 0 to `verbosity` and `filterLength`, as the zero value has them; klog-leaves,
2026-11-23).''',
    alloc_types={'logging': 'k8s_io.klog.v2.loggingT'},
    finish=['iStructNamed Hlogging', 'iStructNamed settings',
            'ipersist verbosity', 'ipersist filterLength', 'ipersist logger'] + FIN_PRE[:6] +
           ['imodintro', 'unfold k8s_io.apiserver.pkg.storage.etcd3.klogInit',
            'isplitl []', '· iexists _; iexact verbosity', 'isplitl []',
            # the zero value's fields, by `rfl`
            "· have hz : (zero_val k8s_io.klog.v2.loggingT).settings'.filterLength' = W32 0 := rfl",
            '  rw [← hz]', '  iexact filterLength',
            "· have hz : (zero_val k8s_io.klog.v2.loggingT).settings'.logger' = null := rfl",
            '  rw [← hz]', '  iexact logger'],
)
# (prove-k8s, 2026-11-20) more k8s lists translated (until then each package's `opaqueInitsOk`); their
# facts are `True`.
SPECIAL['k8s_io.utils.trace'] = dict(doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers: `klogV`, a func literal over `klog.V(lvl).Enabled()` (prove-k8s,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).''', alloc_types=_ALLOC_ANY)
SPECIAL['k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured'] = dict(doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers: `UnstructuredJSONScheme`, an empty struct literal, and the `var _ I =
&T{}` checks (prove-k8s, 2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).''',
    alloc_types=_ALLOC_ANY,
    # `runtime.Codec` is a named `Serializer`: `≤u` has no transitive instance (notes/perennial-changes.md)
    before={'UnstructuredJSONScheme': ['haveI : k8s_io.apimachinery.pkg.runtime.Codec.ty ≤u '
                'k8s_io.apimachinery.pkg.runtime.Serializer.underlying := '
                '⟨(go.underlying_unfold (t := k8s_io.apimachinery.pkg.runtime.Codec.ty)).trans '
                '(go.underlying_unfold (t := k8s_io.apimachinery.pkg.runtime.Serializer.ty))⟩'],
            '$end': ['try wp_auto', 'repeat (wp_alloc_anon; try wp_auto)']})
# (prove-k8s3, 2026-11-21) grpclog's `internal`, imported (types only) so that grpclog's `LoggerV2`
# is its interface: its variables' initializers, translated.
SPECIAL['google_golang_org.grpc.grpclog.internal'] = dict(doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s3, 2026-11-21): `severityName`, a slice literal, and the
function values `sprintf`, `sprint`, `sprintln` (`fmt`'s) and `exit` (`os.Exit`).''',
    alloc_types=_ALLOC_ANY,
    before={'severityName': ['try wp_auto',
                'wp_apply (wp_slice_literal (l := [go!"INFO", go!"WARNING", go!"ERROR", go!"FATAL"])); '
                'isplitr; (· ipureintro; rfl); iintro %sn -',
                'try wp_auto']})
SPECIAL['k8s_io.apimachinery.pkg.util.wait'] = dict(doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): `ErrWaitTimeout` (`ErrorInterrupted` of an `errors.New` error, translated),
`errWaitTimeout` and `internalClock` (empty struct literals), `RealTimer` (a method value),
`ForeverTestTimeout` (a constant product), `NeverStop` (a fresh channel), `jitterRand` (a function
value) and `var _ context.Context = channelContext{}`.''',
    alloc_types=_ALLOC_ANY,
    before={'ErrWaitTimeout': ['try wp_auto', 'wp_apply _root_.Perennial.errors.wp_New_errorString as %xW ⟨#_, #MW⟩',
                               'try wp_auto', 'wp_func_call', 'wp_call', 'try wp_auto'],
            'NeverStop': ['try wp_auto', 'wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩', 'try wp_auto']})
_LB = 'k8s_io.apimachinery.pkg.labels'
SPECIAL[_LB] = dict(doc='''Its fact (`labelsInit`, `storage/etcd3/Base.lean`; #25, 2026-11-21): its shared selectors,
read-only for good, `sharedEverythingSelector` an empty `internalSelector` and `sharedNothingSelector`
a `nothingSelector` (`Everything`, `MatchesNothing`). Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): the operator slices `unaryOperators`, `binaryOperators` (literals) and
`validRequirementOperators` (their `append`), the shared selectors `sharedEverythingSelector` (an
empty `internalSelector` literal) and `sharedNothingSelector` (an empty struct literal), the map
literal `string2token` and `var _ Selector = ValidatedSetSelector{}` (an empty map literal).''',
    alloc_types=_ALLOC_ANY,
    before={'unaryOperators': ['try wp_auto',
                'wp_apply (wp_slice_literal (l := [go!"exists", go!"!"])); isplitr; (· ipureintro; rfl); iintro %su ⟨Su, -⟩',
                'try wp_auto'],
            'binaryOperators': ['try wp_auto',
                'wp_apply (wp_slice_literal (l := [go!"in", go!"notin", go!"=", go!"==", go!"!=", go!"gt", go!"lt"])); '
                'isplitr; (· ipureintro; rfl); iintro %sb ⟨Sb, Cb⟩',
                'try wp_auto'],
            'validRequirementOperators': ['try wp_auto',
                'wp_apply (wp_slice_append (V := GoString) _ _ _ _ _) $$ [Sb Cb Su] as %sv -',
                '· iframe Sb Cb Su',
                'try wp_auto'],
            'sharedEverythingSelector': ['try wp_auto',
                f'wp_apply (wp_slice_literal (V := {_LB}.Requirement) (l := [])); isplitr; (· ipureintro; rfl); iintro %se -',
                'try wp_auto'],
            'string2token': map_lit_steps('Hst', 'GoString', 'w64', 'go.string', f'{_LB}.Token.ty', 11),
            '$end': ['try wp_auto', f'wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mvs Hvs',
                     'try wp_auto']},
    finish=['ipersist HsharedEverythingSelector', 'ipersist HsharedNothingSelector'] + FIN_PRE[:6] +
           ['imodintro', 'unfold k8s_io.apiserver.pkg.storage.etcd3.labelsInit', 'isplitl []',
            '· iexists se; rw [show (W64 0 : w64) = W64 (go.arrayLiteralSize []) by rfl]; iexact HsharedEverythingSelector', '· iexists _; iexact HsharedNothingSelector'])
SPECIAL['k8s_io.apimachinery.pkg.util.runtime'] = dict(doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): `ReallyCrash` (`true`), `PanicHandlers` and `ErrorHandlers` (slice literals of
function values, one the closure `backoffError` returns, translated: it allocates a
`rudimentaryErrorBackoff` stamped with `time.Now()`).''',
    alloc_types=_ALLOC_ANY,
    before={'PanicHandlers': ['try wp_auto',
                'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sp -', 'try wp_auto'],
            'ErrorHandlers': ['try wp_auto', 'wp_func_call', 'wp_call', 'try wp_auto',
                'wp_apply _root_.Perennial.time.wp_Now as %t0 -', 'try wp_auto',
                'repeat (wp_alloc_anon; try wp_auto)',
                'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %se -', 'try wp_auto']})
_SETS_NEW = 'wp_apply (EtcdGrove.sets.New.wp_proof EtcdGrove.sets.Set.Insert.wp_proof)'
def _newstring_steps(tag, lst):
    """`sets.NewString(lst...)` (its slice literal, then `New[string]`'s spec): `H<tag>`, the set."""
    return ['try wp_auto',
            f'wp_apply (wp_slice_literal (l := {lst})); isplitr; (· ipureintro; rfl); iintro %sl{tag} ⟨S{tag}, -⟩',
            'try wp_auto', 'wp_func_call', 'wp_call', 'try wp_auto',
            f'{_SETS_NEW} $$ [S{tag}] as %r{tag} ⟨H{tag}, -⟩', '· iframe', 'try wp_auto']
SPECIAL['k8s_io.apiserver.pkg.endpoints.request'] = dict(doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): `sets.NewString` calls (`sets` with bodies: `New`'s spec), the last of
`namespaceSubresources.List()` (`List`'s).''',
    alloc_types=_ALLOC_ANY,
    imports=['Proof.k8s_io.apimachinery.pkg.util.sets.New', 'Proof.k8s_io.apimachinery.pkg.util.sets.Set__Insert',
             'Proof.k8s_io.apimachinery.pkg.util.sets.List', 'Proof.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList',
             'Perennial.Proof.slices.Link', 'Perennial.Proof.cmp.Link'],
    before={'specialVerbs': _newstring_steps('1', '[go!"proxy", go!"watch"]'),
            'specialVerbsNoSubresources': _newstring_steps('2', '[go!"proxy"]'),
            'namespaceSubresources': _newstring_steps('3', '[go!"status", go!"finalize"]'),
            'verbsWithSelectors': _newstring_steps('4', '[go!"list", go!"watch", go!"deletecollection"]'),
            'NamespaceSubResourcesForTest': ['try wp_auto', 'wp_method_call', 'wp_call', 'try wp_auto',
                'wp_method_call', 'wp_call', 'try wp_auto',
                'wp_func_call', 'wp_call', 'try wp_auto',
                'have hsz : GMap.size (EtcdGrove.sets.insertAll (∅ : GMap GoString EtcdGrove.sets.Elem) '
                '[go!"status", go!"finalize"]) ≤ 2 ^ 62 := '
                'Nat.le_trans (EtcdGrove.sets.size_insertAll_le _ _) (by simp [GMap.map_size_empty])',
                "wp_apply (EtcdGrove.sets.List'.wp_proof EtcdGrove.sets.Set.UnsortedList.wp_proof "
                '_root_.Perennial.slices.wp_Sort _root_.Perennial.cmp.wp_Less _ _ _ hsz) $$ [H3] '
                'as %sl5 %ks5 ⟨H3, S5, -⟩', '· iframe',
                'try wp_auto', 'wp_func_call', 'wp_call', 'try wp_auto',
                f'{_SETS_NEW} $$ [S5] as %r5 ⟨H5, -⟩', '· iframe', 'try wp_auto']})
SPECIAL['k8s_io.apiserver.pkg.util.flowcontrol'] = dict(doc='''Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s2, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): `readOnlyVerbs = sets.NewString(...)` (`sets` with bodies: `New`'s spec) and the
two interface assertions `var _ fmt.GoStringer = RequestDigest{}` and
`var _ fmt.GoStringer = (*priorityLevelState)(nil)` (conversions to an interface).''',
    alloc_types=_ALLOC_ANY,
    imports=['Proof.k8s_io.apimachinery.pkg.util.sets.New', 'Proof.k8s_io.apimachinery.pkg.util.sets.Set__Insert'],
    before={'readOnlyVerbs': _newstring_steps('1', '[go!"get", go!"list", go!"watch", go!"proxy"]')})
_AE = 'k8s_io.apimachinery.pkg.api.errors'
SPECIAL[_AE] = dict(doc='''Its fact (`apierrorsInit`, `storage/etcd3/Base.lean`; prove-k8s2, 2026-11-20, `True` until then):
`knownReasons` holds, read-only for good, the map of the 19 known reasons (`knownReasonsMap`), which
`IsTimeout` looks reasons up in. Its initializer initializes its imports, allocates its variables and
runs their translated initializers: `var _ error = &StatusError{}` and `knownReasons`, a map literal
of the 19 known reasons (prove-k8s, 2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).''',
    alloc_types={'knownReasons': 'Loc'},
    before={'knownReasons': ['try wp_auto', 'wp_alloc_anon'] + map_lit_steps('Hkr', 'GoString', 'Unit',
        'k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty', '(go.GoType.StructType [])', 19)},
    finish=['ipersist HknownReasons', 'ipersist Hkr'] + FIN_PRE[:6] + [
        'imodintro', 'unfold k8s_io.apiserver.pkg.storage.etcd3.apierrorsInit', 'iexists _',
        'iframe HknownReasons',
        'unfold EtcdGrove.apierrors.knownReasonsMap EtcdGrove.apierrors.knownReasons',
        'simp only [List.foldl]', 'iexact Hkr'])
SPECIAL['k8s_io.apimachinery.pkg.util.errors'] = newvars_cfg(dict(
    doc='''Its fact is `True`. Its initializer initializes its imports, allocates `ErrPreconditionViolated` and
runs its translated initializer, an `errors.New` call (prove-smallinits, 2026-11-20; until then the
trust-boundary axiom `opaqueInitsOk`).'''), ['ErrPreconditionViolated'])


def plain(ns):
    return ns.replace('«', '').replace('»', '')

def dirof(ns):
    return plain(ns).replace('.', '/')


# (mustreg, 2026-11-20) the packages whose translated `init()` only registers their metrics
# (`prometheus.MustRegister`): `PRE_RES`, their initializers given the rights to the names
# (`regNames`, checked by the proof against the constructors' `collectorName`), in `init()`'s
# order (`metrics.go`). Until then their `init()` was names only, the trust-boundary axiom
# `initFuncsOk` (the read package's since item 8).
_E, _S, _N, _D = 'etcd', 'server', 'network', 'etcd_debugging'
register(SPECIAL[_RD], _RD, [
    reg_scalar('slowReadIndex', _E, _S, 'slow_read_indexes_total', c='c1', n='N1'),
    reg_scalar('readIndexFailed', _E, _S, 'read_indexes_failed_total', c='c2', n='N2')])
register(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.membership'],
         'go_etcd_io.etcd.server.v3.etcdserver.api.membership', [
    reg_vec('ClusterVersionMetrics', 'Gauge', _E, 'cluster', 'version'),
    reg_vec('knownPeers', 'Gauge', _E, _N, 'known_peers'),
    reg_scalar('isLearner', _E, _S, 'is_learner')])
register(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp'],
         'go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp', [
    reg_vec('activePeers', 'Gauge', _E, _N, 'active_peers'),
    reg_vec('disconnectedPeers', 'Counter', _E, _N, 'disconnected_peers_total'),
    reg_vec('sentBytes', 'Counter', _E, _N, 'peer_sent_bytes_total'),
    reg_vec('receivedBytes', 'Counter', _E, _N, 'peer_received_bytes_total'),
    reg_vec('sentFailures', 'Counter', _E, _N, 'peer_sent_failures_total'),
    reg_vec('recvFailures', 'Counter', _E, _N, 'peer_received_failures_total'),
    reg_vec('snapshotSend', 'Counter', _E, _N, 'snapshot_send_success'),
    reg_vec('snapshotSendInflights', 'Gauge', _E, _N, 'snapshot_send_inflights_total'),
    reg_vec('snapshotSendFailures', 'Counter', _E, _N, 'snapshot_send_failures'),
    reg_vec('snapshotSendSeconds', 'Histogram', _E, _N, 'snapshot_send_total_duration_seconds'),
    reg_vec('snapshotReceive', 'Counter', _E, _N, 'snapshot_receive_success'),
    reg_vec('snapshotReceiveInflights', 'Gauge', _E, _N, 'snapshot_receive_inflights_total'),
    reg_vec('snapshotReceiveFailures', 'Counter', _E, _N, 'snapshot_receive_failures'),
    reg_vec('snapshotReceiveSeconds', 'Histogram', _E, _N, 'snapshot_receive_total_duration_seconds'),
    reg_vec('rttSec', 'Histogram', _E, _N, 'peer_round_trip_time_seconds')])
register(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.snap'],
         'go_etcd_io.etcd.server.v3.etcdserver.api.snap', [
    reg_scalar('snapMarshallingSec', _D, 'snap', 'save_marshalling_duration_seconds'),
    reg_scalar('snapSaveSec', _D, 'snap', 'save_total_duration_seconds'),
    reg_scalar('snapFsyncSec', _E, 'snap', 'fsync_duration_seconds'),
    reg_scalar('snapDBSaveSec', _E, 'snap_db', 'save_total_duration_seconds'),
    reg_scalar('snapDBFsyncSec', _E, 'snap_db', 'fsync_duration_seconds')])
register(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc'],
         'go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc', [
    reg_scalar('sentBytes', _E, _N, 'client_grpc_sent_bytes_total'),
    reg_scalar('receivedBytes', _E, _N, 'client_grpc_received_bytes_total'),
    reg_vec('streamFailures', 'Counter', _E, _N, 'server_stream_failures_total'),
    reg_vec('clientRequests', 'Counter', _E, _S, 'client_requests_total'),
    reg_scalar('watchSendLoopWatchStreamDuration', _D, _S, 'watch_send_loop_watch_stream_duration_seconds'),
    reg_scalar('watchSendLoopWatchStreamDurationPerEvent', _D, _S,
               'watch_send_loop_watch_stream_duration_per_event_seconds'),
    reg_scalar('watchSendLoopControlStreamDuration', _D, _S, 'watch_send_loop_control_stream_duration_seconds'),
    reg_scalar('watchSendLoopProgressDuration', _D, _S, 'watch_send_loop_progress_duration_seconds')])
register(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.apply'], 'go_etcd_io.etcd.server.v3.etcdserver.apply', [
    reg_vec('alarms', 'Gauge', _D, _S, 'alarms')])
register(SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.txn'], 'go_etcd_io.etcd.server.v3.etcdserver.txn', [
    reg_vec('applySec', 'Histogram', _E, _S, 'apply_duration_seconds'),
    reg_vec('rangeSec', 'Histogram', _E, _S, 'range_duration_seconds'),
    reg_scalar('slowApplies', _E, _S, 'slow_apply_total')])
register(SPECIAL['go_etcd_io.etcd.server.v3.storage'], 'go_etcd_io.etcd.server.v3.storage', [
    reg_scalar('quotaBackendBytes', _E, _S, 'quota_backend_bytes')])
register(SPECIAL['go_etcd_io.etcd.server.v3.storage.wal'], 'go_etcd_io.etcd.server.v3.storage.wal', [
    reg_scalar('walFsyncSec', _E, 'disk', 'wal_fsync_duration_seconds'),
    reg_scalar('walWriteSec', _E, 'disk', 'wal_write_duration_seconds'),
    reg_scalar('walWriteBytes', _E, 'disk', 'wal_write_bytes_total')])
# (etcdstorage, 2026-11-20, the user's decision: mvccrand's and mvccfull's closed theorems take
# `namesUnclaimed`) auth, lease, backend and mvcc. A `NewGaugeFunc` gauge's `collectorName` fact is
# conditional on its name's validity (`N<x> : nameOk ... → collectorName ...`), `decide`d here.
def reg_gfunc(x, ns, sub, name):
    return reg_scalar(x, ns, sub, name, n=f'(N{x} (by decide))')
register(SPECIAL['go_etcd_io.etcd.server.v3.auth'], 'go_etcd_io.etcd.server.v3.auth', [
    reg_gfunc('currentAuthRevision', _D, 'auth', 'revision')])
register(SPECIAL['go_etcd_io.etcd.server.v3.lease'], 'go_etcd_io.etcd.server.v3.lease', [
    reg_scalar('leaseGranted', _D, 'lease', 'granted_total'),
    reg_scalar('leaseRevoked', _D, 'lease', 'revoked_total'),
    reg_scalar('leaseRenewed', _D, 'lease', 'renewed_total'),
    reg_scalar('leaseTotalTTLs', _D, 'lease', 'ttl_total')])
register(SPECIAL['go_etcd_io.etcd.server.v3.storage.backend'], 'go_etcd_io.etcd.server.v3.storage.backend', [
    reg_scalar('commitSec', _E, 'disk', 'backend_commit_duration_seconds'),
    reg_scalar('rebalanceSec', _D, 'disk', 'backend_commit_rebalance_duration_seconds'),
    reg_scalar('spillSec', _D, 'disk', 'backend_commit_spill_duration_seconds'),
    reg_scalar('writeSec', _D, 'disk', 'backend_commit_write_duration_seconds'),
    reg_scalar('defragSec', _E, 'disk', 'backend_defrag_duration_seconds'),
    reg_scalar('defragBlockingSec', _E, 'disk', 'backend_defrag_blocking_duration_seconds'),
    reg_scalar('snapshotTransferSec', _E, 'disk', 'backend_snapshot_duration_seconds'),
    reg_scalar('isDefragActive', _E, 'disk', 'defrag_inflight')])
_MVR = 'mvcc'
# (prom-registry, 2026-11-23) mvcc's 23 registrations, each over its collector's (persistent `IProp`)
# `collectorName` and an `idToks` right, past the default recursion depth at the last one
SPECIAL[_MV]['rec_depth'] = 20000
register(SPECIAL[_MV], _MV, [
    reg_scalar('rangeCounter', _E, _MVR, 'range_total'),
    reg_scalar('putCounter', _E, _MVR, 'put_total'),
    reg_scalar('deleteCounter', _E, _MVR, 'delete_total'),
    reg_scalar('txnCounter', _E, _MVR, 'txn_total'),
    reg_scalar('keysGauge', _D, _MVR, 'keys_total'),
    reg_scalar('watchStreamGauge', _D, _MVR, 'watch_stream_total'),
    reg_scalar('watcherGauge', _D, _MVR, 'watcher_total'),
    reg_scalar('slowWatcherGauge', _D, _MVR, 'slow_watcher_total'),
    reg_scalar('totalEventsCounter', _D, _MVR, 'events_total'),
    reg_scalar('pendingEventsGauge', _D, _MVR, 'pending_events_total'),
    reg_scalar('indexCompactionPauseMs', _D, _MVR, 'index_compaction_pause_duration_milliseconds'),
    reg_scalar('dbCompactionPauseMs', _D, _MVR, 'db_compaction_pause_duration_milliseconds'),
    reg_scalar('dbCompactionTotalMs', _D, _MVR, 'db_compaction_total_duration_milliseconds'),
    reg_scalar('dbCompactionLast', _D, _MVR, 'db_compaction_last'),
    reg_scalar('dbCompactionKeysCounter', _D, _MVR, 'db_compaction_keys_total'),
    reg_gfunc('dbTotalSize', _E, _MVR, 'db_total_size_in_bytes'),
    reg_gfunc('dbTotalSizeInUse', _E, _MVR, 'db_total_size_in_use_in_bytes'),
    reg_gfunc('dbOpenReadTxN', _E, _MVR, 'db_open_read_transactions'),
    reg_scalar('hashSec', _E, _MVR, 'hash_duration_seconds'),
    reg_scalar('hashRevSec', _E, _MVR, 'hash_rev_duration_seconds'),
    reg_gfunc('currentRev', _D, _MVR, 'current_revision'),
    reg_gfunc('compactRev', _D, _MVR, 'compact_revision'),
    reg_scalar('totalPutSizeGauge', _D, _MVR, 'total_put_size_in_bytes')])


# (prom-registry, route (b), 2026-11-22: notes/prom-registry.md) prometheus's default registry is the real
# client_golang code (translated with its bodies): its initializer allocates `defaultRegistry`,
# `DefaultRegisterer` and `DefaultGatherer`, runs `defaultRegistry = NewRegistry()` (stepped into: three empty
# map literals and the struct) and the two interface conversions, and then its `init()`, whose trusted model
# (`TrustedCode/github_com/prometheus/client_golang/prometheus.lean`) inserts the built-in collectors' IDs and
# names into the registry's maps (`EtcdGrove.prometheus.wp_seed_insertAll`). Until then `defaultRegistry.init`,
# `DefaultRegisterer.init` and `DefaultGatherer.init` were in `opaqueInitsOk` and `init.«0»` the trust-boundary
# axiom `initFuncsOk`.
SPECIAL['github_com.prometheus.client_golang.prometheus'] = dict(
    doc='''Its fact (`promInit γ`, `PkgInit.lean`, at the run's registry ghost name `γ`, the parameter
`PromRegGS` of the package's fact; route (b), Option 4, 2026-11-22, notes/prom-registry.md): `defaultRegistry`
and `DefaultRegisterer` hold the default registry, read-only, a registry over `γ` (`isRegistry`). Its
initializer initializes its imports and runs its translated variable initializers (the others are goose
`[[skip]]` entries, mit-pdos/etcd-grove#23): `defaultRegistry = NewRegistry()` (stepped into) and `DefaultRegisterer`/`DefaultGatherer`,
`defaultRegistry` converted to an interface; then its `init()`, whose trusted model inserts the built-in
collectors' descriptor IDs, names and collector IDs into the registry's maps
(`EtcdGrove.prometheus.wp_seed_insertAll`); the registry's lock is then made the guard of its invariant
(`EtcdGrove.prometheus.isRegistry_init`: the built-ins need no right). (Until 2026-11-22 its fact was `True`;
until step 1 of route (b) `defaultRegistry.init`, `DefaultRegisterer.init` and `DefaultGatherer.init` were
among `opaqueInitsOk`, and `init.«0»` was the trust-boundary axiom `initFuncsOk`.)''',
    imports=['Proof.github_com.prometheus.client_golang.prometheus.Seed'],
    vars=[PROMREG_VAR],
    table_vars=[PROMREG_VAR],
    alloc_types={'defaultRegistry': 'Loc', 'DefaultRegisterer': 'GoInterface', 'DefaultGatherer': 'GoInterface'},
    before={'defaultRegistry': [
        'try wp_auto',
        'wp_func_call', 'wp_call', 'try wp_auto',
        'wp_apply (wp_map_make1 (K := w64) (V := GoInterface) go.uint64 github_com.prometheus.client_golang.prometheus.Collector.ty) as %mC HmC',
        'try wp_auto',
        'wp_apply (wp_map_make1 (K := w64) (V := Unit) go.uint64 (go.GoType.StructType [])) as %mD HmD',
        'try wp_auto',
        'wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string go.uint64) as %mN HmN',
        'try wp_auto']},
    after={'init.«0»': [
        'simp only [EtcdGrove.prometheus.seed_Registry_eq, EtcdGrove.prometheus.seed_Collector_eq,'
        ' EtcdGrove.prometheus.seed_defaultRegistry_eq]',
        'try wp_auto',
        'wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := w64) (V := Unit) go.uint64 (fun id => (id, ()))'
        ' github_com.prometheus.client_golang.prometheus.seed.descIDs) $$ HmD as HmD',
        'try wp_auto',
        'wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := GoString) (V := w64) go.string (fun nd => nd)'
        ' github_com.prometheus.client_golang.prometheus.seed.dims) $$ HmN as HmN',
        'try wp_auto',
        'wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := w64) (V := GoInterface) go.uint64'
        ' (fun id => (id, (interface.nil : GoInterface))) github_com.prometheus.client_golang.prometheus.seed.collectorIDs) $$ HmC as HmC',
        'try wp_auto',
        '-- the registry: its fields, and its lock the guard of its invariant (`isRegistry`)',
        'irename «$r0» => Hreg0',
        'iStructNamed Hreg0',
        'imod (EtcdGrove.prometheus.isRegistry_init (GF := GF) (EtcdGrove.prometheus.PromRegGS.γ (GF := GF)) _ mC mD mN _ _ _'
        ' EtcdGrove.prometheus.seed_C_builtin EtcdGrove.prometheus.seed_D_builtin EtcdGrove.prometheus.seed_N_builtin)'
        ' $$ mtx collectorsByID descIDs dimHashesByName HmC HmD HmN with #Hreg',
        'ipersist HdefaultRegistry',
        'ipersist HDefaultRegisterer']},
    finish=['ihave #Hfact : (github_com.prometheus.client_golang.prometheus.promInit'
            ' (EtcdGrove.prometheus.PromRegGS.γ (GF := GF)) : IProp GF) $$ []',
            '· iunfold github_com.prometheus.client_golang.prometheus.promInit',
            '  iexists _',
            '  iframe #',
            'iframe Hown', 'imodintro', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
            'is_pkg_init_finish'],
)


def closure(p):
    seen = set(); st = [p]
    while st:
        q = st.pop()
        if q in seen: continue
        seen.add(q); st += inv[q]['imports']
    return seen

def init_module(q):
    d = inv[q]
    if q in RAFT_INIT:
        return 'Proof.go_etcd_io.raft.v3.Init'
    if q == 'k8s_io.utils.third_party.forked.golang.btree':
        return 'Proof.k8s_io.utils.third_party.forked.golang.btree.initialize'
    if d['perennial'] and q not in PERENNIAL_HERE:
        return 'Perennial.Proof.' + plain(q) + '.Link'
    return 'Proof.' + plain(q) + '.Init'

def init_thm(q):
    if q == 'k8s_io.utils.third_party.forked.golang.btree':
        return '_root_.Perennial.EtcdGrove.btree.initialize.wp_proof'
    return '_root_.Perennial.' + q + '.wp_initialize\''

def hyps(p):
    """The assumed packages below `p`: its theorem's hypotheses, in order."""
    return sorted(q for q in closure(p) if q in ASSUMED and q != p)


def init_call(q):
    """The term proving `q`'s initializer's spec."""
    if q in ASSUMED:
        return ASSUMED[q][1]
    h = hyps(q)
    if h:
        return '(' + init_thm(q) + ' ' + ' '.join(ASSUMED[x][1] for x in h) + ')'
    return init_thm(q)


def res_list(p):
    """The packages below `p` (or `p`) whose initializers need a resource (`PRE_RES`), sorted (any
    number of `p`'s imports may lead to each: the `_res` form spends each once)."""
    return [q for q in sorted(closure(p)) if q in PRE_RES]


def qs_lit(rs):
    """The literal list of the packages `rs` with their metric names and other IDs (`regQs`' elements)."""
    return '[' + ', '.join(f'(pkg_id.{q}, _root_.Perennial.{q}.regNames, _root_.Perennial.{q}.regKeys)'
                           for q in rs) + ']'


def sublist_term(big, small):
    """A term of `small <+ big` (`List.Sublist`), over two sorted lists of `PRE_RES` packages
    (as `qs_lit` writes them)."""
    t, close, i = '', 0, 0
    for q in big:
        if i < len(small) and small[i] == q:
            t += 'List.Sublist.cons₂ _ ('; i += 1
        else:
            t += 'List.Sublist.cons _ ('
        close += 1
    assert i == len(small), (big, small)
    return t + 'List.Sublist.slnil' + ')' * close


def external(q):
    """`q`'s `wp_initialize'` is not generated here (Perennial's, raft's, the B-tree's)."""
    return (q in RAFT_INIT or q == 'k8s_io.utils.third_party.forked.golang.btree' or
            (inv[q]['perennial'] and q not in PERENNIAL_HERE))


def ext_ctor(q):
    # (`unsafe` is a Lean keyword: its constructor is `unsafe_`)
    n = plain(q).replace('.', '_')
    return n + '_' if n == 'unsafe' else n


# (L1, 2026-11-24) The external initializers each generated file names (`ExternalInit.<ctor>`),
# recorded while generating, for the registrations (`gen_ext`): a Perennial package's goes to the
# shared `Proof/runtime/PkgInitExt.lean`, any other (raft's, protobuf's `proto`, the B-tree's; a
# part's own translations) to the registration module of the tree being generated, `EXT_LOCAL_MOD`
# (the main tree's `Proof/runtime/PkgInitExtRaft.lean`; a part's: `Dsverify/`'s `PkgInitDsv`), which
# a generated file that names one imports beside the shared one.
EXT_LOCAL_MOD = 'Proof.runtime.PkgInitExtRaft'
EXT_SHARED = {}  # the shared module's registrations: package -> its translation's module
EXT_MAIN = {}  # the main tree's `PkgInitExtRaft`'s
EXT_RECORD = EXT_MAIN  # where the tree being generated records its own (a part's: a dict of its own)
_EXT_CALL = set()  # the non-Perennial externals named by the current `gen` call


def ext_shared(q):
    """`q`'s translation is Perennial's: its registration is the shared module's."""
    return code_module(q).startswith('Perennial.')


def lb_term(q, hin):
    """A proof of `∀ σ0, {{ ownInitLb g σ0 }} q.initialize' #() {{ ... }}` (`hin`: its
    `GetIsPkgInitProp`)."""
    assert q not in ASSUMED, q
    if external(q):
        if ext_shared(q):
            EXT_SHARED[q] = code_module(q)
        else:
            EXT_RECORD[q] = code_module(q)
            _EXT_CALL.add(q)
        return (f'(EtcdGrove.initLb_of_spec pkg_id.{q} _root_.Perennial.{q}.initialize\'\n'
                f'      EtcdGrove.ExternalInit.{ext_ctor(q)} {init_thm(q)} _ {hin})')
    return f'(_root_.Perennial.{q}.wp_initialize\'_lb _ {hin})'


def pkginfo_imports(p):
    t = open(inv[p]['file']).read()
    m = re.search(r"instance info' : PkgInfo pkg_id\.\S+ where\n  pkgImportedPkgs := \[(.*)\]", t)
    if not m or not m.group(1).strip():
        return []
    return [x.strip()[len('pkg_id.'):] for x in m.group(1).split(',')]

def exec_order(p):
    """The initializer's statements in execution order: ('import', q) / ('opaque', X) /
    ('trusted', X) / ...."""
    d = inv[p]
    t = open(d['file']).read()
    i = t.find("noncomputable def initialize'")
    j = t.find("\n\n", i)
    body = t[i:j]
    items = []
    for m in re.finditer(r"\(Val _root_\.Perennial\.(\S+)\.initialize'\)|\(Val ([^\s()]+)\.init\)|go\.GlobalAlloc (\S+) |GlobalVarAddr (\S+)\)|FuncResolve (init\.«\d+») \[\]", body):
        if m.group(1):
            items.append(('import', m.group(1)))
        elif m.group(2):
            # an untranslated initializer (an `opaque` of the translation since Perennial
            # f551a1b46, an `axiom` before), or a trusted variable's model (in `TrustedCode/`)
            x = m.group(2)
            kind = 'opaque' if f'opaque {x}.init ' in t or f'axiom {x}.init ' in t else 'trusted'
            items.append((kind, m.group(2)))
        elif m.group(3):
            items.append(('alloc', m.group(3)))
        elif m.group(4):
            items.append(('store', m.group(4)))
        else:
            # a `func init()`, `init.<k>` (as gc names them): unfolded if translated or trusted
            # (its `FuncUnfold` is an `Assumptions` field, in the package's index file when the
            # translation is in chunks: 2026-11-07 for a trusted one; k8s-inits-2, 2026-11-24, for a
            # translated one too, which until then kept its axiom)
            idx = re.sub(r'/chunk\d+\.lean$', '.lean', d['file'])
            tg = ''
            if idx != d['file'] and os.path.exists(idx):
                tg = open(idx).read()
            kind = 'initfn' if f'FuncUnfold {m.group(5)} [] ' in t + tg else 'opaqueinitfn'
            items.append((kind, m.group(5)))
    items.reverse()
    return items

def _tier_mod():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'tier_check', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tier-check.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


_TIER = None
_PROOFISH = {}


def proofish(m):
    """Whether the module `m` of this repository is a proof or linking module
    (`etc/tier-check.py`): an import only a linking module may have."""
    global _TIER
    if m not in _PROOFISH:
        f = m.replace('.', '/') + '.lean'
        if m.endswith('.InitLinked'):
            _PROOFISH[m] = True
        elif not os.path.exists(f):
            _PROOFISH[m] = False
        else:
            if _TIER is None:
                _TIER = _tier_mod()
            _PROOFISH[m] = _TIER.tier(m, open(f).read(), _TIER.linking_list()) in ('proof', 'linking')
    return _PROOFISH[m]


_SPLIT = {}
# the configurations of the tree being generated, over `SPECIAL` (a part's: `WT_SPECIAL`, ...)
CFG_OVERRIDE = {}


def split(p):
    """Whether `p`'s `Init.lean` is split into its facts (`Init`, defs tier) and its
    `wp_initialize'` (`InitLinked`, linking; import tiers, 2026-11-19): when the proof applies a
    proof or linking module's theorem, its own imports' or (through an import's `InitLinked`) one
    below. A key of `inv` at the time of the call (the parts' trees replace `inv`)."""
    key = (p, id(inv), id(CFG_OVERRIDE))
    if key not in _SPLIT:
        _SPLIT[key] = False
        cfg = CFG_OVERRIDE.get(p) or SPECIAL.get(p) or {}
        imps = [x for (kind, x) in exec_order(p) if kind == 'import']
        _SPLIT[key] = (any(proofish(m) for m in cfg.get('imports', []))
                       or any(q not in ASSUMED and (proofish(init_module(q))
                                                     or (not external(q) and split(q)))
                              for q in imps))
    return _SPLIT[key]


def linked_module(q):
    """The module of `q`'s `wp_initialize'`."""
    if q in ASSUMED:
        return ASSUMED[q][0]
    if not external(q) and split(q):
        return 'Proof.' + plain(q) + '.InitLinked'
    return init_module(q)


def gen(p, cfg=None):
    """`_gen`'s files, each that names a non-Perennial external initializer importing the tree's
    registrations (`EXT_LOCAL_MOD`) beside the shared ones."""
    _EXT_CALL.clear()
    outs = _gen(p, cfg)
    base = 'public import Proof.runtime.PkgInitExt\n'
    res = []
    for path, txt in outs:
        if any(f'EtcdGrove.ExternalInit.{ext_ctor(q)} ' in txt for q in _EXT_CALL):
            assert base in txt, path
            txt = txt.replace(base, base + f'public import {EXT_LOCAL_MOD}\n', 1)
        res.append((path, txt))
    return res


def _gen(p, cfg=None):
    cfg = cfg or {}
    newvars = cfg.get('newvars', {})
    custom = cfg.get('custom', {})
    d = inv[p]
    k = plain(p)
    imods = inst.get(k) or inst.get(p)
    inst_mod = PERENNIAL_INST[p] if p in PERENNIAL_INST else (
        imods[0][0][1:] if imods[0][0].startswith('@') else 'Proof.' + imods[0][0].replace('/', '.'))
    cl = closure(p)
    needs_ctx = 'context' in cl
    needs_raft = 'go_etcd_io.raft.v3' in cl
    pk = pkginfo_imports(p)
    items = exec_order(p)
    opq = [x for (kind, x) in items if kind == 'opaque' and x not in newvars and x not in custom]
    custom_initfn = cfg.get('custom_initfn', {})
    opqf = [x for (kind, x) in items if kind == 'opaqueinitfn' and x not in custom_initfn]
    trs = [x for (kind, x) in items if kind == 'trusted']
    imps = [x for (kind, x) in items if kind == 'import']
    assert sorted(imps) == sorted(pk), (p, imps, pk)
    # (mustreg) the registration rights' definitions (`regNames`: prometheus's `fqName`) and lemmas
    cfg_imps = list(cfg.get('imports', []))
    if res_list(p):
        for m in ['Proof.github_com.prometheus.client_golang.prometheus.Registry', 'Proof.runtime.PkgInitRes']:
            if m not in cfg_imps:
                cfg_imps.append(m)
    for m in ['Proof.github_com.prometheus.client_golang.prometheus.MustRegister',
              'Proof.github_com.prometheus.client_golang.prometheus.Registry__MustRegister',
              'Proof.github_com.prometheus.client_golang.prometheus.Registry__Register']:
        if p in PRE_RES and m not in cfg_imps:
            cfg_imps.append(m)
    mods = [inst_mod] + sorted({ASSUMED[q][0] if q in ASSUMED else init_module(q) for q in imps}) + cfg_imps
    if newvars: mods.append('Proof.errors.NewVarCell')
    mods.append('Proof.runtime.PkgInitExt')
    sp = split(p)
    if sp:
        # (import tiers, 2026-11-19) the facts module imports no proof or linking module: the
        # imports' facts (`Init`), not their `InitLinked`; the proofs the `wp_initialize'` applies
        # go to the linking module
        facts_mods = [inst_mod] + sorted({init_module(q) for q in imps
                                          if not proofish(init_module(q))}) + \
            [m for m in cfg_imps if not proofish(m)]
        if newvars: facts_mods.append('Proof.errors.NewVarCell')
        linked_mods = [f'Proof.{plain(p)}.Init'] + sorted({linked_module(q) for q in imps}) + \
            [m for m in cfg_imps if proofish(m)] + ['Proof.runtime.PkgInitExt']
    lines = []
    A = lines.append
    A('/-')
    A(f'Package initialization of `{p}`')
    A('(item 8, 2026-10-17): its `wp_initialize\'`.')
    A('')
    if 'doc' in cfg:
        A(cfg['doc'])
    elif trs and not opq and not opqf:
        A('Its fact is `True`. Its initializer initializes its imports and runs the trusted')
        A('initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).')
    elif opq and opqf:
        A('Its fact is `True`. Its initializer initializes its imports, runs the untranslated')
        A('initializers of its variables (`X.init`, axioms of the translation), which the')
        A('trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated')
        A('`init` functions, which the trust-boundary axiom `initFuncsOk` says return.')
    elif opq:
        A('Its fact is `True`. Its initializer initializes its imports and runs the untranslated')
        A('initializers of its variables (`X.init`, axioms of the translation), which the')
        A('trust-boundary axiom `opaqueInitsOk` says run without panicking.')
    elif opqf:
        A('Its fact is `True`. Its initializer initializes its imports and runs its untranslated')
        A('`init` functions, which the trust-boundary axiom `initFuncsOk` says return (it has no')
        A('initialized variable).')
    else:
        A('Its fact is `True`. Its initializer initializes its imports (it has no initialized')
        A('variable).')
    A('-/')
    A('module')
    A('')
    i_imports = len(lines)
    for m in mods:
        A(f'public import {m}')
    j_imports = len(lines)
    A('')
    A('@[expose] public section')
    A('')
    A('set_option linter.iris.style.nameCheck false')
    A('set_option linter.unusedSectionVars false')
    A('set_option linter.iris.dupNamespace false')
    A('')
    A('noncomputable section')
    A('')
    A('namespace Perennial')
    A('')
    A('/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/')
    A('local macro "mem_tac" : tactic =>')
    A('  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))')
    A('')
    A('open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode')
    A('')
    if opq or opqf or newvars or custom or custom_initfn:
        A('section opaqueInits')
        A(f'namespace {p}')
        A('variable [GooseExts] [GooseSemantics] [GooseInterp]')
        A('variable [go_gctx : GoGlobalContext]')
        A('variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]')
        A('variable [sem : go.Semantics]')
        A('')
        if opq:
            A(f'/-- **The trust boundary: `{p}`\'s untranslated variable initializers run.**')
            A('Goose translates them names-only, so each `X.init` is an axiom of the translation; Go')
            A('runs them at program start, and etcd starts, so each returns without panicking.')
            for l in cfg.get('opaque_doc_extra', []):
                A(l)
            A('Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/')
            A('axiom opaqueInitsOk :')
            A('    ∀ v ∈ ([' + ',\n        '.join(f'{x}.init' for x in opq) + '] : List val),')
            A('    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}')
            A('')
        if opqf:
            A(f'/-- **The trust boundary: `{p}`\'s untranslated `init` functions return.** Goose')
            A('names a package\'s `func init()`s `init.<k>`, as gc does, and translates them names-only')
            A('here, so the model does not unfold them (`@! init.<k>`: the semantics\' `functions`, which')
            A('the package\'s `Assumptions` do not constrain for them). Go runs them at program start, and')
            A('etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of')
            A('other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/')
            A('axiom initFuncsOk :')
            A('    ∀ f ∈ ([' + ', '.join(opqf) + '] : List GoString),')
            A('    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}')
            A('')
        if newvars:
            A(f'/-- **The trust boundary: `{p}`\'s variables initialized by `errors.New`.** Each')
            A('listed `X.init` (untranslated) runs Go\'s `var X = errors.New(msg)`, as its Go source has')
            A('it, the fresh `errorString`\'s `s` field holding `msg` (`errStrCell`, D19k). -/')
            A('axiom errorsNewVarsInit :')
            A('    ∀ (init : val) (X msg : GoString), (init, X, msg) ∈ ([' + ',\n        '.join(f'({x}.init, {x}, go!{json.dumps(m)})' for x, m in newvars.items()) + '] : List (val × GoString × GoString)) →')
            A('    EtcdGrove.errorsNewVarInitC (GF := GF) init X msg')
            A('')
        for x, c in custom.items():
            # (sweep repairs 1, B5, 2026-11-08) optional `binder` (`∀ g : T,`) and `pre`: an
            # initializer that reads another variable's value (`DefaultFeatureGate =
            # DefaultMutableFeatureGate`)
            A(c['doc'])
            A(f'axiom {x}_init :' + (f' {c["binder"]}' if 'binder' in c else ''))
            A(f'    {{{{ ({c.get("pre", "True")} : IProp GF) }}}} (App (Val {x}.init) (Val #()))')
            A(f'    {{{{ RET #(); {c["post"]} }}}}')
            A('')
        for x, c in custom_initfn.items():
            # (sweep repairs 1, B5, 2026-11-08) an untranslated `init` function with a spec of its
            # own (`k8s.io/apiserver/pkg/features`' registration), instead of `initFuncsOk`'s `True`
            A(c['doc'])
            A(f'axiom {c["name"]} :' + (f' {c["binder"]}' if 'binder' in c else ''))
            A(f'    {{{{ ({c.get("pre", "True")} : IProp GF) }}}} (App (Val (@! {x})) (Val #()))')
            A(f'    {{{{ RET #(); {c["post"]} }}}}')
            A('')
        A(f'end {p}')
        A('end opaqueInits')
        A('')
    for l in cfg.get('pre', []):
        A(l)
    rl = res_list(p)
    if rl:
        # (mustreg, 2026-11-20) the metric names the closure's initializers register (`PRE_RES`)
        A(f'namespace {p}')
        A('')
        if p in PRE_RES:
            A('/-- The fully-qualified names of the metrics this package\'s `init()` registers with')
            A('prometheus\'s default registry, in its order (`MustRegister`; `metrics.go`). -/')
            A('def regNames : List GoString :=')
            A('  [' + ',\n   '.join(f'EtcdGrove.prometheus.fqName go!"{a}" go!"{b}" go!"{c}"'
                                   for (_, _, _, (a, b, c)) in PRE_RES[p]) + ']')
            A('')
            A('/-- The IDs besides its names\' this package\'s initializer takes the rights to (prom-registry:')
            A('a later registration\'s, `REG_KEYS`). -/')
            A(f'def regKeys : List w64 := {REG_KEYS.get(p, "[]")}')
            A('')
        A('/-- The packages of this package\'s import closure (itself included) whose initializers')
        A('register metrics, with their names and other IDs: their registration rights (keyed by ID,')
        A('`EtcdGrove.prometheus.regRes`) are its initializer\'s resources (`ownInitResL`,')
        A('`Proof/runtime/PkgInitRes.lean`; its `wp_initialize\'`\'s precondition: `regsFree regQs`). -/')
        A(f'def regQs : List (GoString × List GoString × List w64) :=\n  {qs_lit(rl)}')
        A('')
        A(f'end {p}')
        A('')
    i_init = len(lines)
    A('section init')
    A('variable [GooseExts] [GooseSemantics] [GooseInterp]')
    A('variable [go_gctx : GoGlobalContext]')
    A('variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]')
    A('variable [sem : go.Semantics]')
    A(f'variable [package_sem : _root_.Perennial.{p}.Assumptions]')
    _SP = {**SPECIAL, **WT_SPECIAL}
    vs = list(cfg.get('vars', []))
    for q in sorted(cl):
        for v in _SP.get(q, {}).get('vars', []):
            if v not in vs: vs.append(v)
    for v in vs:
        A(f'variable {v}')
    if needs_raft and '[_root_.Perennial.log.NewModel]' not in vs:
        A('variable [_root_.Perennial.log.NewModel]')
    A('')
    A(f'namespace {p}')
    A('')
    if len(items) > 50 or cfg.get('heavy'):
        A('set_option maxHeartbeats 8000000 in')
    if cfg.get('rec_depth'):
        # (prove-rpcmap, 2026-11-20) an initializer too deep for the default (`rpctypes`' 180 variables)
        A(f"set_option maxRecDepth {cfg['rec_depth']} in")
    assert not hyps(p), p
    form = 'self' if p in PRE_RES else ('res' if rl else 'lb')
    # the resource list the body sees (`self`: without `p`'s own entry) and its literal
    body_rl = [q for q in rl if q != p]
    body_L = f'EtcdGrove.regResL (GF := GF) {qs_lit(body_rl)}' if form == 'self' else \
        'EtcdGrove.regResL (GF := GF) regQs'
    st = f'pkg_id.{p}'
    if form == 'lb':
        A('theorem wp_initialize\'_lb (get_is_pkg_init : GoString → IProp GF)')
        A(f'    (Hinit : GetIsPkgInitProp {st} get_is_pkg_init) (σ0 : GMap GoString Bool) :')
        A('    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}')
        A(f'      (App (Val initialize\') (Val #()))')
        A('    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗')
        A(f'        isPkgInit (PROP := IProp GF) {st} }}}} := by')
        A('  wp_start as Hown')
        A('  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ')
        A('  iframe Hown')
        A('  iintro Hown')
    else:
        rres = 'EtcdGrove.regResL (GF := GF) regQs'
        A('theorem wp_initialize\'_res (get_is_pkg_init : GoString → IProp GF)')
        A(f'    (Hinit : GetIsPkgInitProp {st} get_is_pkg_init) :')
        A(f'    {{{{ EtcdGrove.ownInitResL get_is_pkg_init ({rres}) }}}}')
        A(f'      (App (Val initialize\') (Val #()))')
        A(f'    {{{{ RET #(); EtcdGrove.ownInitResL get_is_pkg_init ({rres}) ∗')
        A(f'        isPkgInit (PROP := IProp GF) {st} }}}} := by')
        A('  wp_start as Hown')
        if form == 'self':
            i = rl.index(p)
            A('  iapply EtcdGrove.wp_package_init_resL_self (heq := Hinit.1) (L := EtcdGrove.regResL (GF := GF) regQs)')
            A(f'    (L1 := EtcdGrove.regResL (GF := GF) {qs_lit(rl[:i])})')
            A(f'    (L2 := EtcdGrove.regResL (GF := GF) {qs_lit(rl[i + 1:])})')
            A(f'    (L\' := {body_L})')
            A('    (R := EtcdGrove.prometheus.idToks (GF := GF) (EtcdGrove.prometheus.PromRegGS.γ (GF := GF))')
            A('      (regNames.map EtcdGrove.prometheus.descId ++ regKeys))')
            A('    (hL := rfl) (hL\' := rfl) $$ [Hown] HΦ')
            A('  iframe Hown')
            A('  iintro ⟨Hown, HR⟩')
            A(f'  iunfold _root_.Perennial.{p}.regNames at HR')
        else:
            A('  iapply EtcdGrove.wp_package_init_resL (heq := Hinit.1) $$ [Hown] HΦ')
            A('  iframe Hown')
            A('  iintro Hown')
    A('  wp_auto')
    if 'finish' in cfg:
        A('  iapply wp_fupd')

    def hdsub(l):
        # `{Hd:<pkg>}`: the name of the import's fact, by its position among the imports
        return re.sub(r'\{Hd:([\w.]+)\}', lambda m: f'Hd{pk.index(m.group(1)) + 1}', l)
    before = dict(cfg.get('before', {}))
    for kind, x in items:
        if kind in ('initfn', 'opaqueinitfn'):
            # the `init` functions run after every variable initializer: `$inits`' steps first
            for l in before.pop('$inits', []):
                A('  ' + hdsub(l))
        if kind == 'opaque' and x in before:
            for l in before.pop(x):
                A('  ' + hdsub(l))
        if kind == 'import':
            idx = pk.index(x) + 1
            hin = f'Hinit{".2" * idx}.1'
            xrl = [] if (external(x) or x in ASSUMED) else res_list(x)
            if form == 'lb':
                A(f'  wp_apply {lb_term(x, hin)} _ $$ Hown as ⟨Hown, #Hd{idx}⟩')
            elif xrl:
                # (mustreg) an import with some of the list's packages: the others passed on
                A(f'  wp_apply (EtcdGrove.initResL_sub _ ({body_L})')
                A(f'      (EtcdGrove.regResL (GF := GF) _root_.Perennial.{x}.regQs)')
                A(f'      (List.Sublist.map _ ({sublist_term(body_rl, xrl)}))')
                A(f'      _ _ (_root_.Perennial.{x}.wp_initialize\'_res _ {hin}))')
                A(f'    $$ Hown as ⟨Hown, #Hd{idx}⟩')
            else:
                A(f'  wp_apply (EtcdGrove.initResL_carry _ _ _ _ {lb_term(x, hin)})')
                A(f'    $$ Hown as ⟨Hown, #Hd{idx}⟩')
        elif kind == 'opaque' and x in newvars:
            A(f'  wp_apply (errorsNewVarsInit {x}.init {x} go!{json.dumps(newvars[x])} (by mem_tac))\n    as ⟨%x{x}, H{x}, #M{x}, #C{x}⟩')
        elif kind == 'opaque' and x in custom and 'apply' in custom[x]:
            for l in custom[x]['apply']:
                A('  ' + hdsub(l))
        elif kind == 'opaque' and x in custom:
            A(f'  wp_apply {x}_init as {custom[x]["pat"].replace("@", x)}')
        elif kind == 'opaqueinitfn' and x in custom_initfn:
            for l in custom_initfn[x]['apply']:
                A('  ' + hdsub(l))
        elif kind == 'opaque':
            A(f'  wp_apply (opaqueInitsOk {x}.init (by mem_tac))')
        elif kind == 'trusted' and x in cfg.get('trusted', {}):
            # (2026-11-07) a trusted initializer with steps of its own (`os.Stderr`'s model)
            A(f'  -- {x}: its trusted initializer')
            for l in cfg['trusted'][x]:
                A('  ' + hdsub(l))
        elif kind == 'trusted':
            A(f'  wp_call  -- {x}: its trusted initializer does nothing')
        elif kind == 'opaqueinitfn':
            A(f'  wp_apply (initFuncsOk {x} (by mem_tac))')
        elif kind == 'initfn':
            A(f'  -- the translated {x}')
            A('  wp_func_call')
            A('  wp_call')
            A('  try wp_auto')
            # the hand-written steps of its body (`after`, keyed by the function's name)
            for l in cfg.get('after', {}).get(x, []):
                A('  ' + hdsub(l))
        elif kind == 'alloc':
            # (a quoted name, `«α»`, is no Iris hypothesis name: `Hα`)
            A(f'  wp_apply wp_GlobalAlloc (V := {cfg.get("alloc_types", {}).get(x, "TODO")}) {x} _ as H{x.strip("«»")}')
        else:
            A(f'  -- translated initializer of {x}')
            # (2026-10-23) steps before a translated initializer too (a constant to unfold)
            # (the store's match keeps the closing parentheses: `X))`)
            for l in before.pop(x.rstrip(')'), []):
                A('  ' + hdsub(l))
    for l in before.pop('$inits', []) + before.pop('$end', []):
        A('  ' + hdsub(l))
    if form == 'self':
        # (prom-registry) the rights left after the registrations: the other IDs' (`regKeys`)
        A('  icases (EtcdGrove.prometheus.idToks_names_nil (GF := GF) _ _).1 $$ HR with HRK' if p in REG_KEYS
          else '  iclear HR')
    assert not before, (p, 'steps keyed by no initializer of the package (re-key them to the next item)', before)
    for l in cfg.get('finish', ['iframe Hown', 'is_pkg_init_finish']):
        A('  ' + hdsub(l))
    A('')
    if form == 'lb':
        A('/-- Perennial\'s form, from `wp_initialize\'_lb`. -/')
    else:
        A('/-- Perennial\'s form with the rights to register the closure\'s metric names (decision D16),')
        A('from `wp_initialize\'_res`. -/')
    A(f'theorem wp_initialize\' (get_is_pkg_init : GoString → IProp GF)')
    A(f'    (Hinit : GetIsPkgInitProp {st} get_is_pkg_init) :')
    if form == 'lb':
        A('    {{ ownInitializing get_is_pkg_init }}')
    else:
        A('    {{ ownInitializing get_is_pkg_init ∗ EtcdGrove.prometheus.regsFree (GF := GF) regQs }}')
    A(f'      (App (Val initialize\') (Val #()))')
    A('    {{ RET #(); ownInitializing get_is_pkg_init ∗')
    A(f'        isPkgInit (PROP := IProp GF) {st} }}}} :=')
    if form == 'lb':
        A('  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize\'_lb get_is_pkg_init Hinit)')
    else:
        A('  EtcdGrove.wp_init_of_regResL _ _ _ _ (wp_initialize\'_res get_is_pkg_init Hinit)')
    A('')
    A('')
    A(f'end {p}')
    A('')
    A('end init')
    A('')
    A('end Perennial')
    path = f'Proof/{dirof(p)}/Init.lean'
    if not sp:
        return [(path, '\n'.join(lines) + '\n')]
    # (import tiers, 2026-11-19) split: `Init` (defs tier) keeps the facts and the trust-boundary
    # axioms, `InitLinked` (linking) the `wp_initialize'` proof, which applies other packages'
    # `wp_initialize'` and functions' `wp_proof`s (CLAUDE.md, "Import tiers")
    head = lines[:i_imports]
    prelude = lines[j_imports:]
    k = prelude.index('open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode') + 2
    body_start = i_init - j_imports
    assert head[1:3] == [f'Package initialization of `{p}`', '(item 8, 2026-10-17): its `wp_initialize\'`.'] \
        and head[-3:] == ['-/', 'module', ''], head
    facts = (head[:2] + ['(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize\'` is in',
                         '`InitLinked.lean` (2026-11-19: the proof applies other packages\' `wp_initialize\'` and',
                         'functions\' proofs, so it is a linking module, CLAUDE.md "Import tiers").']
             + head[3:-3] + ['-/', 'module', '']
             + [f'public import {m}' for m in facts_mods]
             + prelude[:body_start] + ['end Perennial'])
    linked = (['/-', f'Package initialization of `{p}`: its `wp_initialize\'` (item 8, 2026-10-17;',
               'split from its facts and trust-boundary axioms, `Init.lean`, 2026-11-19: this proof',
               'applies other packages\' `wp_initialize\'` and functions\' proofs, so it is a linking',
               'module, CLAUDE.md "Import tiers"). Generated by `etc/gen-init.py`.', '-/', 'module', '']
              + [f'public import {m}' for m in linked_mods]
              + prelude[:k] + prelude[body_start:])
    return [(path, '\n'.join(facts) + '\n'),
            (f'Proof/{dirof(p)}/InitLinked.lean', '\n'.join(linked) + '\n')]



def packages():
    seen = set(); st = list(ROOTS)
    while st:
        q = st.pop()
        if q in seen: continue
        seen.add(q); st += inv[q]['imports']
    out = []
    for p in sorted(seen):
        if inv[p]['perennial'] and p not in PERENNIAL_HERE: continue
        if p in RAFT_INIT or p == 'k8s_io.utils.third_party.forked.golang.btree' or p in NOT_YET:
            continue
        out.append(p)
    return out


def code_module(q):
    f = inv[q]['file']
    root = os.path.dirname(os.path.dirname(PERENNIAL_CODE)) + '/'
    if f.startswith(root):
        f = f[len(root):]
    # (a Lean keyword as a component is escaped: `Perennial.Code.«unsafe»`)
    return '.'.join(f'«{c}»' if c == 'unsafe' else c for c in f[:-len('.lean')].split('/'))


EXT_DOC = """/-
The package initializers whose `wp_initialize'` is not generated here, and their `_lb` forms
(decision D19e). Generated by `etc/gen-init.py`; do not edit.

One module for every tree (the main tree and the parts; L1, 2026-11-24): `ExternalInit p init`
registers the initializer `init` of the package `p` as external. This module registers Perennial's
packages, those any tree's generated initializers name; a tree registers the others in a module of
its own, which imports this one (the main tree: raft's, protobuf's `proto` and the B-tree's,
`Proof/runtime/PkgInitExtRaft.lean`; `Dsverify/`: its own translations', `PkgInitDsv.lean`), so that
a part that does not import raft shares this module with the main tree. (Until 2026-11-24
`ExternalInit` was an inductive listing the main tree's packages, and the parts `Net/` and
`Dsverify/` had copies of this module, and of every package initializer that imported it.)

`initLb_of_spec`: if the initializer `init` of the package `p`, a registered one, meets Perennial's
spec (`{{ ownInitializing g }} init #() {{ ownInitializing g ∗ isPkgInit p }}`), then it also keeps
every package initialized before initialized (`ownInitLb g σ0`, for every `σ0`). Perennial's
`initLb_of_initSpec`: `ownInitializing`'s package map is a monotone ghost map (Perennial
`1aab4c42b`), so any proof that keeps `ownInitializing g` keeps its lower bound (`ownInitLb g σ0` is
Perennial's `ownInitializingLb g σ0`). (Until 2026-11-07 a trust-boundary axiom: Perennial's
theorems returned an arbitrary map.) The `ExternalInit` premise is not needed by the proof (any
initializer meeting the spec would do): it documents which initializers the generated proofs take
from elsewhere.
-/"""

EXT_RAFT_DOC = """/-
The main tree's registrations of external package initializers (`ExternalInit`,
`Proof/runtime/PkgInitExt.lean`) whose translations are not Perennial's: raft's, protobuf's `proto`
and the B-tree's (their `wp_initialize'` are hand-written: `Proof/go_etcd_io/raft/v3/Init.lean`,
`Proof/k8s_io/utils/third_party/forked/golang/btree/initialize.lean`). A module of its own so that
`PkgInitExt` imports no translation of this repository: the parts that do not import raft share it,
and the parts with a raft of their own (`RaftWitness/`, `RaftNoAx/`, `RaftTla/`, `KvRaft/`) have a
copy of this module over theirs. Generated by `etc/gen-init.py`; do not edit.
-/"""

EXT_DSV_DOC = """/-
The part `Dsverify/`'s registrations of external package initializers (`ExternalInit`,
`Proof/runtime/PkgInitExt.lean`) whose translations are not Perennial's: the packages whose
`wp_initialize'` is a trust-boundary axiom of the part (`etc/dsv/<kit>.py`'s `HYP_INITS`)
translated by this repository (the part's own translations, or `Net/`'s). Generated by
`etc/gen-init.py` (`dsv_inits`); do not edit. (Until 2026-11-24 this module declared a variant of
`initLb_of_spec` without the `ExternalInit` premise, the part importing `Net/`'s copy of
`PkgInitExt`.)
-/"""


def ext_ns(L):
    return L + ['', '@[expose] public section', '', 'set_option linter.unusedSectionVars false', '',
                'noncomputable section', '', 'namespace Perennial', 'namespace EtcdGrove', '',
                'open Iris Iris.BI Iris.ProgramLogic Iris.Std', '']


def ext_regs(pkgs):
    return [f'theorem ExternalInit.{ext_ctor(q)} [GooseExts] [GoGlobalContext] :\n'
            f'    ExternalInit pkg_id.{q} _root_.Perennial.{q}.initialize\' := ⟨⟩'
            for q in sorted(pkgs)]


def gen_ext():
    """The shared `PkgInitExt` (`ExternalInit`, Perennial's packages' registrations and
    `initLb_of_spec`), and the main tree's `PkgInitExtRaft`."""
    exts = EXT_SHARED
    mods = sorted(set(exts.values()))
    L = [EXT_DOC, 'module', '', 'public import Proof.runtime.PkgInit']
    L += [f'public import {m}' for m in mods]
    L = ext_ns(L)
    L += ['/-- The registered initializers of the packages whose `wp_initialize\'` is not',
          'generated here (see the file header). -/',
          'structure ExternalInit [GooseExts] [GoGlobalContext] (p : GoString) (init : val) : Prop', '']
    L += ['\n'.join(ext_regs(exts)), '']
    L += ['section ax',
          'variable [GooseExts] [GooseSemantics] [GooseInterp]',
          'variable [go_gctx : GoGlobalContext]',
          'variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]',
          'variable [sem : go.Semantics]',
          '',
          '/-- A registered initializer keeps the initialized packages (see the file header). -/',
          'theorem initLb_of_spec (p : GoString) (init : val) (_hext : ExternalInit p init)',
          '    [IsPkgInit (IProp GF) p] [GetIsPkgInitWf (IProp GF) p]',
          '    (Hstd : ∀ (get_is_pkg_init : GoString → IProp GF),',
          '      GetIsPkgInitProp p get_is_pkg_init →',
          '      {{ ownInitializing get_is_pkg_init }} (App (Val init) (Val #()))',
          '      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) p }}) :',
          '    ∀ (get_is_pkg_init : GoString → IProp GF), GetIsPkgInitProp p get_is_pkg_init →',
          '    ∀ σ0, {{ ownInitLb get_is_pkg_init σ0 }} (App (Val init) (Val #()))',
          '      {{ RET #(); ownInitLb get_is_pkg_init σ0 ∗ isPkgInit (PROP := IProp GF) p }} :=',
          '  fun g hg σ0 => initLb_of_initSpec init g _ (Hstd g hg) σ0',
          '',
          'end ax',
          '',
          'end EtcdGrove',
          'end Perennial']
    return [('Proof/runtime/PkgInitExt.lean', '\n'.join(L) + '\n'),
            ext_local('Proof/runtime/PkgInitExtRaft.lean', EXT_RAFT_DOC, EXT_MAIN)]


def ext_local(path, doc, exts):
    """A tree's registrations module (`path`) of the external initializers `exts` (package -> its
    translation's module)."""
    L = [doc, 'module', '', 'public import Proof.runtime.PkgInitExt']
    L += [f'public import {m}' for m in sorted(set(exts.values()))]
    L = ext_ns(L)
    L += ['\n'.join(ext_regs(exts)), '', 'end EtcdGrove', 'end Perennial']
    return path, '\n'.join(L) + '\n'


# The programs whose closed theorem needs the package table of their import closure (item 9,
# D19r, 2026-10-18): the root package and the module of the generated table.
# (net-swap, 2026-11-22) etcd/all's, k8s/all's and leaseexpiryN's tables went with their closed theorems;
# (2026-11-23, etcd-grove#28) restored with them, as `*_single_process` (`notes/single-process-restore.md`)
PROGRAMS = {'github_com.mit_pdos.etcd_grove.examples.etcd.all':
            'Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/PkgTable.lean',
            'github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter':
            'Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/counter/PkgTable.lean',
            'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkv':
            'Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkv/PkgTable.lean',
            'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvcompact':
            'Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvcompact/PkgTable.lean',
            'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvsnap':
            'Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvsnap/PkgTable.lean',
            'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw':
            'Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvrw/PkgTable.lean',
            'github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvappend':
            'Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvappend/PkgTable.lean',
            # (2026-11-23, etcd-grove#28) k8s_safe_single_process's and etcd_leaseexpiryN_safe_single_process's
            # tables, restored
            'github_com.mit_pdos.etcd_grove.examples.k8s.all':
            'Proof/github_com/mit_pdos/etcd_grove/examples/k8s/all/PkgTable.lean',
            'github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN':
            'Proof/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/PkgTable.lean'}
# (R10, 2026-11-07) mvcc's randomized tester
PROGRAMS['github_com.mit_pdos.etcd_grove.examples.mvccrand'] = \
    'Proof/github_com/mit_pdos/etcd_grove/examples/mvccrand/PkgTable.lean'
# (F1 Prove, 2026-11-10) mvcc's full tester, for its closed theorem (`mvccfull_adequate`)
PROGRAMS['github_com.mit_pdos.etcd_grove.examples.mvccfull'] = \
    'Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull/PkgTable.lean'
# (2026-11-23) putget_safe's package (both machines' boot programs run its initializer), for its
# distributed theorem (notes/putget-dist-plan.md)
PROGRAMS['github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget'] = \
    'Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putget/PkgTable.lean'
# (2026-11-19) Kubernetes' conditional authorization's driver, for its closed theorem
PROGRAMS['github_com.mit_pdos.etcd_grove.examples.k8s.authz'] = \
    'Proof/github_com/mit_pdos/etcd_grove/examples/k8s/authz/PkgTable.lean'

# (fmt1-errno, 2026-11-24) the osfs examples' boot programs, for their closed (crash) theorems
for _ex in ['crashlog', 'walfs', 'bboltfs']:
    PROGRAMS[f'github_com.mit_pdos.etcd_grove.examples.osfs.{_ex}'] = \
        f'Proof/github_com/mit_pdos/etcd_grove/examples/osfs/{_ex}/PkgTable.lean'

TABLE_DOC = """/-
The package table of the program of `{p}`
(item 9, D19r, 2026-10-18): `getIsPkgInit`, each package of its import closure mapped to its
`isPkgInit`, what `ownInitializing` hands out for an initialized package, and `getIsPkgInit_wf`,
the program's `GetIsPkgInitProp`, proved package by package in import order (each package's proof
uses its imports', so the import DAG is not unfolded as a tree). Generated by `etc/gen-init.py`;
do not edit.
-/"""


def table_vars(cl):
    """The section variables of a package table whose closure is `cl` (`SPECIAL`'s `table_vars`: a
    package fact's own parameters, as the compactor registry's name)."""
    vs = []
    for q in sorted(cl):
        for v in SPECIAL.get(q, {}).get('table_vars', []):
            if v not in vs:
                vs.append(v)
    return vs


def gen_table(p, path):
    cl = closure(p)
    order, seen = [], set()

    def visit(q):
        if q in seen:
            return
        seen.add(q)
        for d in pkginfo_imports(q):
            visit(d)
        order.append(q)
    visit(p)
    assert seen == cl, (p, seen ^ cl)
    L = [TABLE_DOC.replace('{p}', plain(p)), 'module', '',
         f'public import Proof.{plain(p)}.Init', '',
         '@[expose] public section', '', 'set_option linter.unusedSectionVars false',
         'set_option maxRecDepth 100000', '',
         'noncomputable section', '', 'namespace Perennial', f'namespace {p}', '',
         'open Iris Iris.BI Iris.ProgramLogic Iris.Std', '',
         'section table',
         'variable [GooseExts] [GooseSemantics] [GooseInterp]',
         'variable [go_gctx : GoGlobalContext]',
         'variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]',
         'variable [sem : go.Semantics]',
         f'variable [package_sem : _root_.Perennial.{p}.Assumptions]'] + \
        [f'variable {v}' for v in table_vars(cl)] + ['',
         '/-- Every package of the program\'s import closure, with its `isPkgInit`. -/',
         'def pkgInitTable : List (GoString × IProp GF) :=']
    rows = [f'(pkg_id.{q}, isPkgInit (PROP := IProp GF) pkg_id.{q})' for q in sorted(order)]
    L.append('  [' + ',\n   '.join(rows) + ']')
    L += ['',
          '/-- `get_is_pkg_init` for the program: a package\'s entry in `pkgInitTable`. -/',
          'def getIsPkgInit (s : GoString) : IProp GF :=',
          '  ((pkgInitTable (GF := GF)).lookup s).getD iprop(True)', '',
          f'theorem getIsPkgInit_wf : GetIsPkgInitProp pkg_id.{p} (getIsPkgInit (GF := GF)) := by']
    names = {q: f'h{i}' for i, q in enumerate(order)}
    for q in order:
        deps = pkginfo_imports(q)
        L.append(f'  have {names[q]} : GetIsPkgInitProp pkg_id.{q} (getIsPkgInit (GF := GF)) := by')
        L.append('    refine And.intro ?_ ?_')
        L.append('    · rfl')
        L.append('    exact ' + ('⟨' + ', '.join([names[d] for d in deps] + ['True.intro']) + '⟩'
                                   if deps else 'True.intro'))
    L.append(f'  exact {names[p]}')
    L += ['', 'end table', '', f'end {p}', 'end Perennial']
    return path, '\n'.join(L) + '\n'


# The parallel tree `RaftWitness/` (raft's witness experiment, notes/raft-witness.md) imports the
# initializers of these packages, which reached raft through `PkgInitExt` until 2026-11-24 (raft's
# `initialize'` is an `ExternalInit`, registered since in `PkgInitExtRaft`, of which the part has a
# copy; the copies of these packages' `Init.lean` remain, until a cleanup); no module may import
# both raft trees (the same declarations), so the part
# has its own copies: the same files, at `RaftWitness/<path>`, whose imports of these modules and
# of raft's translation are the part's.
PART_ROOT = 'RaftWitness'
PART_INITS = ['github_com.anishathalye.porcupine', 'github_com.mit_pdos.etcd_grove.examples.lib.lintest',
              'google_golang_org.protobuf.internal.impl', 'google_golang_org.protobuf.internal.pragma',
              'google_golang_org.protobuf.reflect.protoreflect',
              'google_golang_org.protobuf.runtime.protoimpl',
              # (2026-11-03) `os`'s, now generated (raft's `Init.lean` imports it), and its imports'
              'os', 'syscall', 'io.fs',
              # (2026-11-07) `os`'s translated initializers' imports
              'internal.poll', 'internal.syscall.unix',
              # (2026-11-25, Go model overlays at Perennial e9a45a420) `os`'s new import, whose
              # `Init.lean` imports `PkgInitExt`: filepathlite (`os` no longer imports `runtime`:
              # Code/os.toml, rawConn)
              'internal.filepathlite']


def part_paths(inits):
    return ({f'Proof/{dirof(p)}/Init.lean' for p in inits}
            | {f'Proof/{dirof(p)}/InitLinked.lean' for p in inits if split(p)}
            | {'Proof/runtime/PkgInitExtRaft.lean'})


# Every such part: its packages, and the module prefixes (besides its copies of these files) whose
# imports are the part's. The part `RaftNoAx/` (raft without hand-written axioms,
# notes/raft-noax-part.md): its other copies (etc/copy-part.py) are raft's proofs, and the
# translations raft's and walpb's (etc/goose.py). (Until 2026-11-24 also kvdurable's, kvreconf's and
# their initializers, durable's and trusted_proph's: retired.)
PARTS = {
    PART_ROOT: (PART_INITS, ['Code.go_etcd_io.raft']),
    'RaftNoAx': (PART_INITS,
                 ['Code.go_etcd_io.raft', 'GeneratedProof.go_etcd_io.raft', 'Spec.go_etcd_io.raft',
                  'Proof.go_etcd_io.raft', 'Code.go_etcd_io.etcd.server.v3.storage.wal.walpb']),
}
PART_PATHS = part_paths(PART_INITS)


def part_copy(path, txt, root=PART_ROOT):
    """The part `root`'s copy of the generated file `path`."""
    inits, prefixes = PARTS[root]
    mods = {p[:-len('.lean')].replace('/', '.') for p in part_paths(inits)}
    def imp(m):
        x = m.group(2)
        if x in mods or any(x == q or x.startswith(q + '.') for q in prefixes):
            x = root + '.' + x
        return m.group(1) + x
    txt = re.sub(r'(?m)^(public import )(\S+)', imp, txt)
    i = txt.index('\nmodule\n') + 1
    note = (f'-- The copy for the parallel tree `{root}/` of `{path}` (`PART_INITS` in\n'
            f'-- `etc/gen-init.py`): the same, but its imports of the copied modules and of raft are the part\'s.\n')
    return f'{root}/{path}', txt[:i] + note + txt[i:]

# The part `PorcupineDag/` (porcupine's pull request #46, the DAG search; notes/porcupine-dag-plan.md):
# the same Go path as v1.3.1's porcupine, translated into a module root of its own. Its package's
# initializer is generated as the main tree's, from the part's translation (`DAG_ROOT/Code`) and
# the part's instance (`DAG_ROOT/Proof`), with the imports of the part's modules prefixed; and the
# closures its fact names (func literals of its variables' initializers, which capture nothing),
# extracted from the translation into `Closures.lean`.
DAG_ROOT = 'PorcupineDag'
DAG_PKG = 'github_com.anishathalye.porcupine'
# name -> (variable, the `Let` binding of a composite literal's field, or None for the whole
# initializer), and the doc
DAG_CLOSURES = [
    ('rtV', 'RealTime', None, '`RealTime`: the real-time oracle.'),
    ('glV', 'GeneralLikely', None, '`GeneralLikely`: the call-order oracle.'),
    ('rvInitV', 'RVal', '$v0', '`RVal.Init`: the model\'s `Init`.'),
    ('rvStepV', 'RVal', '$v1', '`RVal.Step`: the model\'s `StepContext`.'),
]
DAG_SPECIAL = dict(
    doc="""Its fact (`linInit`, `Base.lean`): `Linearizability` holds the consistency value whose
oracles slice holds `RealTime` and `GeneralLikely` and whose validity is `RVal` (the closures of
`Closures.lean`). Its initializer runs its variables' translated initializers (func literals,
slice and struct literals).""",
    imports=[],
    alloc_types={'GeneralLikely': 'GoFunc', 'RealTime': 'GoFunc',
                 'LinearizabilityOracles': 'GoSlice', 'RealTimeWrites': 'GoFunc',
                 'OrderedSequentialConsistencyOracles': 'GoSlice', 'RVal': 'Validity',
                 'Linearizability': 'Consistency', 'OrderedSequentialConsistency': 'Consistency'},
    finish=[
        # `LinearizabilityOracles`, then `OrderedSequentialConsistencyOracles`: slice literals of
        # the globals' closures
        'wp_apply wp_slice_literal (l := [rtV, glV])', 'isplitr', '· ipureintro; rfl',
        'iintro %s1 ⟨S1, -⟩', 'try wp_auto',
        'wp_apply wp_slice_literal (l := [_, _])', 'isplitr', '· ipureintro; rfl',
        'iintro %s2 ⟨S2, -⟩', 'try wp_auto',
        # `RVal`: a struct literal of two func literals, folded to their names
        'rw [← rvInitV_val, ← rvStepV_val]', 'try wp_auto',
        'ipersist HLinearizability', 'ipersist S1', 'iframe Hown', 'imodintro', 'isplitr',
        '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish', 'imodintro',
        'unfold linInit', 'iexists _', 'iframe HLinearizability', 'unfold isLinearizability',
        'iframe S1', 'ipureintro', 'rfl'],
)


# The trace checker (`examples/raft/tracecheck/etcdraft`, 2026-11-09, layer C): its fact
# (`etcdraftInit`, `Base.lean`) is that `Invariants` holds the seven named closures of
# `Closures.lean` (each calls its `State` method), read-only; `State.Violated`'s proof reads it.
TC_PKG = 'github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft'
TC_CLOSURES = [(f'{n[0].lower()}{n[1:]}V', 'Invariants', f'$v{2 * k + 1}', f'`{n}`\'s closure: `s.{n}()`.')
               for k, n in enumerate(['LogInv', 'MoreThanOneLeaderInv', 'ElectionSafetyInv', 'LogMatchingInv',
                                      'QuorumLogInv', 'LeaderCompletenessInv', 'CommittedIsDurableInv'])]
SPECIAL[TC_PKG] = dict(
    doc="""Its fact (`etcdraftInit`, `Base.lean`): `Invariants` holds the seven named invariants of
`Traceetcdraft.cfg`, in order, each with its closure of `Closures.lean` (read-only), and the three
tables their literals (read-only maps). Its initializer
runs its variables' translated initializers (`Invariants`' slice literal of func literals, the
tables' map literals, `EmptyBag`'s struct literal).""",
    alloc_types={'Invariants': 'GoSlice', 'RaftMsgType': 'Loc', 'RaftMsgSubtype': 'Loc',
                 'ReceiveMessageTraceNames': 'Loc', 'EmptyBag': 'Bag'},
    before={
        # a slice literal of struct literals whose closures fold to `Closures.lean`'s
        'Invariants': ['try wp_auto',
                       'rw [' + ', '.join(f'← {c[0]}_val' for c in TC_CLOSURES) + ']',
                       'try wp_auto', 'wp_apply wp_slice_literal (l := invariantsV)', 'isplitr',
                       '· ipureintro; rfl', 'iintro %sl ⟨Hsl, -⟩', 'try wp_auto'],
        # the tables: map literals
        'RaftMsgType': [
            'wp_apply (wp_map_make1 (K := GoString) (V := MsgType) go.string MsgType.ty) as %m1 Hm1',
            'try wp_auto',
            'repeat (wp_apply (wp_mapInsert (K := GoString) (V := MsgType) go.string) $$ Hm1 as Hm1; try wp_auto)'],
        'RaftMsgSubtype': [
            'wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %m2 Hm2',
            'try wp_auto',
            'repeat (wp_apply (wp_mapInsert (K := GoString) (V := GoString) go.string) $$ Hm2 as Hm2; try wp_auto)'],
        'ReceiveMessageTraceNames': [
            'wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %m3 Hm3',
            'try wp_auto',
            'repeat (wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hm3 as Hm3; try wp_auto)'],
        'EmptyBag': ['try wp_auto']},
    finish=['ipersist HInvariants', 'ipersist Hsl', 'ipersist HRaftMsgType', 'ipersist HRaftMsgSubtype',
            'ipersist HReceiveMessageTraceNames',
            'imod ownMap_persist _ _ _ $$ Hm1 with #Hm1', 'imod ownMap_persist _ _ _ $$ Hm2 with #Hm2',
            'imod ownMap_persist _ _ _ $$ Hm3 with #Hm3',
            'iframe Hown', 'imodintro', 'isplitr', '· ipureintro',
            '  exact isPanic_intoVal _', 'is_pkg_init_finish', 'imodintro', 'unfold etcdraftInit',
            'isplitr', '· iexists _; iframe HInvariants; iexact Hsl',
            'isplitr', '· iexists m1; iframe HRaftMsgType; iExactEq Hm1; rfl',
            'isplitr', '· iexists m2; iframe HRaftMsgSubtype; iExactEq Hm2; rfl',
            'iexists m3; iframe HReceiveMessageTraceNames; iExactEq Hm3; rfl'],
)

def sexp_end(s, i):
    """The index after the parenthesized term starting at `s[i] == '('` (strings skipped)."""
    assert s[i] == '(', s[i:i + 20]
    depth = 0
    j = i
    while j < len(s):
        ch = s[j]
        if ch == '"':
            j += 1
            while s[j] != '"':
                j += 2 if s[j] == '\\' else 1
        elif ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    raise ValueError('unbalanced')


def dag_initializer(body, var):
    """The initializer term of `var` in `initialize'`'s body: the `Let "$r0"` bound around its
    store."""
    store = body.index(f'(GlobalVarAddr {var}))) (Val #())) (Var "$r0")')
    best = None
    for m in re.finditer(r'\(Let "\$r0" ', body):
        if m.start() < store and sexp_end(body, m.start()) > store:
            best = m.start()
    k = best + len('(Let "$r0" ')
    return body[k:sexp_end(body, k)]


def gen_closures(root, pkg, closures, fact, cfg_name):
    """`Closures.lean`: the func literals `pkg`'s package fact names, from the translation (of the
    part `root`, or of the main tree when `root` is empty)."""
    pre = root + '/' if root else ''
    mpre = root + '.' if root else ''
    t = open(f'{pre}Code/{dirof(pkg)}.lean').read()
    i = t.find("noncomputable def initialize'")
    body = t[i:t.find("\n\n", i)]
    L = ['/-',
         f'The closures `{pkg}`\'s package fact names (`{fact}`, `Base.lean`): the func literals',
         'of its variables\' initializers, as the translation\'s `initialize\'` has them (they capture',
         f'nothing). Generated by `etc/gen-init.py` (`{cfg_name}`) from',
         f'`{pre}Code/{dirof(pkg)}.lean`; do not edit.',
         '-/', 'module', '', f'public import {mpre}Code.{pkg}', '',
         '@[expose] public section', '', 'set_option maxRecDepth 100000', '',
         'open Iris', '',
         'namespace Perennial', 'noncomputable section', '', f'namespace {pkg}', '']
    for name, var, field, doc in closures:
        init = dag_initializer(body, var)
        if field is not None:
            k = init.index(f'(Let "{field}" ') + len(f'(Let "{field}" ')
            init = init[k:sexp_end(init, k)]
        m = re.match(r'\(Lam "([^"]*)"\n', init)
        assert m and init.endswith(')'), (name, init[:60])
        arg = m.group(1)
        inner = init[m.end():-1]
        L.append(f'/-- {doc} -/')
        L.append(f'noncomputable def {name} [GooseExts] [GoGlobalContext] : GoFunc :=')
        L.append(f'  func.mk BAnon "{arg}"')
        L.append('  ' + inner.replace('\n', '\n  '))
        L.append('')
        L.append(f'/-- `{name}` as the value its func literal evaluates to (to fold it in a goal). -/')
        L.append(f'theorem {name}_val [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]\n    [go.Semantics] :')
        L.append(f'    (#{name} : val) = RecV BAnon "{arg}"')
        L.append('  ' + inner.replace('\n', '\n  ') + ' := by')
        L.append('  rw [go.intoVal_unfold GoFunc]; rfl')
        L.append('')
    L += [f'end {pkg}', '', 'end', 'end Perennial']
    return f'{pre}Proof/{dirof(pkg)}/Closures.lean', '\n'.join(L) + '\n'


def dag_closures():
    """`Closures.lean` of the part `PorcupineDag/`."""
    return gen_closures(DAG_ROOT, DAG_PKG, DAG_CLOSURES, 'linInit', 'DAG_CLOSURES')


def dag_init():
    """The part's `Init.lean` (and `InitLinked.lean`, if split), generated as the main tree's from
    the part's files."""
    global inv, inst, CFG_OVERRIDE
    saved = inv, inst, CFG_OVERRIDE
    try:
        inv = inventory(f'{DAG_ROOT}/Code')
        inst = instances(f'{DAG_ROOT}/Proof/')
        CFG_OVERRIDE = {DAG_PKG: DAG_SPECIAL}
        raw = gen(DAG_PKG, DAG_SPECIAL)
    finally:
        inv, inst, CFG_OVERRIDE = saved
    return [(f'{DAG_ROOT}/{path}',
             re.sub(r'(?m)^(public import )(Proof\.' + re.escape(plain(DAG_PKG)) + r'\.)', r'\1' + DAG_ROOT + r'.\2', txt))
            for path, txt in raw]



# The part `RaftTla/` (raft's `with_tla` build, etc/gen-raft-tla.py): the closed trace-check program
# (`examples/raft/tracecheck`) runs that build, so its `Init.lean` and `PkgTable.lean` are generated
# from the part's translations over the main tree's (the part translates raft's own package and the
# program; everything else is the main tree's), with the imports redirected as etc/gen-raft-tla.py
# redirects those of the modules it copies.
TLA_ROOT = 'RaftTla'
TLA_PROGRAM = 'github_com.mit_pdos.etcd_grove.examples.raft.tracecheck'


def tla_outs():
    """The part's generated `Init.lean` and `PkgTable.lean` of the trace-check program."""
    global inv, inst
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'gen_raft_tla', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen-raft-tla.py'))
    grt = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(grt)
    redirect = grt.plan()[4]
    global EXT_RECORD
    saved = inv, inst, EXT_RECORD
    try:
        EXT_RECORD = {}  # (the part's `PkgInitExtRaft` is etc/gen-raft-tla.py's copy of the main tree's)
        inv = dict(inv)
        inv.update({q: d for q, d in inventory(f'{TLA_ROOT}/Code').items() if not d['perennial']})
        inst = dict(inst)
        inst.update(instances(f'{TLA_ROOT}/Proof/'))
        outs = gen(TLA_PROGRAM, SPECIAL.get(TLA_PROGRAM)) + [
                gen_table(TLA_PROGRAM, f'Proof/{dirof(TLA_PROGRAM)}/PkgTable.lean')]
    finally:
        inv, inst, EXT_RECORD = saved
    def imp(m):
        return m.group(1) + redirect(m.group(2))
    return [(f'{TLA_ROOT}/{path}', re.sub(r'(?m)^(public import )(\S+)', imp, txt)) for path, txt in outs]


# The part `WalTester/` (notes/wal-lean-integration.md): the WAL tester and `examples/lib/durable` with
# its bodies, whose Go path the main tree's trusted `durable` has too. Their initializers are generated
# as the main tree's, from the part's translation (`WT_ROOT/Code`, over the main tree's for the rest)
# and instances (`WT_ROOT/Proof`, over the main tree's), with the imports of the part's modules
# prefixed. The Perennial packages only they import join the main `PkgInitExt` (`gen_ext`).
WT_ROOT = 'WalTester'
WT_PKGS = ['github_com.mit_pdos.etcd_grove.examples.lib.durable',
           'github_com.mit_pdos.etcd_grove.examples.etcd.wal']
WT_PROGRAM = 'github_com.mit_pdos.etcd_grove.examples.etcd.wal'


def wt_inventory():
    """The part's translation over the main tree's (the part's inventory lists Perennial's packages too,
    which the main tree may translate itself: `os`)."""
    out = dict(inv)
    for q, d in inventory(f'{WT_ROOT}/Code').items():
        if not d['perennial']:
            out[q] = d
    return out


def wt_inits():
    """The part's `Init.lean` files."""
    global inv, inst, CFG_OVERRIDE
    saved = inv, inst, CFG_OVERRIDE
    raw = []
    try:
        inv = wt_inventory()
        inst = {**inst, **{k: [(f'{WT_ROOT}/Proof/' + f, fact) for f, fact in v]
                           for k, v in instances(f'{WT_ROOT}/Proof/').items()}}
        CFG_OVERRIDE = WT_SPECIAL
        for p in WT_PKGS:
            raw += gen(p, WT_SPECIAL.get(p, SPECIAL.get(p)))
        # (2026-11-24, wal-open) the tester's package table, for its crash-safety theorem's initializer
        raw.append(gen_table(WT_PROGRAM, f'Proof/{dirof(WT_PROGRAM)}/PkgTable.lean'))
    finally:
        inv, inst, CFG_OVERRIDE = saved
    part_mods = {path[:-len('.lean')].replace('/', '.') for path, _ in raw}

    def imp(m):
        x = m.group(2)
        if x.startswith(f'Proof.{WT_ROOT}.'):
            x = x[len('Proof.'):]
        elif os.path.exists(f'{WT_ROOT}/{x.replace(".", "/")}.lean') or x in part_mods:
            x = f'{WT_ROOT}.{x}'
        return m.group(1) + x
    return [(f'{WT_ROOT}/{path}', re.sub(r'(?m)^(public import )(\S+)', imp, txt)) for path, txt in raw]


sys.path.insert(0, os.path.join(ROOT, 'etc'))
import goose as _goose  # noqa: E402


# The part `Net/` (the net extension's `net` and the programs over it, `examples/net/`; project
# net): `net` is a Go path the main tree translates too (names only), so the part's packages'
# initializers are generated as `LinuxFs/`'s, from the part's translation and instances, with the
# imports of the part's modules prefixed, and a `PkgInitExt` without raft.
NET_ROOT = 'Net'
NET_PKGS = ['net', 'github_com.mit_pdos.etcd_grove.examples.net.wire'] + \
    [f'github_com.mit_pdos.etcd_grove.examples.net.{p}' for p in
     ['echo', 'framed', 'acceptloop', 'duplex', 'halfclose', 'shutdown', 'preface']]
# The library models' Go code (`models/`, project models, phase 5 of
# notes/dsverify-net-port-plan.md).
NET_PKGS += ['models_lab.pbcodec', 'models_lab.jsoncodec']
# (2026-11-22, notes/remote-port-plan.md) clients on machines of their own (`examples/lib/remote`).
NET_PKGS += ['github_com.mit_pdos.etcd_grove.examples.lib.remote']
# (2026-11-22) its counter instance (R4) and the instance's four commands, programs of the part.
REMOTE_NODES = ['orch', 'client0', 'client1', 'server']
NET_PKGS += ['github_com.mit_pdos.etcd_grove.examples.lib.remote.counter'] + \
    [f'github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.{n}' for n in REMOTE_NODES]
# Each example's nodes, a command each (`examples/net/<ex>/cmd/<node>`): the programs.
NET_NODES = {'echo': ['server', 'client', 'junk'], 'framed': ['server', 'client', 'junk'],
            'acceptloop': ['server', 'client'], 'duplex': ['server', 'client'],
            'halfclose': ['server', 'client'], 'preface': ['server', 'client', 'junk'],
            'shutdown': ['node'], 'rpcdriver': ['server', 'client']}
# (2026-11-24) net/rpc's driver (notes/library-drivers.md): its package and its service's
NET_PKGS += ['github_com.mit_pdos.etcd_grove.examples.net.rpcdriver',
             'github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service']
# its fact is `True` (`Base.lean`): its variables (`reached`, a function value, and `failMsgs`, a
# slice literal) are allocated and stored
NET_SPECIAL['github_com.mit_pdos.etcd_grove.examples.net.rpcdriver'] = dict(
    doc='''Its fact is `True`. Its initializer allocates its variables, initializes its imports (net/rpc's
and net/http's by their interim axioms, `Net/Proof/net/{rpc,http}/Init.lean`) and stores
`reached`'s function value and `failMsgs`'s slice literal.''',
    alloc_types=_ALLOC_ANY,
    before={'reached': ['try wp_auto'],
            'failMsgs': ['try wp_auto',
                         'wp_apply (wp_slice_literal (l := [go!"driver: no such key", go!"driver: not leader", go!"driver: x"]));'
                         ' isplitr; (· ipureintro; rfl); iintro %sf -',
                         'try wp_auto']})
# (rpc-driver, 2026-11-24) The part's packages whose `wp_initialize'` is an interim trust-boundary
# axiom (`Net/Proof/<pkg>/Init.lean`, hand-written; its fact in `PkgInit.lean`): net/rpc's and
# net/http's models, whose closures reach initializers not translated (retired by L2 step 6,
# notes/library-drivers.md). The generated initializers importing them take them as external
# (`ExternalInit`, registered in the part's `Proof/runtime/PkgInitNet.lean`), their imports those
# of the translation (the programs' tables hold their closures: the main tree's `bufio`, `net/url`,
# `path`, `crypto/tls`, ..., with the main tree's facts). `Dsverify/` keeps them as hypotheses
# (`InitHyp`) over the same facts.
NET_AXIOM_INITS = ['net.rpc', 'net.http']
NET_EXT_MOD = 'Proof.runtime.PkgInitNet'
EXT_NET_DOC = """/-
The part `Net/`'s registrations of external package initializers (`ExternalInit`,
`Proof/runtime/PkgInitExt.lean`) whose translations are not Perennial's: net/rpc's and net/http's
models, whose `wp_initialize'` is an interim trust-boundary axiom (`Net/Proof/net/{rpc,http}/Init.lean`;
`NET_AXIOM_INITS`). Generated by `etc/gen-init.py` (`net_inits`); do not edit.
-/"""
NET_PKGS += [f'github_com.mit_pdos.etcd_grove.examples.net.{ex}.cmd.{n}'
            for ex, ns in NET_NODES.items() for n in ns]
# The part's programs whose adequacy theorem needs the package table of their import closure (as
# `PROGRAMS`): the root package and the table's file under `NET_ROOT`.
NET_PROGRAMS = {f'github_com.mit_pdos.etcd_grove.examples.net.{ex}.cmd.{n}':
               f'Proof/github_com/mit_pdos/etcd_grove/examples/net/{ex}/cmd/{n}/PkgTable.lean'
               for ex, ns in NET_NODES.items() for n in ns}
NET_PROGRAMS.update({f'github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.{n}':
                     f'Proof/github_com/mit_pdos/etcd_grove/examples/lib/remote/counter/cmd/{n}/PkgTable.lean'
                     for n in REMOTE_NODES})


# The main tree's packages the part's `net` imports (`os`, and the packages `os` imports): their
# translations and `IsPkgInit` instances are the main tree's, their `Init.lean` copies in the part.
NET_MAIN = ['os', 'syscall', 'internal.poll', 'io.fs', 'internal.syscall.unix',
            'internal.filepathlite']
# ((Go model overlays S5) the models' internal/gomodel, which syscall's and os's import, is Perennial's:
# no `Init.lean` of its own, here or in the part.)
# (2026-11-22) and the main tree's packages `examples/lib/remote` imports: lintest's driver and
# porcupine (their `Init.lean` import the main tree's `PkgInitExt`, which the part's replaces).
NET_MAIN += ['github_com.anishathalye.porcupine', 'github_com.mit_pdos.etcd_grove.examples.lib.lintest',
             'github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient',
             'github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter']


IMPORT_RE = r'(?m)^(public import )(\S+)'


def shared_inits(raw, main_txt, resolve):
    """(L1, 2026-11-24) The part's generated files (`raw`: path under the part -> text, its imports
    not yet redirected) that are the main tree's: with its imports redirected (`resolve(txt,
    shared)`, given the files already found shared, whose modules are then the main tree's), the
    file is the text the main tree generates at the same path (`main_txt`). The part imports the
    main tree's file instead of generating a copy: one `Init.lean` per Go package."""
    shared, changed = set(), True
    while changed:
        changed = False
        for path, txt in raw:
            if path not in shared and main_txt.get(path.split('/', 1)[1]) == resolve(txt, shared):
                shared.add(path)
                changed = True
    return shared


NET_GEN, NET_SHARED = set(), set()  # `Net/`'s generated paths (under the part), and which are shared


def net_has(f, shared=frozenset()):
    """Whether the module of the file `f` (a path in the main tree's layout) is `Net/`'s: a file of
    the part this script does not write, or one it writes that is not the main tree's."""
    g = f'{NET_ROOT}/{f}'
    if g in NET_GEN:
        return g not in shared and g not in NET_SHARED
    return os.path.exists(g)


def net_prefix(txt, shared=frozenset()):
    """`txt` with its imports of the part's modules (`net_has`) prefixed."""
    def imp(m):
        x = m.group(2)
        if net_has(x.replace('.', '/') + '.lean', shared):
            x = f'{NET_ROOT}.{x}'
        return m.group(1) + x
    return re.sub(IMPORT_RE, imp, txt)


def net_inits(main_txt):
    """The part's `Init.lean` files (those that are not the main tree's, `main_txt`: path -> text)
    and its programs' `PkgTable.lean`; and the paths of the shared ones (stale if on disk)."""
    global inv, inst, CFG_OVERRIDE, EXT_RECORD, EXT_LOCAL_MOD
    saved = inv, inst, CFG_OVERRIDE
    saved_ext = EXT_RECORD, EXT_LOCAL_MOD
    ext_net = {}
    try:
        CFG_OVERRIDE = NET_SPECIAL
        EXT_RECORD, EXT_LOCAL_MOD = ext_net, NET_EXT_MOD
        inv = inventory(f'{NET_ROOT}/Code')
        inst = instances(f'{NET_ROOT}/Proof/')
        # (v3, 2026-11-14) the main tree's `os` and the packages it imports, which `net` imports
        # (`etc/goose.py`'s net lean roots): their translations and instances are the main tree's
        for p in NET_MAIN:
            inv[p] = saved[0][p]
            if p in saved[1]:  # (runtime's instance is Perennial's)
                inst[p] = saved[1][p]
        # (rpc-driver) the axiom packages' closures: the main tree's packages the part lacks
        st = [q for p in NET_AXIOM_INITS for q in inv[p]['imports']]
        while st:
            q = st.pop()
            if q in inv or q not in saved[0]:
                continue
            inv[q] = saved[0][q]
            if q in saved[1]:
                inst[q] = saved[1][q]
            st += inv[q]['imports']
        # and the axiom packages themselves: external here
        for p in NET_AXIOM_INITS:
            inv[p] = dict(inv[p], perennial=True)
        # their `Init.lean` (the main tree's, `shared_inits`, since L1: until then copies, over a
        # copy of `PkgInitExt` without raft)
        raw = [(f'{NET_ROOT}/{path}', txt) for p in NET_MAIN for path, txt in gen(p, SPECIAL.get(p))]
        raw += [(f'{NET_ROOT}/{path}', txt) for p in NET_PKGS
                if os.path.exists(f'{NET_ROOT}/Code/{dirof(p)}.lean')
                for path, txt in gen(p, NET_SPECIAL.get(p, SPECIAL.get(p)))]
        tables = [(f'{NET_ROOT}/{path}', txt) for path, txt in
                  (gen_table(p, path) for p, path in NET_PROGRAMS.items())]
    finally:
        inv, inst, CFG_OVERRIDE = saved
        EXT_RECORD, EXT_LOCAL_MOD = saved_ext

    def axiom_fix(txt):
        # an axiom package's `wp_initialize'` is the part's hand-written `Init.lean`'s
        for p in NET_AXIOM_INITS:
            txt = txt.replace(f'public import Perennial.Proof.{p}.Link\n', f'public import Proof.{p}.Init\n')
        return txt
    raw = [(path, axiom_fix(txt)) for path, txt in raw]
    ext_path = f'{NET_ROOT}/{NET_EXT_MOD.replace(".", "/")}.lean'
    NET_GEN.update(path for path, _ in raw + tables)
    NET_GEN.add(ext_path)
    NET_SHARED.update(shared_inits(raw, main_txt, net_prefix))
    outs = [(path, net_prefix(txt)) for path, txt in raw + tables if path not in NET_SHARED]
    outs.append(ext_local(ext_path, EXT_NET_DOC, ext_net))
    return outs, sorted(NET_SHARED)


# The part `KvRaft/` (kvraft's proof, notes/kvraft-part.md): raft-noax's raft, the net extension's `net`
# (`Net/`'s) and the bodied `durable` over fsExt (`WalTester/`'s), in one closure. Each of its source
# parts has its own `PkgInitExt` and its own copies of `os`'s initializers over it (`Net/`: without
# raft; `RaftNoAx/`: with its raft), and `RaftNoAx/` and `WalTester/` both have a `durable`
# initializer (the trusted one's, the bodied one's): the part's are generated here, as the main
# tree's, from the part's translation (`KvRaft/Code` over the main tree's) and instances
# (`KvRaft/Proof/`, etc/copy-part.py's copies, over the main tree's), with `net`'s and `durable`'s
# configurations those of `Net/` and `WalTester/`, the imports of the part's modules prefixed, and a
# `PkgInitExt` that is the main tree's with the part's raft; kvraft's and kvcheck's own, and their
# programs' `PkgTable`s (`KVRAFT_PROGRAMS`).
# etc/copy-part.py does not copy these (`kvraft_paths`).
KVRAFT_ROOT = 'KvRaft'
KVRAFT_INITS = PART_INITS + ['net', 'github_com.mit_pdos.etcd_grove.examples.lib.durable',
                            # (`durable`'s imports that `os` does not import)
                            'internal.filepathlite', 'path.filepath']
# (2026-11-22) kvraft's and kvcheck's own (the two programs of the top-level theorem), and their tables
KVRAFT_PKG = 'github_com.mit_pdos.etcd_grove.examples.raft.kvraft'
KVRAFT_INITS += [KVRAFT_PKG, f'{KVRAFT_PKG}.kvcheck']
KVRAFT_PROGRAMS = {KVRAFT_PKG: f'Proof/{KVRAFT_PKG.replace(".", "/")}/PkgTable.lean',
                  f'{KVRAFT_PKG}.kvcheck': f'Proof/{KVRAFT_PKG.replace(".", "/")}/kvcheck/PkgTable.lean'}
KVRAFT_SPECIAL = {**NET_SPECIAL, **WT_SPECIAL}
# kvraft's fact is `True` (`Base.lean`): its one variable, `StatNames` (stats.go), an array literal no
# proof reads, is allocated and stored
KVRAFT_SPECIAL[KVRAFT_PKG] = dict(alloc_types=_ALLOC_ANY, before={'StatNames': ['try wp_auto']})
_KVRAFT_RAW = []
EXT_KVRAFT = {}  # the part's `PkgInitExtRaft`'s registrations (its raft, raft-noax's)


def kvraft_raw():
    """The part's `Init.lean` files, unprefixed: (path under the part, text)."""
    global inv, inst, CFG_OVERRIDE, EXT_RECORD
    if _KVRAFT_RAW:
        return _KVRAFT_RAW[0]
    saved = inv, inst, CFG_OVERRIDE, EXT_RECORD
    try:
        EXT_RECORD = EXT_KVRAFT
        inv = dict(inv)
        for q, d in inventory(f'{KVRAFT_ROOT}/Code').items():
            if not d['perennial']:
                inv[q] = d
        inst = {**inst, **instances(f'{KVRAFT_ROOT}/Proof/')}
        CFG_OVERRIDE = KVRAFT_SPECIAL
        raw = [o for p in KVRAFT_INITS
               for o in gen(p, KVRAFT_SPECIAL.get(p, SPECIAL.get(p)))]
        raw += [gen_table(p, path) for p, path in KVRAFT_PROGRAMS.items()]
    finally:
        inv, inst, CFG_OVERRIDE, EXT_RECORD = saved
    _KVRAFT_RAW.append(raw)
    return raw


def kvraft_paths():
    """The paths (relative to the part) this script writes for the part."""
    return {path for path, _ in kvraft_raw()} | {'Proof/runtime/PkgInitExtRaft.lean'}


def kvraft_inits():
    """The part's `Init.lean` files and `PkgInitExtRaft.lean` (its registrations, `EXT_KVRAFT`)."""
    raw = kvraft_raw()
    made = {f'{KVRAFT_ROOT}/{path}' for path, _ in raw}

    def imp(m):
        x = m.group(2)
        f = f'{KVRAFT_ROOT}/{x.replace(".", "/")}.lean'
        if os.path.exists(f) or f in made or x == 'Proof.runtime.PkgInitExtRaft':
            x = f'{KVRAFT_ROOT}.{x}'
        return m.group(1) + x
    outs = [(f'{KVRAFT_ROOT}/{path}', re.sub(r'(?m)^(public import )(\S+)', imp, txt)) for path, txt in raw]
    path, ext = ext_local('Proof/runtime/PkgInitExtRaft.lean', EXT_RAFT_DOC, EXT_KVRAFT)
    i = ext.index('\nmodule\n') + 1
    note = (f'-- The part `{KVRAFT_ROOT}/`\'s `Proof/runtime/PkgInitExtRaft.lean` (`etc/gen-init.py`):\n'
            f'-- the registrations its generated initializers name, its raft the part\'s (raft-noax\'s).\n')
    outs.append((f'{KVRAFT_ROOT}/{path}', ext[:i] + note + ext[i:]))
    return outs


# The part `Dsverify/` (the dsverify kits ported onto the net extension, notes/dsv-paxos.md): each
# kit's packages over the part `Net/`'s `net` and remote, and the main tree's lintest and porcupine
# (`NET_MAIN`). Generated as `Net/`'s, from `Net/`'s translation and instances with the part's added,
# the imports of the part's modules prefixed `Dsverify.` and of `Net/`'s `Net.`; the programs'
# `PkgTable`s. Each kit configures its own generation in its own file, `etc/dsv/<kit>.py` (format:
# etc/dsv/README.md; `goose.dsv_kits()` loads them), so that a kit adds a file instead of editing
# this one; each kit's packages are generated in a context of its own (`dsv_kit_raw`).
DSV_ROOT = 'Dsverify'
DSV_KITS = _goose.DSV_KITS


# the `HYP_INITS` packages whose `wp_initialize'` stays a premise of the statement (the class
# `InitHyp`, which the generated sections take as an instance) instead of a trust-boundary axiom:
# their `axiom`-skill reviews refuted the axiom (dsv-fix3, 2026-11-25:
# notes/axiom-review/dsv-inits/github-com-go-redis-redis-v8.md, google-golang-org-grpc.md)
DSV_PREMISE_INITS = ['github_com.go_redis.redis.v8', 'google_golang_org.grpc']


def dsv_hyp_fix(path, txt, need):
    """A generated file of the part whose package's closure holds a hypothesis package (`need`:
    the package directory -> its hypothesis packages): its import of that package's
    initialization is the part's `Init.lean`, whose `wp_initialize'` is a trust-boundary axiom
    (dsv-fix3, mit-pdos/etcd-grove#8 2026-11-25T02:20:53Z: until then the class `InitHyp`, which
    the file's sections took as an instance), or, for the `DSV_PREMISE_INITS`, still the class
    `InitHyp`, which the file's sections take as an instance."""
    d = os.path.dirname(path)[len(f'{DSV_ROOT}/Proof/'):]
    for q in need.get(d, []):
        txt = txt.replace(f'public import Perennial.Proof.{q}.Link\n',
                          f'public import {DSV_ROOT}.Proof.{q}.Init\n')
        if f'public import {DSV_ROOT}.Proof.{q}.Init\n' not in txt:
            txt = re.sub(r'(?m)^(public import .*\n)(?!public import)',
                         lambda m: m.group(1) + f'public import {DSV_ROOT}.Proof.{q}.Init\n', txt,
                         count=1)
        if q in DSV_PREMISE_INITS:
            txt = re.sub(r'(?m)^(variable \[sem : go\.Semantics\].*)$',
                         lambda m: m.group(1) + f'\nvariable [_root_.Perennial.{q}.InitHyp GF]', txt)
    return txt


def dsv_special():
    """The kits' `special(g)` configurations, added to `SPECIAL` (a package configured twice is
    an error)."""
    g = types.SimpleNamespace(**globals())
    for k in DSV_KITS:
        for p, cfg in (k.special(g) if hasattr(k, 'special') else {}).items():
            if p in SPECIAL:
                sys.exit(f'gen-init: etc/dsv/{k.KIT}.py configures {p}, which already has a configuration')
            SPECIAL[p] = cfg
            DSV_CFG[p] = k.KIT


DSV_CFG = {}  # a kit-configured package -> its kit
dsv_special()


def dsv_kit_raw(k, base):
    """Kit `k`'s generated files (paths under the part, imports not yet redirected), and the
    package directory -> hypothesis packages map of `dsv_hyp_fix`. `base`: the main tree's
    (`inv`, `inst`), and the inventory and instances of `Net/` and of `Dsverify/`."""
    global inv, inst, CFG_OVERRIDE, RAFT_INIT, pkginfo_imports, EXT_RECORD, EXT_LOCAL_MOD
    main_inv, main_inst, net_inv, net_inst, dsv_inv, dsv_inst = base
    pkgs, programs = getattr(k, 'PKGS', []), getattr(k, 'PROGRAMS', {})
    hyp = list(getattr(k, 'HYP_INITS', []))
    hyp_imports = getattr(k, 'HYP_IMPORTS', 'all')
    # (a dict: per package, `'all'` for a package it does not list)
    hyp_mode = (lambda q: hyp_imports.get(q, 'all')) if isinstance(hyp_imports, dict) \
        else (lambda q: hyp_imports)
    hyp_none = [q for q in hyp if hyp_mode(q) == 'none']
    main = list(getattr(k, 'MAIN', []))
    main_gen = list(getattr(k, 'MAIN_GEN', main))
    own = set(getattr(k, 'OWN', ()))
    saved = inv, inst, CFG_OVERRIDE, RAFT_INIT, pkginfo_imports, set(PERENNIAL_HERE)
    saved_ext = EXT_RECORD, EXT_LOCAL_MOD
    saved_pi = pkginfo_imports
    try:
        EXT_RECORD, EXT_LOCAL_MOD = EXT_DSV, 'Proof.runtime.PkgInitDsv'

        CFG_OVERRIDE = NET_SPECIAL
        RAFT_INIT = RAFT_INIT - set(main)  # a `MAIN` package's `Init` is the part's
        if hyp_none:
            # a hypothesis package's imports, as its `GetIsPkgInitWf` sees them: none (its
            # `Init.lean`), so the programs' tables stop there
            pkginfo_imports = lambda q: [] if q in hyp_none else saved_pi(q)
        inv, inst = dict(net_inv), dict(net_inst)
        _DSV_KEEP.append(inv)  # (`split`'s cache is keyed by `id(inv)`)
        for p in NET_MAIN:
            inv[p] = main_inv[p]
            if p in main_inst:  # (runtime's instance is Perennial's)
                inst[p] = main_inst[p]
        # the main tree's packages `MAIN` (always the main tree's inventory), and those of their
        # imports that `Net/` lacks
        st, seen = list(main), set()
        while st:
            p = st.pop()
            if p in seen or p not in main_inv or (p not in main and (p in inv or p in inst)):
                continue
            seen.add(p)
            inv[p] = main_inv[p]
            if p in main_inst:
                inst[p] = main_inst[p]
            st += main_inv[p]['imports']
        for q, d in dsv_inv.items():
            if not d['perennial']:
                inv[q] = d
        # the packages whose `wp_initialize'` is a hypothesis (`Dsverify/Proof/<pkg>/Init.lean`'s
        # class `InitHyp`): external here, their imports as `HYP_IMPORTS` says
        for q in hyp:
            inv[q] = dict(inv[q], perennial=True)
            if hyp_mode(q) == 'none':
                inv[q]['imports'] = []
            elif hyp_mode(q) == 'known':
                inv[q]['imports'] = [i for i in inv[q]['imports'] if i in inv]
        # (dsv-fix2, 2026-11-25) net/rpc's and net/http's models, when not a hypothesis of the
        # kit: external, their `wp_initialize'` `Net/`'s interim axioms (`NET_AXIOM_INITS`), as in
        # `Net/`'s programs
        netax = [q for q in NET_AXIOM_INITS if q not in hyp and q in inv]
        for q in netax:
            inv[q] = dict(inv[q], perennial=True)
        PERENNIAL_HERE.difference_update(hyp + netax)
        gen_pkgs = [p for p in pkgs if os.path.exists(f'{DSV_ROOT}/Code/{dirof(p)}.lean')] + main_gen
        gen_pkgs = [p for p in dict.fromkeys(gen_pkgs) if p not in hyp and p not in netax]
        need = {dirof(p): [q for q in hyp if q in closure(p)] for p in pkgs + main_gen if p in inv}
        inst.update(dsv_inst)
        raw = [(f'{DSV_ROOT}/{path}', txt) for p in gen_pkgs
               for path, txt in gen(p, None if p in own and DSV_CFG.get(p) != k.KIT
                                    else SPECIAL.get(p))]
        for p, path in programs.items():
            path, txt = gen_table(p, path)
            raw.append((f'{DSV_ROOT}/{path}', txt))
        # the axiom packages' `wp_initialize'`: `Net/`'s hand-written `Init.lean`
        for q in netax:
            raw = [(path, txt.replace(f'public import Perennial.Proof.{q}.Link\n',
                                      f'public import Net.Proof.{q}.Init\n')) for path, txt in raw]
    finally:
        inv, inst, CFG_OVERRIDE, RAFT_INIT, pkginfo_imports, here = saved
        EXT_RECORD, EXT_LOCAL_MOD = saved_ext
        PERENNIAL_HERE.clear()
        PERENNIAL_HERE.update(here)
    return raw, need


_DSV_KEEP = []
EXT_DSV = {}  # the part's registrations (`Dsverify/Proof/runtime/PkgInitDsv.lean`)


def dsv_inits(main_txt):
    """The part's `Init.lean` files and its programs' `PkgTable.lean`, every kit's (but those that
    are the main tree's, `shared_inits`; after `net_inits`), and its registrations
    (`PkgInitDsv.lean`); and the paths of the shared ones."""
    base = (inv, inst, inventory(f'{NET_ROOT}/Code'), instances(f'{NET_ROOT}/Proof/'),
            inventory(f'{DSV_ROOT}/Code'), instances(f'{DSV_ROOT}/Proof/'))
    raw, need, by = [], {}, {}
    for k in DSV_KITS:
        r, n = dsv_kit_raw(k, base)
        for path, txt in r:
            if path in by:
                if by[path][1] != txt:
                    sys.exit(f'gen-init: kits {by[path][0]} and {k.KIT} generate {path} differently')
                continue
            by[path] = (k.KIT, txt)
            raw.append((path, txt))
            need[path] = n
    gen_paths = {path for path, _ in raw} | {f'{DSV_ROOT}/Proof/runtime/PkgInitDsv.lean'}

    def dsv_has(f, shared):
        g = f'{DSV_ROOT}/{f}'
        if g in gen_paths:
            return g not in shared
        return os.path.exists(g)

    def hyp(path):
        return need[path].get(os.path.dirname(path)[len(f'{DSV_ROOT}/Proof/'):], [])
    def resolve(txt, shared):
        def imp(m):
            x = m.group(2)
            f = x.replace('.', '/') + '.lean'
            if dsv_has(f, shared):
                x = f'{DSV_ROOT}.{x}'
            elif net_has(f):
                x = f'{NET_ROOT}.{x}'
            return m.group(1) + x
        return re.sub(IMPORT_RE, imp, txt)
    shared = shared_inits([(p, t) for p, t in raw if not hyp(p)], main_txt, resolve)
    outs = [(path, dsv_hyp_fix(path, resolve(txt, shared), need[path]))
            for path, txt in raw if path not in shared]
    outs.append(ext_local(f'{DSV_ROOT}/Proof/runtime/PkgInitDsv.lean', EXT_DSV_DOC, EXT_DSV))
    return outs, sorted(shared)


def main(argv):
    check = '--check' in argv
    pkgs = [a for a in argv if not a.startswith('--')] or packages()
    bad = []
    outs = [o for p in pkgs for o in gen(p, SPECIAL.get(p))]
    full = not [a for a in argv if not a.startswith('--')]
    stale = []
    if full:
        outs += [gen_table(p, path) for p, path in PROGRAMS.items()]
        outs += [dag_closures()] + dag_init() + [
                 gen_closures('', TC_PKG, TC_CLOSURES, 'etcdraftInit', 'TC_CLOSURES')]
        outs += tla_outs()
        outs += wt_inits()
        main_txt = dict(outs)
        o, st = net_inits(main_txt)
        outs += o
        stale += st
        outs += kvraft_inits()
        o, st = dsv_inits(main_txt)
        outs += o
        stale += st
        # (after every tree's generation: the registrations are those the generated files name)
        outs += gen_ext()
    outs += [part_copy(path, txt, root) for root, (inits, _) in PARTS.items()
             for path, txt in outs if path in part_paths(inits)]
    # the files of the parts' that are now the main tree's (`shared_inits`), and the parts' former
    # copies of `PkgInitExt` (L1, 2026-11-24): stale, to delete
    if full:
        stale += [f'{r}/Proof/runtime/PkgInitExt.lean' for r in (NET_ROOT, KVRAFT_ROOT, *PARTS)]
    for path in stale:
        if os.path.exists(path):
            if check:
                bad.append(path)
            print(f'gen-init: stale (delete it: git rm {path})', file=sys.stderr)
    for path, txt in outs:
        old = open(path).read() if os.path.exists(path) else None
        if old == txt:
            continue
        if check:
            bad.append(path)
        else:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            open(path, 'w').write(txt)
            print('wrote', path)
    if check:
        for b in bad:
            print('gen-init: differs from the generated:', b)
        if bad:
            sys.exit(1)
        print(f'gen-init: {len(pkgs)} files up to date')


if __name__ == '__main__':
    main(sys.argv[1:])
