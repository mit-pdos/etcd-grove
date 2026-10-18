#!/usr/bin/env python3
"""Generate the package initialization proofs `Proof/<pkg>/Init.lean` (item 8).

Each file proves `<pkg>.wp_initialize'`: running the package's Goose `initialize'` from
`ownInitializing` gives its `isPkgInit`. The proof follows the translation's `initialize'` in
execution order (the `GlobalAlloc`s of the translated variables, the imports' `initialize'`, the
variables' initializers); an untranslated initializer (`X.init`, an axiom of the translation)
gets a trust-boundary axiom of the file: `opaqueInitsOk` (it runs), `errorsNewVarsInit` (it is
`errors.New(msg)`) or `<X>_init` (what a fact reads of it). The packages are the import closure
of `ROOTS`, but Perennial's (with a `Link`), raft's (`Proof/go_etcd_io/raft/v3/Init.lean`), the
B-tree's (`initialize.lean`) and `NOT_YET`; a package whose fact is not `True` or whose
initializer runs translated code needs an entry in `SPECIAL` (the per-package doc, axioms, the
hand-written steps `before` an item, and the `finish`).

Each theorem is proved in a form that keeps what is initialized (decision D19e,
`Proof/runtime/PkgInit.lean`): `wp_initialize'_lb` (from `ownInitLb g σ0`, for every `σ0`) or,
for a package whose import closure contains a `PRE_RES` package, `wp_initialize'_res` (from
`ownInitRes g q R`: `R` held unless `q` is initialized); `wp_initialize'` (Perennial's form, with
`R` for the latter) follows. The other packages' (Perennial's, raft's, the B-tree's) `_lb` forms
come from their `wp_initialize'` by the trust-boundary axiom `EtcdGrove.initLb_of_spec`, over the
initializers listed in the generated `Proof/runtime/PkgInitExt.lean` (`ExternalInit`).

  etc/gen-init.py            regenerate every file
  etc/gen-init.py --check    exit 1 if a file differs from what would be generated
  etc/gen-init.py PKG...     regenerate these packages (Lean names, `go_etcd_io.etcd.pkg.v3.wait`)
"""
import glob, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
PERENNIAL_CODE = '.lake/packages/perennial/Perennial/Code'

ROOTS = ['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc', 'go_etcd_io.etcd.server.v3.etcdserver',
         'go_etcd_io.etcd.client.v3', 'go_etcd_io.etcd.server.v3.etcdserver.read',
         'github_com.mit_pdos.etcd_grove.examples.putget']
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
PRE_RES = {'go_etcd_io.etcd.server.v3.etcdserver.read': 'EtcdGrove.read.readRegPerm'}
# Perennial packages without Perennial's `wp_initialize'` (names-only there): generated here.
PERENNIAL_HERE = {'math.rand', 'reflect'}


def inventory():
    """Every translated package: its file, imports, untranslated initializers, translated vars."""
    out = {}
    files = sorted(glob.glob('Code/**/*.lean', recursive=True)) + \
        sorted(glob.glob(PERENNIAL_CODE + '/**/*.lean', recursive=True))
    for f in files:
        t = open(f).read()
        m = re.search(r"instance info' : PkgInfo pkg_id\.(\S+) where", t)
        if not m:
            continue
        i = t.find("noncomputable def initialize'")
        body = t[i:t.find("\n\n", i)]
        out[m.group(1)] = dict(
            file=f, perennial=f.startswith('.lake'),
            imports=re.findall(r"\(Val _root_\.Perennial\.(\S+)\.initialize'\)", body))
    return out


def instances():
    """Where each package's `IsPkgInit` instance is (first in path order) and its fact."""
    loc = {}
    for f in sorted(glob.glob('Proof/**/*.lean', recursive=True)):
        t = open(f).read()
        for m in re.finditer(r"IsPkgInit \(IProp GF\) pkg_id\.(\S+?) :=\s*\n?\s*define_is_pkg_init\s+(\S+)", t):
            loc.setdefault(m.group(1).replace('«attribute»', 'attribute'), []).append(
                (f[len('Proof/'):-len('.lean')], m.group(2)))
    return loc


inv = inventory()
inst = instances()

# Per-package configuration of the packages with facts or translated initializers.
SPECIAL = {}

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.errors'] = dict(
    doc='''Its fact (`errorsInit`, `errors/Base.lean`): `ErrNoSpace` holds a pointer error. Its
initializer runs its variables' initializers, all untranslated `errors.New` calls (`errors.go`),
which the trust-boundary axiom `errorsNewVarsInit` states.''',
    newvars=dict(ErrUnknownMethod="etcdserver: unknown method",
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
        ErrKeyNotFound="etcdserver: key not found"),
    finish=['ipersist HErrNoSpace', 'iframe Hown', 'imodintro', 'isplitr',
            '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish', 'try (isplitl []; · (imodintro; itrivial))', 'imodintro', 'iexists _',
            'iframe HErrNoSpace', 'ipureintro', 'exact ⟨_, _, rfl, rfl⟩'],
)

SPECIAL['go_etcd_io.bbolt.errors'] = dict(
    doc='''Its fact (`bboltErrorsInit`, `storage/backend/Base.lean`): `ErrBucketNotFound` holds an
`errors.New` error, a leaf pointer error without an `Is` method (`EtcdGrove.ErrorStringLeaf`, a
premise on the method sets). Its initializer runs its variables' initializers, all untranslated
`errors.New` calls (`errors/errors.go`), which the trust-boundary axiom `errorsNewVarsInit`
states.''',
    newvars=dict(ErrDatabaseNotOpen="database not open",
        ErrInvalid="invalid database",
        ErrInvalidMapping="database isn't correctly mapped",
        ErrVersionMismatch="version mismatch",
        ErrChecksum="checksum error",
        ErrTimeout="timeout",
        ErrTxNotWritable="tx not writable",
        ErrTxClosed="tx closed",
        ErrDatabaseReadOnly="database is in read-only mode",
        ErrFreePagesNotLoaded="free pages are not pre-loaded",
        ErrBucketNotFound="bucket not found",
        ErrBucketExists="bucket already exists",
        ErrBucketNameRequired="bucket name required",
        ErrKeyRequired="key required",
        ErrKeyTooLarge="key too large",
        ErrValueTooLarge="value too large",
        ErrMaxSizeReached="database reached maximum size",
        ErrIncompatibleValue="incompatible value",
        ErrSameBuckets="the source and target are the same bucket",
        ErrDifferentDB="the source and target buckets are in different database files"),
    vars=['[EtcdGrove.ErrorStringLeaf]'],
    finish=['ipersist HErrBucketNotFound', 'iframe Hown', 'imodintro', 'isplitr',
            '· ipureintro', '  exact isPanic_intoVal _', 'is_pkg_init_finish', 'try (isplitl []; · (imodintro; itrivial))', 'imodintro', 'iexists _',
            'iframe HErrBucketNotFound', 'ipureintro',
            'exact ⟨⟨_, _, rfl, rfl⟩, EtcdGrove.ErrorStringLeaf.leaf _, EtcdGrove.ErrorStringLeaf.noIs⟩'],
)

FIN_PRE = ['iframe Hown', 'imodintro', 'isplitr', '· ipureintro', '  exact isPanic_intoVal _',
           'is_pkg_init_finish', 'try (isplitl []; · (imodintro; itrivial))', 'imodintro']

SPECIAL['go_etcd_io.etcd.api.v3.version'] = dict(
    doc='''Its fact (`server/v3/lease/Base.lean`): `Version` and `V3_6` hold fixed values. Its
initializer runs its variables' untranslated initializers (`version.go`): string constants,
`semver` versions (`*semver.New(3, 6, 0, "", "")`), and `AllVersions`; the trust-boundary axioms
`Version_init` and `V3_6_init` state the two the fact reads, `opaqueInitsOk` the others.''',
    custom={
        'Version': dict(doc='/-- `Version = "3.8.0-alpha.0"` (`version.go`): a string. -/',
                        post='∃ v : GoString, globalAddr Version ↦ v', pat='⟨%v@, H@⟩'),
        'V3_6': dict(doc='/-- `V3_6 = *semver.New(3, 6, 0, "", "")` (`version.go`): a `semver.Version`. -/',
                     post='∃ v : github_com.Masterminds.semver.v3.Version, globalAddr V3_6 ↦ v',
                     pat='⟨%v@, H@⟩'),
    },
    finish=['ipersist HVersion', 'ipersist HV3_6'] + FIN_PRE[:6],
)

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.membership'] = dict(
    doc='''Its fact (`etcdserver/apply/Base.lean`): `ClusterVersionMetrics` holds a fixed pointer
(a `*prometheus.GaugeVec`). Its initializer initializes its imports and runs its variables'
untranslated initializers; the trust-boundary axiom `ClusterVersionMetrics_init` states the one
the fact reads (`metrics.go`: `prometheus.NewGaugeVec(...)`), `opaqueInitsOk` the others.''',
    custom={
        'ClusterVersionMetrics': dict(
            doc='/-- `ClusterVersionMetrics = prometheus.NewGaugeVec(...)` (`metrics.go`): a `*GaugeVec`. -/',
            post='∃ gv : Loc, globalAddr ClusterVersionMetrics ↦ gv', pat='⟨%gv@, H@⟩'),
    },
    finish=['ipersist HClusterVersionMetrics'] + FIN_PRE[:6],
)

def hist(x, file='metrics.go'):
    return dict(doc=f'/-- `{x} = prometheus.NewHistogram(...)` (`{file}`): a `Histogram`, whose `Observe` returns. -/',
                post=f'∃ h : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok h ∗ histSpec h',
                pat='⟨%h@, H@, #S@⟩')

SPECIAL['go_etcd_io.etcd.server.v3.storage.backend'] = dict(
    doc='''Its fact (`backendInit`, `Base.lean`): the commit's histograms `rebalanceSec`,
`spillSec`, `writeSec`, `commitSec` hold `Histogram`s whose `Observe` returns. Its initializer
allocates and sets its translated constants, initializes its imports and runs its variables'
untranslated initializers; the trust-boundary axioms `<X>_init` state the four the fact reads
(`metrics.go`: `prometheus.NewHistogram(...)`), `opaqueInitsOk` the others.''',
    custom={x: hist(x) for x in ['commitSec', 'rebalanceSec', 'spillSec', 'writeSec']},
    alloc_types={'defaultBatchLimit': 'w64', 'defaultBatchInterval': 'w64', 'defragLimit': 'w64',
                 'InitialMmapSize': 'w64', 'minSnapshotWarningTimeout': 'w64'},
    finish=['ipersist HcommitSec', 'ipersist HrebalanceSec', 'ipersist HspillSec', 'ipersist HwriteSec']
           + FIN_PRE[:6] + ['imodintro', 'unfold backendInit', 'iframe #'],
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
    doc='''Its fact (`schemaInit`, `etcdserver/Base.lean`): the `Meta` and `Key` buckets, as
`bucket.go` makes them, and the consistent index's two key names (`cindex.go`). Its initializer
allocates and sets those translated variables (with `keyBucketName`, `metaBucketName`),
initializes its imports and runs its other variables' untranslated initializers, which the
trust-boundary axiom `opaqueInitsOk` says run.''',
    alloc_types={'MetaTermKeyName': 'GoSlice', 'MetaConsistentIndexKeyName': 'GoSlice',
                 'Meta': 'GoInterface', 'Key': 'GoInterface', 'metaBucketName': 'GoSlice',
                 'keyBucketName': 'GoSlice'},
    before={
        'leaseBucketName': ['wp_apply wp_string_to_bytes go!"key" as %skey ⟨Hskey, -⟩', 'try wp_auto',
                            'wp_apply wp_string_to_bytes go!"meta" as %smeta ⟨Hsmeta, -⟩', 'try wp_auto'],
        'Lease': ['try wp_auto'],
        'AuthEnabledKeyName': ['wp_apply wp_string_to_bytes go!"consistent_index" as %sci ⟨Hsci, -⟩',
                               'try wp_auto'],
        'MetaConfStateName': ['wp_apply wp_string_to_bytes go!"term" as %sterm ⟨Hsterm, -⟩', 'try wp_auto'],
    },
    finish=['ipersist Hskey', 'ipersist Hsmeta', 'ipersist Hsci', 'ipersist Hsterm',
            'ipersist HKey', 'ipersist HMeta', 'ipersist HMetaConsistentIndexKeyName',
            'ipersist HMetaTermKeyName'] + FIN_PRE[:6] + ['imodintro', 'unfold schemaInit bucketIs metaName ciKeyBytes termKeyBytes keyName',
            'iframe #', 'isplitl []', '· ipureintro; rfl', 'ipureintro; rfl'],
)

def counter_inc(x, file='metrics.go'):
    return dict(doc=f'/-- `{x} = prometheus.NewCounter(...)` (`{file}`): a `Counter`, whose `Inc` returns. -/',
                post=f'∃ c : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok c ∗ counterSpec c',
                pat='⟨%c@, H@, #S@⟩')

SPECIAL['go_etcd_io.etcd.server.v3.lease'] = dict(
    doc='''Its fact (`leaseInit`, `Base.lean`): the error variables `ErrLeaseNotFound`,
`ErrLeaseExists`, `ErrLeaseTTLTooLarge` (translated `errors.New` calls: leaf pointer errors
without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose `Error()` returns), `forever` (the zero
`time.Time`), the counters `leaseGranted`, `leaseRevoked` and the histogram `leaseTotalTTLs`
(`metrics.go`, untranslated: the trust-boundary axioms `<X>_init`); `opaqueInitsOk` states the
other untranslated initializers run.''',
    imports=['Proof.errors.NewVar', 'Perennial.Proof.context.NewErrorString'],
    vars=['[EtcdGrove.ErrorStringLeaf]'],
    custom={'leaseGranted': counter_inc('leaseGranted'), 'leaseRevoked': counter_inc('leaseRevoked'),
            'leaseTotalTTLs': dict(
                doc='/-- `leaseTotalTTLs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/',
                post='∃ h : GoInterfaceOk, globalAddr leaseTotalTTLs ↦ GoInterface.ok h ∗ go_etcd_io.etcd.server.v3.storage.backend.histSpec h',
                pat='⟨%h@, H@, #S@⟩')},
    alloc_types={'ErrLeaseTTLTooLarge': 'GoInterface', 'ErrLeaseExists': 'GoInterface',
                 'ErrLeaseNotFound': 'GoInterface', 'forever': '_root_.Perennial.time.Time'},
    before={'leaseGranted': [
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xNF #MNF',
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xEx #MEx',
        'wp_apply _root_.Perennial.context.wp_New_errorString as %xTL #MTL']},
    finish=['ipersist HErrLeaseNotFound', 'ipersist HErrLeaseExists', 'ipersist HErrLeaseTTLTooLarge',
            'ipersist Hforever', 'ipersist HleaseGranted', 'ipersist HleaseRevoked',
            'ipersist HleaseTotalTTLs',
            'ihave #TNF := EtcdGrove.errorMsg_triple _ _ _ $$ MNF',
            'ihave #TEx := EtcdGrove.errorMsg_triple _ _ _ $$ MEx',
            'ihave #TTL := EtcdGrove.errorMsg_triple _ _ _ $$ MTL'] + FIN_PRE[:6] + [
            'imodintro', 'unfold leaseInit leaseErrVar', 'iframe #', 'dsimp only', 'iframe #',
            'repeat (first | (isplitl []; · (ipureintro; exact EtcdGrove.errorString_leaf _)) | (ipureintro; exact EtcdGrove.errorString_leaf _))'],
)

SPECIAL['go_etcd_io.etcd.pkg.v3.wait'] = dict(
    doc='''Its fact is `True`. Its initializer allocates `closec`, initializes its imports and runs
its translated `init()` (`wait_time.go`: `closec = make(chan struct{}); close(closec)`).''',
    alloc_types={'closec': 'GoChan'},
    before={'$end': [
        'wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩',
        'wp_apply_core chan.wp_close (V := Unit) ch γ $$ His_ch',
        'iintro -', 'unfold closeAu', 'iapply fupd_mask_intro Std.LawfulSet.empty_subset',
        'iintro Hmask', 'inext', 'iexists .Idle', 'iframe Hch', 'dsimp only', 'iintro Hch',
        'imod Hmask with -', 'imodintro', 'wp_auto']},
)

CV3 = 'go_etcd_io.etcd.cache.v3'
SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes'] = dict(
    doc='''Its fact (`rpctypesInit`, `cache/v3/Base.lean`): the errors `ErrFutureRev`, `ErrCompacted`
(`EtcdError`s, whose `Error()` returns), the map `errStringToError` (its values `status.Error`
errors grpc's `status` accepts), `EtcdError`'s method set (`EtcdGrove.RpctypesEtcdErrorMethods`, a
premise on the method sets), the `EtcdError`s `ErrUserEmpty`, `ErrInvalidAuthToken`,
`ErrAuthOldRevision` and the pointer error `ErrGRPCNotSupportedForLearner`. Its variables'
initializers (`error.go`, `metadatafields.go`) are untranslated: the trust-boundary axioms
`<X>_init` state the ones the fact reads, `opaqueInitsOk` the others.''',
    pre=['/-- **The method set of `rpctypes.EtcdError`** is `{Code, Error}` (`error.go`): no `As`,',
         '`Unwrap`, `GRPCStatus` or `Is` method. A fact about the method sets, which the semantics leaves',
         'uninterpreted: a premise, as `EtcdGrove.ErrorStringLeaf`. -/',
         'class EtcdGrove.RpctypesEtcdErrorMethods [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] : Prop where',
         '  leaf : ∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩',
         '  noGRPCStatus : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none',
         '  noIs : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none',
         ''],
    vars=['[EtcdGrove.RpctypesEtcdErrorMethods]'],
    custom={
        'ErrFutureRev': dict(doc='/-- `ErrFutureRev = Error(ErrGRPCFutureRev)` (`error.go`): an `EtcdError`, whose `Error()` returns its description. -/',
                             post=f'∃ e : GoInterfaceOk, globalAddr ErrFutureRev ↦ GoInterface.ok e ∗ {CV3}.errorStringSpec e',
                             pat='⟨%e@, H@, #S@⟩'),
        'ErrCompacted': dict(doc='/-- `ErrCompacted = Error(ErrGRPCCompacted)` (`error.go`): an `EtcdError`, whose `Error()` returns its description. -/',
                             post=f'∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦ GoInterface.ok e ∗ {CV3}.errorStringSpec e',
                             pat='⟨%e@, H@, #S@⟩'),
        'errStringToError': dict(doc='/-- `errStringToError = map[string]error{...}` (`error.go`): a map whose values are `ErrGRPC*` errors, `status.Error(...)`s: `*status.Error`s, leaf errors whose `Error()`, `GRPCStatus()` and `Is` return. -/',
                                 post=f'∃ (mref : Loc) (m : GMap GoString GoInterface), globalAddr errStringToError ↦ mref ∗ mref ↦$□ m ∗ □ (∀ (k : GoString) (v : GoInterface), ⌜m !! k = some v⌝ → {CV3}.statusErrOk v)',
                                 pat='⟨%mref@, %m@, H@, #M@, #S@⟩'),
        'ErrUserEmpty': dict(doc='/-- `ErrUserEmpty = Error(ErrGRPCUserEmpty)` (`error.go`): an `EtcdError`. -/',
                             post='∃ x : EtcdError, globalAddr ErrUserEmpty ↦ interface.mkOk EtcdError.ty #x',
                             pat='⟨%x@, H@⟩'),
        'ErrInvalidAuthToken': dict(doc='/-- `ErrInvalidAuthToken = Error(ErrGRPCInvalidAuthToken)` (`error.go`): an `EtcdError`. -/',
                             post='∃ x : EtcdError, globalAddr ErrInvalidAuthToken ↦ interface.mkOk EtcdError.ty #x',
                             pat='⟨%x@, H@⟩'),
        'ErrAuthOldRevision': dict(doc='/-- `ErrAuthOldRevision = Error(ErrGRPCAuthOldRevision)` (`error.go`): an `EtcdError`. -/',
                             post='∃ x : EtcdError, globalAddr ErrAuthOldRevision ↦ interface.mkOk EtcdError.ty #x',
                             pat='⟨%x@, H@⟩'),
        'ErrGRPCNotSupportedForLearner': dict(doc='/-- `ErrGRPCNotSupportedForLearner = status.Error(codes.FailedPrecondition, ...)` (`error.go`): a `*status.Error`, a pointer error. -/',
                             post='∃ e : GoInterfaceOk, globalAddr ErrGRPCNotSupportedForLearner ↦ GoInterface.ok e ∗ ⌜errors.IsPointerError e⌝',
                             pat='⟨%e@, H@, %P@⟩'),
    },
    finish=['ipersist HErrFutureRev', 'ipersist HErrCompacted', 'ipersist HerrStringToError',
            'ipersist HErrUserEmpty', 'ipersist HErrInvalidAuthToken', 'ipersist HErrAuthOldRevision',
            'ipersist HErrGRPCNotSupportedForLearner',
            'ihave #HFRS : iprop(□ ∀ e : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok e -∗',
            '    go_etcd_io.etcd.cache.v3.errorStringSpec e) $$ []',
            '· iintro !> %e He',
            '  icombine HErrFutureRev He gives %Heq',
            '  cases Heq',
            '  iexact SErrFutureRev'] + FIN_PRE[:6] + [
            'imodintro', 'unfold go_etcd_io.etcd.cache.v3.rpctypesInit', 'iframe #',
            'ipureintro', 'refine ⟨?_, by assumption⟩',
            'exact ⟨EtcdGrove.RpctypesEtcdErrorMethods.leaf, EtcdGrove.RpctypesEtcdErrorMethods.noGRPCStatus, EtcdGrove.RpctypesEtcdErrorMethods.noIs⟩'],
)

SPECIAL['go_etcd_io.etcd.client.v3'] = dict(
    doc='''Its fact (`clientv3Init`, `cache/v3/Base.lean`): `noPrefixEnd` (`op.go`, translated:
`[]byte{0}`) and `defaultOptions` (`retry_interceptor.go`, untranslated: `&options{...}` whose
backoff function returns; the trust-boundary axiom `defaultOptions_init`), and its translated
`valCtxCh`, `zeroTime` (`time.Unix(0, 0)`, the trust-boundary axiom `time.Unix.wp_proof`) and
`maxBackoff`. Its initializer also runs its other untranslated initializers
(`opaqueInitsOk`).''',
    imports=['Proof.time.Unix'],
    alloc_types={'maxBackoff': 'w64', 'zeroTime': '_root_.Perennial.time.Time', 'valCtxCh': 'GoChan',
                 'noPrefixEnd': 'GoSlice'},
    custom={'defaultOptions': dict(
        doc='/-- `defaultOptions = &options{..., backoffFunc: backoffLinearWithJitter(50*time.Millisecond, 0.10), ...}` (`retry_interceptor.go`): a pointer to fixed options whose backoff function returns (`jitterUp`\'s float arithmetic and `rand.Float64`, which do not panic). -/',
        post=f'∃ (dp : Loc) (ov : options), globalAddr defaultOptions ↦ dp ∗ dp ↦□ ov ∗ {CV3}.backoffOk ov.backoffFunc\'',
        pat='⟨%dp@, %ov@, H@, #P@, #S@⟩')},
    before={'defaultWaitForReady': [
        'wp_apply wp_slice_literal (l := [W8 0])', 'isplitr', '· ipureintro; rfl',
        'iintro %snp ⟨Hsnp, -⟩', 'try wp_auto'],
        '$end': ['wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩',
                 'wp_apply EtcdGrove.time.Unix.wp_proof as %zt -']},
    finish=['ipersist Hsnp', 'ipersist HnoPrefixEnd', 'ipersist HdefaultOptions'] + FIN_PRE[:6] + [
            'imodintro', 'unfold go_etcd_io.etcd.cache.v3.clientv3Init', 'iframe #'],
)

SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes']['custom'].update({
    'TokenFieldNameGRPC': dict(doc='/-- `TokenFieldNameGRPC = "token"` (`metadatafields.go`): a string. -/',
                               post='∃ s : GoString, globalAddr TokenFieldNameGRPC ↦ s', pat='⟨%s@, H@⟩'),
    'TokenFieldNameSwagger': dict(doc='/-- `TokenFieldNameSwagger = "authorization"` (`metadatafields.go`): a string. -/',
                               post='∃ s : GoString, globalAddr TokenFieldNameSwagger ↦ s', pat='⟨%s@, H@⟩'),
})
SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes']['finish'] = (
    ['ipersist HTokenFieldNameGRPC', 'ipersist HTokenFieldNameSwagger'] +
    SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes']['finish'])

SPECIAL['go_etcd_io.etcd.server.v3.auth'] = dict(
    doc='''Its fact (`authInit`, `Base.lean`): its error variables `ErrUserEmpty`, `ErrUserNotFound`,
`ErrPermissionDenied`, `ErrAuthOldRevision`, `ErrInvalidAuthToken` (translated `errors.New`
calls: leaf pointer errors without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose `Error()`
returns), and `rpctypes`' token keys (from `rpctypes`' fact). Its other variables' initializers
are untranslated (`opaqueInitsOk`).''',
    imports=['Proof.errors.NewVar', 'Perennial.Proof.context.NewErrorString'],
    vars=['[EtcdGrove.ErrorStringLeaf]'],
    alloc_types={x: 'GoInterface' for x in ['ErrInvalidAuthToken', 'ErrAuthOldRevision',
                 'ErrPermissionDenied', 'ErrUserNotFound', 'ErrUserEmpty']},
    before={
        'ErrRoleAlreadyExist': ['wp_apply _root_.Perennial.context.wp_New_errorString as %xUE #MUE',
                                'wp_apply _root_.Perennial.context.wp_New_errorString as %xUNF #MUNF'],
        'ErrRoleNotGranted': ['wp_apply _root_.Perennial.context.wp_New_errorString as %xPD #MPD'],
        'ErrInvalidAuthOpts': ['wp_apply _root_.Perennial.context.wp_New_errorString as %xAO #MAO',
                               'wp_apply _root_.Perennial.context.wp_New_errorString as %xIA #MIA'],
    },
    finish=['ipersist HErrUserEmpty', 'ipersist HErrUserNotFound', 'ipersist HErrPermissionDenied',
            'ipersist HErrAuthOldRevision', 'ipersist HErrInvalidAuthToken',
            'ihave #TUE := EtcdGrove.errorMsg_triple _ _ _ $$ MUE',
            'ihave #TUNF := EtcdGrove.errorMsg_triple _ _ _ $$ MUNF',
            'ihave #TPD := EtcdGrove.errorMsg_triple _ _ _ $$ MPD',
            'ihave #TAO := EtcdGrove.errorMsg_triple _ _ _ $$ MAO',
            'ihave #TIA := EtcdGrove.errorMsg_triple _ _ _ $$ MIA',
            'ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []',
            '· iapply isPkgInit_access $$ Hd11',
            'icases Hri with ⟨-, -, -, -, -, -, -, -, -, #HTG, #HTS, -⟩'] + FIN_PRE[:6] + [
            'imodintro', 'unfold authInit authErrVar', 'iframe #', 'dsimp only', 'iframe #',
            'repeat (first | (isplitl []; · (ipureintro; exact EtcdGrove.errorString_leaf _)) | (ipureintro; exact EtcdGrove.errorString_leaf _))'],
)

# Item 8, step 3 (2026-10-17): facts moved into their owners' packages.
_E = SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.errors']
_E['doc'] = """Its fact (`errorsInit`, `errors/Base.lean`): `ErrNoSpace` holds a pointer error, and every
error variable its `errors.New` error (`errorsNewVars errorsMsgs`). Its initializer runs its
variables' initializers, all untranslated `errors.New` calls (`errors.go`), which the
trust-boundary axiom `errorsNewVarsInit` states."""
_E['finish'] = ([f'ipersist H{x}' for x in _E['newvars']] + FIN_PRE[:6] +
    ['try (isplitl []; · (imodintro; itrivial))', 'imodintro',
     'unfold errorsInit errorsMsgs', 'simp only [EtcdGrove.errorsNewVars, EtcdGrove.errorsNewVar]',
     'iframe #', 'ipureintro', 'exact ⟨_, _, rfl, rfl⟩'])

_B = SPECIAL['go_etcd_io.etcd.server.v3.storage.backend']
_B['custom']['boltOpenOptions'] = dict(
    doc='/-- `boltOpenOptions = &bolt.Options{MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true}` (`config_linux.go`; nil on other systems): read-write options with the default page size and `OpenFile`. -/',
    post='∃ p : Loc, globalAddr boltOpenOptions ↦ p ∗ (⌜p = Loc.null⌝ ∨ ∃ o : EtcdGrove.backend.OptsM, EtcdGrove.backend.optsAt p DFrac.discard o ∗ ⌜o.ok⌝)',
    pat='⟨%p@, H@, #S@⟩')
_B['doc'] = _B['doc'].replace("hold `Histogram`s whose `Observe` returns.", "hold `Histogram`s whose `Observe` returns, and `boltOpenOptions` (`boltOpenOptionsOk`).")
_B['finish'] = (['ipersist HcommitSec', 'ipersist HrebalanceSec', 'ipersist HspillSec', 'ipersist HwriteSec',
                 'ipersist HboltOpenOptions'] + FIN_PRE[:6] +
                ['imodintro', 'unfold backendInit EtcdGrove.backend.boltOpenOptionsOk', 'iframe #'])

SPECIAL['go_etcd_io.etcd.pkg.v3.traceutil'] = dict(
    doc="""Its fact (`traceutilInit`, `storage/mvcc/Base.lean`): `Tracer` holds a fixed tracer. Its
variables' initializers are untranslated: the trust-boundary axiom `Tracer_init` states the one
the fact reads (`trace.go`), `opaqueInitsOk` the others.""",
    custom={'Tracer': dict(
        doc='/-- `Tracer = noop.NewTracerProvider().Tracer(instrumentationScope)` (`trace.go`): a `trace.Tracer`. -/',
        post='∃ tr : GoInterfaceOk, globalAddr Tracer ↦ GoInterface.ok tr', pat='⟨%tr@, H@⟩')},
    finish=['ipersist HTracer'] + FIN_PRE[:6] + ['imodintro', 'unfold traceutilInit', 'iframe #'],
)

_R = SPECIAL['go_etcd_io.etcd.api.v3.v3rpc.rpctypes']
_RERRS = ['ErrGRPCEmptyKey', 'ErrGRPCInvalidSortOption', 'ErrGRPCValueProvided', 'ErrGRPCLeaseProvided',
          'ErrGRPCTooManyOps', 'ErrGRPCDuplicateKey', 'ErrGRPCKeyNotFound', 'ErrGRPCNoSpace',
          'ErrGRPCNotCapable', 'ErrGRPCInvalidClientAPIVersion', 'ErrGRPCNoLeader']
_RKEYS = {'MetadataClientAPIVersionKey': 'client-api-version', 'MetadataRequireLeaderKey': 'hasleader',
          'MetadataHasLeader': 'true'}
for x in _RERRS:
    _R['custom'][x] = dict(doc=f'/-- `{x} = status.Error(...)` (`error.go`): a non-nil error. -/',
                           post=f'∃ e : GoInterfaceOk, globalAddr {x} ↦ GoInterface.ok e', pat='⟨%e@, H@⟩')
for x, v in _RKEYS.items():
    _R['custom'][x] = dict(doc=f'/-- `{x} = "{v}"` (`metadatafields.go`): a string. -/',
                           post=f'∃ k : GoString, globalAddr {x} ↦ k', pat='⟨%k@, H@⟩')
_R['finish'] = [f'ipersist H{x}' for x in _RERRS + list(_RKEYS)] + _R['finish']
_R['doc'] = _R['doc'].replace("the pointer error `ErrGRPCNotSupportedForLearner`.", "the pointer error `ErrGRPCNotSupportedForLearner`, the token keys, the `ErrGRPC*` errors\n`v3rpc`'s checks and interceptors return and its metadata keys.")

_P = SPECIAL['go_etcd_io.etcd.api.v3.etcdserverpb']
_P['doc'] = """Its fact (`etcdserverpbInit`, `cache/v3/Base.lean`): the sort enumerations' name maps. Its
initializer allocates and sets the translated gRPC service descriptors (`KV_ServiceDesc`, ...:
`grpc.ServiceDesc` literals), initializes its imports and runs its other variables' untranslated
initializers (the generated protobuf descriptors and enum maps): the trust-boundary axioms
`<X>_init` state the two the fact reads, `opaqueInitsOk` the others."""
for x, n in [('RangeRequest_SortOrder_name', 2), ('RangeRequest_SortTarget_name', 4)]:
    _P['custom'] = _P.get('custom', {})
    _P['custom'][x] = dict(
        doc=f'/-- `{x} = map[int32]string{{...}}` (`rpc.pb.go`): the enumeration\'s names, keys `0` to `{n}`. -/',
        post=f'∃ (mp : Loc) (M : GMap w32 GoString), globalAddr {x} ↦ mp ∗ mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ {n}⌝',
        pat='⟨%mp@, %M@, H@, #S@, %P@⟩')
_P['heavy'] = True
_P['pre'] = ['/-- A small 64-bit literal\'s value as a signed natural (the descriptors\' slice indices). -/',
             'theorem EtcdGrove.sint_nat_ofNat64 (n : Nat) (h : n < 2 ^ 63) : sint.nat (BitVec.ofNat 64 n) = n := by',
             '  simp [sint.nat, BitVec.toInt]; omega', '']
_PB_SL = ['KVm', 'KVs', 'Wm', 'Ws', 'Lm', 'Ls', 'Cm', 'Cs', 'Mm', 'Ms', 'Am', 'As']
_PB_DESCS = ['KV', 'Watch', 'Lease', 'Cluster', 'Maintenance', 'Auth']
_P['finish'] = ([f'wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %p{t} ⟨S{t}, -⟩; try wp_auto'
                 for t in _PB_SL] + ['try wp_auto'] + [f'ipersist S{t}' for t in _PB_SL] +
                [f'ipersist H{d}_ServiceDesc' for d in _PB_DESCS] +
                [f'iStructNamedSuffix H{d}_ServiceDesc "{d}"' for d in _PB_DESCS] +
                ['ipersist HRangeRequest_SortOrder_name', 'ipersist HRangeRequest_SortTarget_name'] +
                FIN_PRE[:6] + ['imodintro', 'unfold go_etcd_io.etcd.cache.v3.etcdserverpbInit go_etcd_io.etcd.cache.v3.etcdserverpbDescs go_etcd_io.etcd.cache.v3.pbDescOk go_etcd_io.etcd.cache.v3.pbDescIs', 'iframe #',
                 'isplitl []', '· ipureintro; exact PRangeRequest_SortOrder_name',
                 'isplitl []', '· ipureintro; exact PRangeRequest_SortTarget_name',
                 'repeat (first | (isplitl []; · (ipureintro; simp (config := {decide := true}) [go.arrayLiteralSize, EtcdGrove.sint_nat_ofNat64])) | (ipureintro; simp (config := {decide := true}) [go.arrayLiteralSize, EtcdGrove.sint_nat_ofNat64]))'])

_C = SPECIAL['go_etcd_io.etcd.client.v3']
_C['custom'].update({
    'defaultCallOpts': dict(
        doc='/-- `defaultCallOpts = []grpc.CallOption{defaultWaitForReady, defaultMaxCallSendMsgSize, defaultMaxCallRecvMsgSize}` (`options.go`): grpc\'s `WaitForReady(true)`, `MaxCallSendMsgSize(...)`, `MaxCallRecvMsgSize(...)`, options holding only scalars (`FailFastCallOption`, `MaxSendMsgSizeCallOption`, `MaxRecvMsgSizeCallOption`). -/',
        post='∃ (sl : GoSlice) (vs : List GoInterface), globalAddr defaultCallOpts ↦ sl ∗ sl ↦*□ vs ∗ ⌜sl.len = sl.cap ∧ ∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ [google_golang_org.grpc.StaticMethodCallOption.ty, google_golang_org.grpc.FailFastCallOption.ty, google_golang_org.grpc.MaxSendMsgSizeCallOption.ty, google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty]⌝',
        pat='⟨%sl@, %vs@, H@, #S@, %P@⟩'),
    'defaultUnaryMaxRetries': dict(doc='/-- `defaultUnaryMaxRetries uint = 100` (`options.go`). -/',
        post='∃ n : w64, globalAddr defaultUnaryMaxRetries ↦ n', pat='⟨%n@, H@⟩'),
    'defaultBackoffWaitBetween': dict(doc='/-- `defaultBackoffWaitBetween = 25 * time.Millisecond` (`options.go`). -/',
        post='∃ d : time.Duration, globalAddr defaultBackoffWaitBetween ↦ d', pat='⟨%d@, H@⟩'),
    'defaultBackoffJitterFraction': dict(doc='/-- `defaultBackoffJitterFraction = 0.10` (`options.go`): a float. -/',
        post='∃ f : w64, globalAddr defaultBackoffJitterFraction ↦ f', pat='⟨%f@, H@⟩'),
})
_C['finish'] = (['ipersist Hsnp', 'ipersist HnoPrefixEnd', 'ipersist HdefaultOptions', 'ipersist HdefaultCallOpts',
                 'ipersist HdefaultUnaryMaxRetries', 'ipersist HdefaultBackoffWaitBetween',
                 'ipersist HdefaultBackoffJitterFraction', 'ipersist HvalCtxCh', 'ipersist HzeroTime',
                 'ipersist HmaxBackoff'] + FIN_PRE[:6] +
                ['imodintro', 'unfold go_etcd_io.etcd.cache.v3.clientv3Init', 'iframe #',
                 'ipureintro', 'exact PdefaultCallOpts'])

_S = SPECIAL['go_etcd_io.etcd.server.v3.storage.schema']
_S['custom'] = {
    'AllBuckets': dict(doc='/-- `AllBuckets = []backend.Bucket{Key, Meta, ...}` (`bucket.go`): a slice. -/',
                       post='∃ sl : GoSlice, globalAddr AllBuckets ↦ sl', pat='⟨%sl@, H@⟩'),
    'ScheduledCompactKeyName': dict(doc='/-- `ScheduledCompactKeyName = []byte("scheduledCompactRev")` (`bucket.go`). -/',
        post='∃ s : GoSlice, globalAddr ScheduledCompactKeyName ↦ s ∗ s ↦*□ (go!"scheduledCompactRev" : GoString)', pat='⟨%s@, H@, #S@⟩'),
    'FinishedCompactKeyName': dict(doc='/-- `FinishedCompactKeyName = []byte("finishedCompactRev")` (`bucket.go`). -/',
        post='∃ s : GoSlice, globalAddr FinishedCompactKeyName ↦ s ∗ s ↦*□ (go!"finishedCompactRev" : GoString)', pat='⟨%s@, H@, #S@⟩'),
}
_S['doc'] = _S['doc'].replace("and the consistent index's two key names (`cindex.go`).", "the consistent index's two key names (`cindex.go`), `AllBuckets` and the compaction's two key\nnames (untranslated: the trust-boundary axioms `<X>_init`).")
_S['finish'] = (_S['finish'][:8] + ['ipersist HAllBuckets', 'ipersist HScheduledCompactKeyName', 'ipersist HFinishedCompactKeyName']
                + _S['finish'][8:])


def errVarFrom(pkg, X, msg, hd, tag):
    """Lines taking `X`'s `errorsNewVar` from `etcdserver/errors`' fact (`errorsInit`) at `hd`."""
    return [f'ihave Hei{tag} : ({pkg}.errorsInit : IProp GF) $$ []',
            f'· iapply isPkgInit_access $$ {hd}',
            f'icases Hei{tag} with ⟨-, #Hev{tag}⟩',
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
_MV_GAU = ['keysGauge', 'watchStreamGauge', 'watcherGauge', 'pendingEventsGauge', 'totalPutSizeGauge']
_MV_HIS = ['indexCompactionPauseMs', 'dbCompactionPauseMs', 'dbCompactionTotalMs']
_mv_custom = {x: _metric(x, 'counter', ['counterSpec']) for x in _MV_CNT}
_mv_custom.update({x: _metric(x, 'gauge', ['gaugeSpec']) for x in _MV_GAU})
_mv_custom['slowWatcherGauge'] = _metric('slowWatcherGauge', 'gauge', ['gaugeSpec', 'gaugeSetSpec'])
_mv_custom['dbCompactionLast'] = _metric('dbCompactionLast', 'gauge', ['gaugeSetSpec'])
_mv_custom.update({x: _metric(x, 'hist', ['histSpec']) for x in _MV_HIS})
_mv_custom['defaultCompactionBatchLimit'] = dict(
    doc='/-- `defaultCompactionBatchLimit = 1000` (`kvstore.go`). -/',
    post='globalAddr defaultCompactionBatchLimit ↦ (W64 1000 : w64)', pat='H@')
_mv_custom['defaultCompactionSleepInterval'] = dict(
    doc='/-- `defaultCompactionSleepInterval = 10 * time.Millisecond` (`kvstore.go`). -/',
    post='∃ d : w64, globalAddr defaultCompactionSleepInterval ↦ d', pat='⟨%d@, H@⟩')
_MV_ERR = {'ErrRevisionNotFound': 'RNF', 'ErrCompacted': 'CP', 'ErrFutureRev': 'FR',
           'ErrWatcherNotExist': 'WNE', 'ErrEmptyWatcherRange': 'EWR', 'ErrWatcherDuplicateID': 'WDI'}
SPECIAL['go_etcd_io.etcd.server.v3.storage.mvcc'] = dict(
    doc="""Its fact (`mvccInit`, `Base.lean`): its error variables (translated `errors.New` calls), its
metrics (`metrics.go`, untranslated: the trust-boundary axioms `<X>_init`; a counter's `Add` only
of a non-negative value), its constants, and `schema`'s two compaction key names (from `schema`'s
fact). `opaqueInitsOk` states its other untranslated initializers run.""",
    imports=['Perennial.Proof.context.NewErrorString'],
    custom=_mv_custom,
    alloc_types={'watchBatchMaxRevs': 'w64', 'ErrWatcherDuplicateID': 'GoInterface',
                 'ErrEmptyWatcherRange': 'GoInterface', 'ErrWatcherNotExist': 'GoInterface',
                 'watchResyncPeriod': 'w64', 'maxWatchersPerSync': 'w64', 'chanBufLen': 'w64',
                 'ErrFutureRev': 'GoInterface', 'ErrCompacted': 'GoInterface',
                 'ErrRevisionNotFound': 'GoInterface'},
    before={'restoreChunkKeys': [f'wp_apply _root_.Perennial.context.wp_New_errorString as %x{t} #M{t}'
                                 for t in ['RNF', 'CP', 'FR']],
            '$end': [f'wp_apply _root_.Perennial.context.wp_New_errorString as %x{t} #M{t}'
                     for t in ['WNE', 'EWR', 'WDI']]},
    finish=([f'ipersist H{x}' for x in _MV_ERR] +
            [f'ipersist H{x}' for x in list(_mv_custom)] +
            ['ipersist HchanBufLen', 'ipersist HmaxWatchersPerSync', 'ipersist HwatchResyncPeriod',
             'ipersist HwatchBatchMaxRevs',
             'ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd4',
             'icases Hsi with ⟨-, -, -, -, -, #HSK, #HFK⟩'] + FIN_PRE[:6] +
           ['imodintro', 'unfold mvccInit EtcdGrove.errorsNewVar', 'iframe #',
            'rw [show (W64 100000000 : w64) = W64 100 * W64 1000000 by rfl]', 'iexact HwatchResyncPeriod']),
)

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.txn'] = dict(
    doc="""Its fact (`txnInit`, `Base.lean`): `lease.ErrLeaseNotFound` and `etcdserver/errors.ErrKeyNotFound`
(from their packages' facts) and its counter `slowApplies` (`metrics.go`, untranslated: the
trust-boundary axiom `slowApplies_init`). `opaqueInitsOk` states its other untranslated
initializers run.""",
    custom={'slowApplies': dict(
        doc='/-- `slowApplies = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`, whose `Inc` returns. -/',
        post='∃ c : GoInterfaceOk, globalAddr slowApplies ↦ GoInterface.ok c ∗ go_etcd_io.etcd.server.v3.lease.counterSpec c',
        pat='⟨%c@, H@, #S@⟩')},
    finish=['ipersist HslowApplies',
            'ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []',
            '· iapply isPkgInit_access $$ Hd11',
            'icases Hli with ⟨#HLNF0, -⟩',
            'iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at HLNF0',
            'icases HLNF0 with ⟨%eLNF, #HLNF, -⟩'] +
           errVarFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrKeyNotFound', 'etcdserver: key not found', 'Hd10', 'KNF') +
           ['iunfold EtcdGrove.errorsNewVar at NKNF', 'icases NKNF with ⟨%xKNF, #HKNF, -⟩'] +
           FIN_PRE[:6] + ['imodintro', 'unfold txnInit', 'iframe #'],
)

_ERRLEAF_PRE = [
    'section errVarLeafOfNew',
    'variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]',
    'variable [go_gctx : GoGlobalContext]',
    'variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]',
    'variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions] [EtcdGrove.ErrorStringLeaf]',
    '',
    '/-- An `errors.New` variable (`errorsNewVar`) holds a leaf pointer error without `Is` whose',
    '`Error()` returns (`errVarLeaf`), by the premise `ErrorStringLeaf`. -/',
    'theorem EtcdGrove.errVarLeaf_of_newVar (X msg : GoString) :',
    '    EtcdGrove.errorsNewVar (GF := GF) X msg ⊢ EtcdGrove.errVarLeaf X := by',
    '  unfold EtcdGrove.errorsNewVar EtcdGrove.errVarLeaf',
    '  iintro ⟨%x, #Hx, #Hm⟩',
    '  iexists _',
    '  iframe Hx',
    '  isplitr',
    '  · ipureintro; exact EtcdGrove.errorString_leaf x',
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

SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.apply'] = dict(
    doc="""Its fact (`applyInit`, `Base.lean`): its gauge vector `alarms` (`metrics.go`, untranslated:
the trust-boundary axiom `alarms_init`), and the error variables it returns or compares with
(`applyErrVars`), from their packages' facts (`etcdserver/errors`', `lease`'s, `mvcc`'s), leaf
errors by the premise `EtcdGrove.ErrorStringLeaf`.""",
    custom={'alarms': dict(
        doc='/-- `alarms = prometheus.NewGaugeVec(...)` (`metrics.go`): a `*GaugeVec`. -/',
        post='∃ gv : Loc, globalAddr alarms ↦ gv', pat='⟨%gv@, H@⟩')},
    pre=_ERRLEAF_PRE,
    finish=(['ipersist Halarms'] +
            errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrCorrupt', 'etcdserver: corrupt cluster', 'Hd19', 'COR') +
            errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrNoSpace', 'etcdserver: no space', 'Hd19', 'NSP') +
            errLeafFrom('go_etcd_io.etcd.server.v3.etcdserver.errors', 'ErrKeyNotFound', 'etcdserver: key not found', 'Hd19', 'KNF') +
            ['ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd10',
             'icases Hli with ⟨#HLNF0, -⟩',
             'ihave #LLNF : (EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound : IProp GF) $$ []',
             '· unfold EtcdGrove.errVarLeaf EtcdGrove.errLeaf EtcdGrove.errMsgOk',
             '  iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at HLNF0',
             '  iexact HLNF0',
             'ihave Hmi : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd18',
             'icases Hmi with ⟨' + '-, ' * 30 + '#NMC, #NMF⟩',
             'ihave #LMC := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NMC',
             'ihave #LMF := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NMF'] +
            FIN_PRE[:6] + ['imodintro', 'unfold applyInit applyErrVars', 'iframe #']),
)

_SRV_ERRS = [('ErrTooManyRequests', 'etcdserver: too many requests', 'TMR'),
             ('ErrRequestTooLarge', 'etcdserver: request is too large', 'RTL'),
             ('ErrStopped', 'etcdserver: server stopped', 'STP'),
             ('ErrCanceled', 'etcdserver: request cancelled', 'CAN'),
             ('ErrTimeout', 'etcdserver: request timed out', 'TMO'),
             ('ErrTimeoutDueToLeaderFail', 'etcdserver: request timed out, possibly due to previous leader failure', 'TLF'),
             ('ErrTimeoutDueToConnectionLost', 'etcdserver: request timed out, possibly due to connection lost', 'TCL')]
_srv_custom = {x: _metric(x, 'gauge', ['gaugeSetSpec']) for x in ['hasLeader', 'isLeader', 'proposalsCommitted', 'proposalsApplied']}
_srv_custom.update({x: _metric(x, 'counter', ['go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec'])
                    for x in ['leaderChanges', 'heartbeatSendFailures', 'proposalsFailed']})
_srv_custom['proposalsPending'] = _metric('proposalsPending', 'gauge', ['go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec'])
for _gv in ['serverFeatureEnabled', 'serverID']:
    # the construction's gauge vectors (unit N4, 2026-10-17: `NewServer` reads them)
    _srv_custom[_gv] = dict(
        doc=f'/-- `{_gv} = prometheus.NewGaugeVec(...)` (`metrics.go`): a `*GaugeVec`. -/',
        post=f'∃ gv : Loc, globalAddr {_gv} ↦ gv', pat='⟨%gv@, H@⟩')
_srv_custom['requestDurationSec'] = dict(
    doc='/-- `requestDurationSec = prometheus.NewHistogramVec(...)` (`metrics.go`): a `*HistogramVec`. -/',
    post='∃ hv : Loc, globalAddr requestDurationSec ↦ hv', pat='⟨%hv@, H@⟩')
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver'] = dict(
    doc="""Its fact (`srvInit`, `BaseApply.lean`): its metrics (`metrics.go`, untranslated: the
trust-boundary axioms `<X>_init`), and from its imports' facts `traceutil.Tracer`, `schema`'s
`AllBuckets` and the error variables of `etcdserver/errors`, `auth` and raft it returns (leaf
errors by the premise `EtcdGrove.ErrorStringLeaf`). Its precondition has the read package's
registration rights (`EtcdGrove.read.readRegPerm`, decision D16), which it passes on to the read
package's initializer.""",
    custom=_srv_custom,
    finish=([f'ipersist H{x}' for x in _srv_custom] +
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
             'ipureintro', 'exact fun x => EtcdGrove.errorString_leaf x']),
)

_V_ERRS = ['ErrGRPCEmptyKey', 'ErrGRPCInvalidSortOption', 'ErrGRPCValueProvided', 'ErrGRPCLeaseProvided',
           'ErrGRPCTooManyOps', 'ErrGRPCDuplicateKey', 'ErrGRPCKeyNotFound', 'ErrGRPCNoSpace',
           'ErrGRPCNotCapable', 'ErrGRPCInvalidClientAPIVersion', 'ErrGRPCNoLeader']
SPECIAL['go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc'] = dict(
    doc="""Its fact (`v3rpcInit`, `Base.lean`): its error map `toGRPCErrorMap` and counter vector
`clientRequests` (untranslated: the trust-boundary axioms `<X>_init`), `metricsServerLock` (an
unlocked mutex guarding `metricsServerCached`, `nil`: `metricsVars`), `rpctypes`' errors and
metadata keys and `etcdserverpb`'s sort-name maps and six `ServiceDesc`s (`svcDescsOk`, from their
facts), and `context.Canceled` a
pointer error (from the read package's premise `EtcdGrove.ContextReadErrs`: Perennial's `context`
fact lacks it). Its precondition has the read package's registration rights
(`EtcdGrove.read.readRegPerm`, decision D16), which it passes on to `etcdserver`'s initializer.""",
    alloc_types={'progressReportIntervalMu': '_root_.Perennial.sync.RWMutex',
                 'progressReportInterval': 'w64', 'metricsServerCached': 'Loc',
                 'metricsServerLock': '_root_.Perennial.sync.Mutex'},
    custom={
        'toGRPCErrorMap': dict(
            doc='/-- `toGRPCErrorMap = map[error]error{...}` (`util.go`): a map whose values are `rpctypes.ErrGRPC*` errors (and `ErrTooManyRequests`, `ErrMemberNotEnoughStarted`), non-nil. -/',
            post='∃ (mp : Loc) (M : GMap GoInterface GoInterface), globalAddr toGRPCErrorMap ↦ mp ∗ mp ↦$□ M ∗ ⌜∀ k v, M !! k = some v → v ≠ GoInterface.nil⌝',
            pat='⟨%mp@, %M@, H@, #S@, %P@⟩'),
        'clientRequests': dict(
            doc='/-- `clientRequests = prometheus.NewCounterVec(...)` (`metrics.go`): a `*CounterVec`. -/',
            post='∃ cv : Loc, globalAddr clientRequests ↦ cv', pat='⟨%cv@, H@⟩'),
    },
    finish=(['ipersist HtoGRPCErrorMap', 'ipersist HclientRequests',
             'ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd22',
             'icases Hri with ⟨-, -, -, -, -, -, -, -, ⟨%eNSL, #HNSL, -⟩, -, -, ' +
             ', '.join(f'#V{i}' for i in range(len(_V_ERRS) + 3)) + '⟩',
             'ihave Hpi : (go_etcd_io.etcd.cache.v3.etcdserverpbInit : IProp GF) $$ []',
             '· iapply isPkgInit_access $$ Hd2',
             'icases Hpi with ⟨#HSO, #HST, #HDescs⟩',
             'ihave ⟨#HCL, -⟩ := EtcdGrove.ContextReadErrs.errs $$ Hd1',
             'ihave #HCP : (∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok e ∗',
             '    ⌜_root_.Perennial.errors.IsPointerError e⌝ : IProp GF) $$ []',
             '· iunfold EtcdGrove.errVarLeaf at HCL', '  icases HCL with ⟨%e, #He, %Hl, -⟩',
             '  iexists e', '  iframe He', '  ipureintro; exact Hl.1',
             '-- `getServerMetrics`\' lock and what it guards (`metricsServerCached`, `nil`)',
             'imod sync.init_Mutex EtcdGrove.v3rpc.metricsP ⊤ EtcdGrove.v3rpc.metricsMu $$ HmetricsServerLock [HmetricsServerCached] with #HMV',
             '· inext', '  unfold EtcdGrove.v3rpc.metricsP', '  iexists _', '  iframe HmetricsServerCached',
             '  ileft', '  ipureintro; rfl',
             '-- the six `ServiceDesc`s, from `etcdserverpb`\'s fact',
             'icases HDescs with ⟨#HK, ⟨%wm, %ws, #HW, %HWp⟩, #HL, #HC, #HA, #HM⟩',
             'obtain ⟨rfl, HWp, -⟩ := HWp',
             'ihave #HSD : (EtcdGrove.v3rpc.svcDescsOk : IProp GF) $$ []',
             '· unfold EtcdGrove.v3rpc.svcDescsOk EtcdGrove.v3rpc.descOk EtcdGrove.descNames EtcdGrove.v3rpc.handlerTy EtcdGrove.v3rpc.kvDescMethods',
            
            
             '  iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HL',
             '  iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HC',
             '  iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HA',
             '  iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HM',
             '  iframe HK HL HC HA HM',
             '  iexists ws',
             '  iframe HW',
             '  ipureintro; exact HWp'] +
            FIN_PRE[:6] +
            ['imodintro', 'unfold v3rpcInit grpcErrMap checkErrVars sortNameMaps ctxCanceledPtr interceptorVars errVarSet EtcdGrove.v3rpc.metricsVars',
             'iframe #', 'ipureintro', 'exact PtoGRPCErrorMap']),
)


# Item 8 (2026-10-17): the read package, its `init()`'s `MustRegister` given the registration
# rights (`EtcdGrove.read.readRegPerm`, `PRE_RES`; decision D16).
_RD = 'go_etcd_io.etcd.server.v3.etcdserver.read'
_RD_CTX_PRE = [
    'section ctxFacts',
    'variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]',
    'variable [go_gctx : GoGlobalContext]',
    'variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]',
    'variable [sem : go.Semantics]',
    '',
    '/-- **The trust boundary: `context.Canceled` and `context.DeadlineExceeded` as Go defines them**',
    '(a premise, stated locally; item 8, 2026-10-17): `Canceled = errors.New("context canceled")`, a',
    'leaf pointer error without `Is` whose `Error()` returns, and `DeadlineExceeded =',
    'deadlineExceededError{}`, a leaf non-pointer error (an empty struct: comparable, a safe map',
    'key) without `Is` whose `Error()` returns (`context.go`: its methods are `Error`, `Timeout` and',
    '`Temporary`). Perennial\'s `context.initialize\'` stores exactly these values, but its fact',
    '(`isInit`) keeps only that they are typed errors, and the method sets are uninterpreted: the',
    'general fix is a Perennial change (`notes/decisions.md`, "Item 8: context\'s facts"). A',
    'premise rather than an axiom: `isPkgInit context` is not sealed (any proof holding the',
    'variables\' cells could make it), so as an axiom the entailment could be used to prove `False`.',
    '(`v3rpc`\'s `context.Canceled` fact, until then the premise `ContextCanceledPtr`, follows.) -/',
    'class EtcdGrove.ContextReadErrs : Prop where',
    '  errs : isPkgInit (PROP := IProp GF) pkg_id.context ⊢',
    '    EtcdGrove.errVarLeaf _root_.Perennial.context.Canceled ∗',
    '      go_etcd_io.etcd.server.v3.etcdserver.read.ctxDeadlineLeaf',
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
axioms `EtcdGrove.prometheus.wp_counterOptsLit` and `NewCounter.wp_proof`), `readIndexRetryTime`,
the error variables it returns or compares with, from their packages' facts (`etcdserver/errors`'
and raft's, leaf errors by the premise `EtcdGrove.ErrorStringLeaf`), and `context`'s
(`EtcdGrove.ContextReadErrs`, a premise: Perennial's `context` fact lacks them). Its translated
`init()` registers the two counters (`prometheus.MustRegister`, the trust-boundary axiom
`MustRegister.wp_proof`), which takes the right to register each name: the precondition
`EtcdGrove.read.readRegPerm` (decision D16).""",
    imports=['Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Metrics',
             'Proof.github_com.prometheus.client_golang.prometheus.NewCounter',
             'Proof.github_com.prometheus.client_golang.prometheus.MustRegister',
             'Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init'],
    pre=_RD_CTX_PRE,
    vars=['[EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]', '[EtcdGrove.ErrorStringLeaf]'],
    alloc_types={'slowReadIndex': 'GoInterface', 'readIndexFailed': 'GoInterface',
                 'readIndexRetryTime': '_root_.Perennial.time.Duration'},
    before={'$end': [
        'wp_apply EtcdGrove.prometheus.wp_counterOptsLit as %o1 %Ho1', 'try wp_auto',
        'wp_apply EtcdGrove.prometheus.NewCounter.wp_proof _ _ _ _ _ Ho1 (by decide) as %c1 ⟨#C1, %N1⟩',
        'try wp_auto',
        'wp_apply EtcdGrove.prometheus.wp_counterOptsLit as %o2 %Ho2', 'try wp_auto',
        'wp_apply EtcdGrove.prometheus.NewCounter.wp_proof _ _ _ _ _ Ho2 (by decide) as %c2 ⟨#C2, %N2⟩',
        'try wp_auto',
        'iunfold EtcdGrove.read.readRegPerm at HR',
        'icases HR with ⟨HR1, HR2⟩',
        'wp_apply wp_slice_literal (l := [GoInterface.ok c1])', 'isplitr', '· ipureintro; rfl',
        'iintro %s1 ⟨S1, -⟩', 'try wp_auto',
        'wp_apply EtcdGrove.prometheus.MustRegister.wp_proof _ _ _ _ N1 $$ [S1 HR1] as S1',
        '· iframe S1 HR1',
        'wp_apply wp_slice_literal (l := [GoInterface.ok c2])', 'isplitr', '· ipureintro; rfl',
        'iintro %s2 ⟨S2, -⟩', 'try wp_auto',
        'wp_apply EtcdGrove.prometheus.MustRegister.wp_proof _ _ _ _ N2 $$ [S2 HR2] as S2',
        '· iframe S2 HR2']},
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
             'ihave ⟨#LCC, #LDL⟩ := EtcdGrove.ContextReadErrs.errs $$ {Hd:context}'] +
            FIN_PRE[:6] +
            ['imodintro', 'unfold readInit', 'iframe #']),
)

RAFT_INIT = {'go_etcd_io.raft.v3', 'go_etcd_io.raft.v3.quorum', 'go_etcd_io.raft.v3.tracker',
             'go_etcd_io.raft.v3.confchange', 'go_etcd_io.raft.v3.raftpb',
             'google_golang_org.protobuf.proto', 'os', 'strconv'}

def plain(ns):
    return ns.replace('«', '').replace('»', '')

def dirof(ns):
    return plain(ns).replace('.', '/')

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
    if d['perennial'] and q not in ('math.rand', 'reflect'):
        return 'Perennial.Proof.' + plain(q) + '.Link'
    if q == 'go_etcd_io.bbolt.internal.common':
        return 'Proof.go_etcd_io.bbolt.internal.common.Initialize'
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


def pre_res(p):
    """The package below `p` (or `p`) whose initializer needs a resource (`PRE_RES`), if any
    (at most one; any number of `p`'s imports may lead there: the `_res` form spends it once)."""
    rs = [q for q in sorted(closure(p)) if q in PRE_RES]
    assert len(rs) <= 1, (p, rs)
    return rs[0] if rs else None


def external(q):
    """`q`'s `wp_initialize'` is not generated here (Perennial's, raft's, the B-tree's)."""
    return (q in RAFT_INIT or q == 'k8s_io.utils.third_party.forked.golang.btree' or
            (inv[q]['perennial'] and q not in PERENNIAL_HERE))


def ext_ctor(q):
    return plain(q).replace('.', '_')


def lb_term(q, hin):
    """A proof of `∀ σ0, {{ ownInitLb g σ0 }} q.initialize' #() {{ ... }}` (`hin`: its
    `GetIsPkgInitProp`)."""
    assert q not in ASSUMED, q
    if external(q):
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
    """The initializer's statements in execution order: ('import', q) / ('opaque', X)."""
    d = inv[p]
    t = open(d['file']).read()
    i = t.find("noncomputable def initialize'")
    j = t.find("\n\n", i)
    body = t[i:j]
    items = []
    for m in re.finditer(r"\(Val _root_\.Perennial\.(\S+)\.initialize'\)|\(Val ([^\s()]+)\.init\)|go\.GlobalAlloc (\S+) |GlobalVarAddr (\S+)\)", body):
        if m.group(1):
            items.append(('import', m.group(1)))
        elif m.group(2):
            items.append(('opaque', m.group(2)))
        elif m.group(3):
            items.append(('alloc', m.group(3)))
        else:
            items.append(('store', m.group(4)))
    items.reverse()
    return items

def gen(p, cfg=None):
    cfg = cfg or {}
    newvars = cfg.get('newvars', {})
    custom = cfg.get('custom', {})
    d = inv[p]
    k = plain(p)
    imods = inst.get(k) or inst.get(p)
    inst_mod = 'Proof.' + imods[0][0].replace('/', '.')
    cl = closure(p)
    needs_ctx = 'context' in cl
    needs_raft = 'go_etcd_io.raft.v3' in cl
    pk = pkginfo_imports(p)
    items = exec_order(p)
    opq = [x for (kind, x) in items if kind == 'opaque' and x not in newvars and x not in custom]
    imps = [x for (kind, x) in items if kind == 'import']
    assert sorted(imps) == sorted(pk), (p, imps, pk)
    mods = [inst_mod] + sorted({ASSUMED[q][0] if q in ASSUMED else init_module(q) for q in imps}) + cfg.get('imports', [])
    if newvars: mods.append('Proof.errors.NewVar')
    mods.append('Proof.runtime.PkgInitExt')
    lines = []
    A = lines.append
    A('/-')
    A(f'Package initialization of `{p}`')
    A('(item 8, 2026-10-17): its `wp_initialize\'`.')
    A('')
    if 'doc' in cfg:
        A(cfg['doc'])
    elif opq:
        A('Its fact is `True`. Its initializer initializes its imports and runs the untranslated')
        A('initializers of its variables (`X.init`, axioms of the translation), which the')
        A('trust-boundary axiom `opaqueInitsOk` says run without panicking.')
    else:
        A('Its fact is `True`. Its initializer initializes its imports (it has no initialized')
        A('variable).')
    A('-/')
    A('module')
    A('')
    for m in mods:
        A(f'public import {m}')
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
    if opq or newvars or custom:
        A('section opaqueInits')
        A(f'namespace {p}')
        A('variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]')
        A('variable [go_gctx : GoGlobalContext]')
        A('variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]')
        A('variable [sem : go.Semantics]')
        A('')
        if opq:
            A(f'/-- **The trust boundary: `{p}`\'s untranslated variable initializers run.**')
            A('Goose translates them names-only, so each `X.init` is an axiom of the translation; Go')
            A('runs them at program start, and etcd starts, so each returns without panicking.')
            A('Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/')
            A('axiom opaqueInitsOk :')
            A('    ∀ v ∈ ([' + ',\n        '.join(f'{x}.init' for x in opq) + '] : List val),')
            A('    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}')
            A('')
        if newvars:
            A(f'/-- **The trust boundary: `{p}`\'s variables initialized by `errors.New`.** Each')
            A('listed `X.init` (untranslated) runs Go\'s `var X = errors.New(msg)`, as its Go source has')
            A('it. -/')
            A('axiom errorsNewVarsInit :')
            A('    ∀ (init : val) (X msg : GoString), (init, X, msg) ∈ ([' + ',\n        '.join(f'({x}.init, {x}, go!{json.dumps(m)})' for x, m in newvars.items()) + '] : List (val × GoString × GoString)) →')
            A('    EtcdGrove.errorsNewVarInit (GF := GF) init X msg')
            A('')
        for x, c in custom.items():
            A(c['doc'])
            A(f'axiom {x}_init :')
            A(f'    {{{{ (True : IProp GF) }}}} (App (Val {x}.init) (Val #()))')
            A(f'    {{{{ RET #(); {c["post"]} }}}}')
            A('')
        A(f'end {p}')
        A('end opaqueInits')
        A('')
    for l in cfg.get('pre', []):
        A(l)
    A('section init')
    A('variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]')
    A('variable [go_gctx : GoGlobalContext]')
    A('variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]')
    A('variable [sem : go.Semantics]')
    A(f'variable [package_sem : _root_.Perennial.{p}.Assumptions]')
    _SP = SPECIAL
    vs = list(cfg.get('vars', []))
    for q in sorted(cl):
        for v in _SP.get(q, {}).get('vars', []):
            if v not in vs: vs.append(v)
    for v in vs:
        A(f'variable {v}')
    if needs_ctx:
        A('variable [_root_.Perennial.context.ErrorStringIsError]')
        A('  [_root_.Perennial.context.DeadlineExceededIsError]')
    if needs_raft:
        A('variable [_root_.Perennial.log.NewModel]')
    A('')
    A(f'namespace {p}')
    A('')
    if len(items) > 50 or cfg.get('heavy'):
        A('set_option maxHeartbeats 8000000 in')
    res = pre_res(p)
    assert not hyps(p), p
    form = 'self' if res == p else ('res' if res else 'lb')
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
        rres = f'pkg_id.{res} ({PRE_RES[res]} (GF := GF))'
        A('theorem wp_initialize\'_res (get_is_pkg_init : GoString → IProp GF)')
        A(f'    (Hinit : GetIsPkgInitProp {st} get_is_pkg_init) :')
        A(f'    {{{{ EtcdGrove.ownInitRes get_is_pkg_init {rres} }}}}')
        A(f'      (App (Val initialize\') (Val #()))')
        A(f'    {{{{ RET #(); EtcdGrove.ownInitRes get_is_pkg_init {rres} ∗')
        A(f'        isPkgInit (PROP := IProp GF) {st} }}}} := by')
        A('  wp_start as Hown')
        if form == 'self':
            A('  iapply EtcdGrove.wp_package_init_res_self (heq := Hinit.1) $$ [Hown] HΦ')
            A('  iframe Hown')
            A('  iintro ⟨Hown, HR⟩')
        else:
            A('  iapply EtcdGrove.wp_package_init_res (heq := Hinit.1) $$ [Hown] HΦ')
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
        if kind == 'opaque' and x in before:
            for l in before.pop(x):
                A('  ' + hdsub(l))
        if kind == 'import':
            idx = pk.index(x) + 1
            hin = f'Hinit{".2" * idx}.1'
            if form == 'self':
                A(f'  wp_apply {init_call(x)} _ {hin} $$ Hown as ⟨Hown, #Hd{idx}⟩')
            elif form == 'lb':
                A(f'  wp_apply {lb_term(x, hin)} _ $$ Hown as ⟨Hown, #Hd{idx}⟩')
            elif res in closure(x):
                A(f'  wp_apply _root_.Perennial.{x}.wp_initialize\'_res _ {hin} $$ Hown as ⟨Hown, #Hd{idx}⟩')
            else:
                A(f'  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ {lb_term(x, hin)})')
                A(f'    $$ Hown as ⟨Hown, #Hd{idx}⟩')
        elif kind == 'opaque' and x in newvars:
            A(f'  wp_apply (errorsNewVarsInit {x}.init {x} go!{json.dumps(newvars[x])} (by mem_tac))\n    as ⟨%x{x}, H{x}, #M{x}⟩')
        elif kind == 'opaque' and x in custom:
            A(f'  wp_apply {x}_init as {custom[x]["pat"].replace("@", x)}')
        elif kind == 'opaque':
            A(f'  wp_apply (opaqueInitsOk {x}.init (by mem_tac))')
        elif kind == 'alloc':
            A(f'  wp_apply wp_GlobalAlloc (V := {cfg.get("alloc_types", {}).get(x, "TODO")}) {x} _ as H{x}')
        else:
            A(f'  -- translated initializer of {x}')
    for l in before.pop('$end', []):
        A('  ' + l)
    assert not before, before
    for l in cfg.get('finish', ['iframe Hown', 'is_pkg_init_finish']):
        A('  ' + hdsub(l))
    A('')
    if form == 'lb':
        A('/-- Perennial\'s form, from `wp_initialize\'_lb`. -/')
    else:
        A('/-- Perennial\'s form with the resource (decision D16), from `wp_initialize\'_res`. -/')
    A(f'theorem wp_initialize\' (get_is_pkg_init : GoString → IProp GF)')
    A(f'    (Hinit : GetIsPkgInitProp {st} get_is_pkg_init) :')
    if form == 'lb':
        A('    {{ ownInitializing get_is_pkg_init }}')
    else:
        A(f'    {{{{ ownInitializing get_is_pkg_init ∗ {PRE_RES[res]} (GF := GF) }}}}')
    A(f'      (App (Val initialize\') (Val #()))')
    A('    {{ RET #(); ownInitializing get_is_pkg_init ∗')
    A(f'        isPkgInit (PROP := IProp GF) {st} }}}} :=')
    if form == 'lb':
        A('  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize\'_lb get_is_pkg_init Hinit)')
    else:
        A('  EtcdGrove.wp_init_of_res _ _ _ _ _ (wp_initialize\'_res get_is_pkg_init Hinit)')
    A('')
    A('')
    A(f'end {p}')
    A('')
    A('end init')
    A('')
    A('end Perennial')
    path = f'Proof/{dirof(p)}/Init.lean'
    if p == 'go_etcd_io.bbolt.internal.common':
        path = f'Proof/{dirof(p)}/Initialize.lean'
    return path, '\n'.join(lines) + '\n'



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
    if f.startswith('.lake/packages/perennial/'):
        f = f[len('.lake/packages/perennial/'):]
    return f[:-len('.lean')].replace('/', '.')


EXT_DOC = """/-
The package initializers whose `wp_initialize'` is not generated here (Perennial's, raft's, the
B-tree's), and the trust-boundary axiom that gives their `_lb` forms (decision D19e). Generated by
`etc/gen-init.py`; do not edit.

**The trust boundary: a Goose-translated package initializer only initializes more.**
`initLb_of_spec`: if the initializer `init` of the package `p`, one of the `ExternalInit` list,
meets Perennial's spec (`{{ ownInitializing g }} init #() {{ ownInitializing g ∗ isPkgInit p }}`),
then it also keeps every package initialized before initialized (`ownInitLb g σ0`, for every
`σ0`). True of Go and of the model: the package-state map changes only by the instructions
`PackageInitStart`/`PackageInitFinish`, which a Goose translation emits only in `package.init`
(`Golang/Defn/Pkg.lean`): `Start q` after `PackageInitCheck q` found `q` not initialized, `Finish q`
setting `q` initialized; initialization is sequential (`ownInitializing` holds the map's half), so
no initialized entry is ever reset. The premise gives the rest (the initializer runs and gives
`isPkgInit p`). Perennial's theorems return an arbitrary map, so this is not provable here from
them; this repository's initializers prove their `_lb` forms (`etc/gen-init.py`). The general fix
is Perennial's (`notes/decisions.md`, D19e). It is stated of the listed initializers only (an
arbitrary expression could reset an entry with a raw `PackageInitStart`), so it is satisfiable:
each conclusion holds in every model where the premise does (the map only grows along any run of
these expressions).
-/"""


def gen_ext():
    exts = sorted({x for p in packages() for x in inv[p]['imports'] if external(x)})
    mods = sorted({code_module(q) for q in exts})
    L = [EXT_DOC, 'module', '', 'public import Proof.runtime.PkgInit']
    L += [f'public import {m}' for m in mods]
    L += ['', '@[expose] public section', '', 'set_option linter.unusedSectionVars false', '',
          'noncomputable section', '', 'namespace Perennial', 'namespace EtcdGrove', '',
          'open Iris Iris.BI Iris.ProgramLogic Iris.Std', '',
          '/-- The initializers of the packages whose `wp_initialize\'` is not generated here. -/',
          'inductive ExternalInit [FfiSyntax] [GoGlobalContext] : GoString → val → Prop where']
    for q in exts:
        L.append(f'  | {ext_ctor(q)} : ExternalInit pkg_id.{q} _root_.Perennial.{q}.initialize\'')
    L += ['',
          'section ax',
          'variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]',
          'variable [go_gctx : GoGlobalContext]',
          'variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]',
          'variable [sem : go.Semantics]',
          '',
          '/-- **The trust boundary: a listed initializer keeps the initialized packages** (see the',
          'file header). -/',
          'axiom initLb_of_spec (p : GoString) (init : val) (hext : ExternalInit p init)',
          '    [IsPkgInit (IProp GF) p] [GetIsPkgInitWf (IProp GF) p]',
          '    (Hstd : ∀ (get_is_pkg_init : GoString → IProp GF),',
          '      GetIsPkgInitProp p get_is_pkg_init →',
          '      {{ ownInitializing get_is_pkg_init }} (App (Val init) (Val #()))',
          '      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) p }}) :',
          '    ∀ (get_is_pkg_init : GoString → IProp GF), GetIsPkgInitProp p get_is_pkg_init →',
          '    ∀ σ0, {{ ownInitLb get_is_pkg_init σ0 }} (App (Val init) (Val #()))',
          '      {{ RET #(); ownInitLb get_is_pkg_init σ0 ∗ isPkgInit (PROP := IProp GF) p }}',
          '',
          'end ax',
          '',
          'end EtcdGrove',
          'end Perennial']
    return 'Proof/runtime/PkgInitExt.lean', '\n'.join(L) + '\n'


def main(argv):
    check = '--check' in argv
    pkgs = [a for a in argv if not a.startswith('--')] or packages()
    bad = []
    outs = [gen(p, SPECIAL.get(p)) for p in pkgs]
    if not [a for a in argv if not a.startswith('--')]:
        outs.append(gen_ext())
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
