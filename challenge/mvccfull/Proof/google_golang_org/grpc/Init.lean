/-
Package initialization of `google_golang_org.grpc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`grpcInit`, `cache/v3/Base.lean`): `EnableTracing` holds `false` for good. Its
initializer initializes its imports, runs the untranslated initializers of its variables (`X.init`,
axioms of the translation), which the trust-boundary axiom `opaqueInitsOk` says run without
panicking, but the first, `DefaultBackoffConfig.init`, whose trust-boundary axiom
`DefaultBackoffConfig_init` also gives `EnableTracing`'s cell, holding `false`: Go allocates every
package variable, zero-valued, before the first initializer runs, and `EnableTracing` (`var
EnableTracing bool`, `trace.go:33` at v1.84.0) has no initializer of its own, so the names-only
translation has no step that allocates it and the fact rides on the first initializer. Its
untranslated `init` functions the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Proof.google_golang_org.grpc.metadata.Init
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace google_golang_org.grpc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.grpc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([noOpRegisterHealthListenerFn.init,
        unaryStreamDesc.init,
        ErrClientConnClosing.init,
        errConnDrain.init,
        errConnClosing.init,
        errConnIdling.init,
        invalidDefaultServiceConfigErrPrefix.init,
        PickFirstBalancerName.init,
        errNoTransportSecurity.init,
        errTransportCredsAndBundle.init,
        errNoTransportCredsInBundle.init,
        errTransportCredentialsMissing.init,
        disconnectionsMetric.init,
        connectionAttemptsSucceededMetric.init,
        connectionAttemptsFailedMetric.init,
        openConnectionsMetric.init,
        «_».init,
        ErrClientConnTimeout.init,
        «_».init,
        «_».init,
        errContextCanceled.init,
        errContextDeadline.init,
        statusOK.init,
        logger.init,
        defaultServerOptions.init,
        ErrServerStopped.init,
        «_».init,
        errDuplicatedName.init,
        errEmptyServiceNonEmptyMethod.init,
        metadataFromOutgoingContextRaw.init,
        emptyMethodConfig.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `google_golang_org.grpc`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2», init.«3», init.«4», init.«5»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `DefaultBackoffConfig = BackoffConfig{MaxDelay: 120 * time.Second}` (`backoff.go`) runs without panicking, and `EnableTracing`'s cell holds `false` after it: Go allocates every package variable, zero-valued, before the first initializer runs, and `EnableTracing` (`var EnableTracing bool`, `trace.go:33` at grpc v1.84.0) has no initializer of its own, so its allocation is attributed to the package's first initializer (grpc's translation is names-only: its `initialize'` has no `GlobalAlloc`). No translated code writes `EnableTracing`; a program that writes it (etcd's `embed` at log level debug, grpc-proxy `--debug`) gets no proof: it would need the cell, which `finish` makes persistent. -/
axiom DefaultBackoffConfig_init :
    {{ (True : IProp GF) }} (App (Val DefaultBackoffConfig.init) (Val #()))
    {{ RET #(); globalAddr EnableTracing ↦ false }}

end google_golang_org.grpc
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.grpc.Assumptions]

namespace google_golang_org.grpc

end google_golang_org.grpc

end init

end Perennial
