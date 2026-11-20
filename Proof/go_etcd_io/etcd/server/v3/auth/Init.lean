/-
Package initialization of `go_etcd_io.etcd.server.v3.auth`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`authInit`, `Base.lean`): its error variables `ErrUserEmpty`, `ErrUserNotFound`,
`ErrPermissionDenied`, `ErrAuthOldRevision`, `ErrInvalidAuthToken`, and the admin side's eleven
(the auth plan's S4, 2026-10-24: `ErrRootUserNotExist`, ..., `ErrInvalidAuthMgmt`), and S5's two
(`ErrAuthFailed`, `ErrAuthNotEnabled`), and E2g's `ErrInvalidAuthOpts` (translated
`errors.New` calls: leaf pointer errors without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose
`Error()` returns), and `rpctypes`' token keys (from `rpctypes`' fact). (prove-initmisc,
2026-11-20) Its other variables' initializers are translated too: `currentAuthRevision`
(`prometheus.NewGaugeFunc`, over its spec), `knownOptions` (a map literal), `DefaultTTL`, `_` (`var _
AuthStore = (*authStore)(nil)`), `rootPerm` (an `authpb.Permission` literal) and the JWT errors
(until then the trust-boundary axiom `opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Init
public import Proof.go_uber_org.zap.Init
public import Proof.golang_org.x.crypto.bcrypt.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.errors.NewVar
public import Proof.errors.NewVarCell
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.sync.RWMutexGuard

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
namespace go_etcd_io.etcd.server.v3.auth
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.auth`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.server.v3.auth
end opaqueInits

end Perennial
