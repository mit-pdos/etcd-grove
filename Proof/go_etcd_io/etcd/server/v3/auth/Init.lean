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
public import Perennial.Proof.crypto.rand.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.big.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.base64.Init
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
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.runtime.PkgInitRes

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

namespace go_etcd_io.etcd.server.v3.auth

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"auth" go!"revision"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := []

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights are its
initializer's resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s
precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys)]

end go_etcd_io.etcd.server.v3.auth

end Perennial
