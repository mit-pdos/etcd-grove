/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.schema`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`schemaInit`, `etcdserver/Base.lean`): the `Meta`, `Key`, `Auth`, `AuthUsers` and
`AuthRoles` buckets, as `bucket.go` makes them, the consistent index's two key names (`cindex.go`),
the auth bucket's two key names and the auth backend's `authEnabled`/`authDisabled` values
(`auth.go`; the auth plan's S1, 2026-10-23), and the lessor's `Lease` bucket (leases T3,
2026-10-25). Its initializer allocates and sets those translated variables (with the buckets'
names), initializes its imports and runs its other variables' initializers, all translated
(prove-initleft, 2026-11-21: `schemaChanges`, a map literal keyed by `version`'s versions, and the
interface assertions; until then the trust-boundary axiom `opaqueInitsOk`), and its untranslated
`init` function (`bucket.go`), which the trust-boundary axiom `initFuncsOk` says returns.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.encoding.binary.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.leasepb.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.github_com.Masterminds.semver.v3.MapKey
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

section opaqueInits
namespace go_etcd_io.etcd.server.v3.storage.schema
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.schema`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.server.v3.storage.schema
end opaqueInits

namespace go_etcd_io.etcd.server.v3.storage.schema

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights are its
initializer's resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s
precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys)]

end go_etcd_io.etcd.server.v3.storage.schema

end Perennial
