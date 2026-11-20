/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.apply`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`applyInit`, `Base.lean`): its gauge vector `alarms` with its label names
(`metrics.go`, translated, over prometheus's `NewGaugeVec` spec; until 2026-11-19 the
trust-boundary axiom `alarms_init`), and the error variables it returns or compares with
(`applyErrVars`), from their packages' facts (`etcdserver/errors`', `lease`'s, `mvcc`'s), leaf
errors by `EtcdGrove.ErrorStringLeaf`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.membershippb.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.pbutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.wait.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.cindex.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init

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
namespace go_etcd_io.etcd.server.v3.etcdserver.apply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.apply`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.server.v3.etcdserver.apply
end opaqueInits

section errVarLeafOfNew
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions]

/-- An `errors.New` variable (`errorsNewVar`) holds a leaf pointer error without `Is` whose
`Error()` returns (`errVarLeaf`), by `ErrorStringLeaf`. -/
theorem EtcdGrove.errVarLeaf_of_newVar (X msg : GoString) :
    EtcdGrove.errorsNewVar (GF := GF) X msg ⊢ EtcdGrove.errVarLeaf X := by
  unfold EtcdGrove.errorsNewVar EtcdGrove.errVarLeaf
  iintro ⟨%x, #Hx, #Hm⟩
  iexists _
  iframe Hx
  isplitr
  · ipureintro; first | exact EtcdGrove.errorString_errLeaf x | exact EtcdGrove.errorString_leaf x
  unfold EtcdGrove.errMsgOk
  iapply EtcdGrove.errorMsg_triple
  iexact Hm

end errVarLeafOfNew

end Perennial
