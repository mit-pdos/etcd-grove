/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.read`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`readInit`, `BaseApply.lean`): its counters `slowReadIndex` and `readIndexFailed`
(`metrics.go`, translated: `prometheus.NewCounter` of a `CounterOpts` literal, the trust-boundary
axiom `NewCounter.wp_proof`), `readIndexRetryTime`,
the error variables it returns or compares with, from their packages' facts (`etcdserver/errors`'
and raft's, leaf errors by `EtcdGrove.ErrorStringLeaf`), and `context`'s
(`EtcdGrove.ContextReadErrs.errs`, from Perennial's `context.isInit`; a premise until ctx-leaf-fix,
2026-11-25). Its translated
`init()` registers the two counters (`prometheus.MustRegister`, the trust-boundary axiom
`MustRegister.wp_proof`), which takes the right to register each name: the precondition
`namesFree regNames` (decision D16; until mustreg, 2026-11-20, `EtcdGrove.read.readRegPerm`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.context.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Metrics
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
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

section ctxFacts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`context.Canceled` and `context.DeadlineExceeded` as Go defines them** (item 8, 2026-10-17;
a premise, the class `ContextReadErrs`, until ctx-leaf-fix, 2026-11-25): `Canceled =
errors.New("context canceled")`, a leaf pointer error without `Is` or `GRPCStatus` whose `Error()`
returns its message, and `DeadlineExceeded = deadlineExceededError{}`, a leaf non-pointer error
without `Is` or `GRPCStatus`, a key of `togRPCError`'s map (`errKeyOk`), whose `Error()` returns
(`context.go`: its methods are `Error`, `Timeout` and `Temporary`). From Perennial's
`context.isInit` (`"#HCanceledCell"`, `"#HDeadlineExceededTy"`) and the method sets goose emits.
The premise had become unsatisfiable with Perennial's P8c (`DeadlineExceeded`'s value a
`SafeMapKey`, which no non-pointer is): `notes/axiom-review/ctx-readerrs-vacuity.md`. -/
theorem EtcdGrove.ContextReadErrs.errs [ctx_sem : _root_.Perennial.context.Assumptions]
    [_root_.Perennial.errors.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      EtcdGrove.errVarLeafW _root_.Perennial.context.Canceled ∗
        go_etcd_io.etcd.server.v3.etcdserver.read.ctxDeadlineLeafW := by
  iintro #Hp
  ihave Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply _root_.Perennial.context.isInit_access $$ Hp
  iNamed Hci
  icases HCanceledCell with ⟨%x, #Hx, #Hs⟩
  isplitl
  · iunfold EtcdGrove.errVarLeafW
    iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
    iframe Hx
    isplitr
    · ipureintro
      have h := EtcdGrove.errorString_errLeaf x
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    · iunfold EtcdGrove.errMsgOk
      iexists go!"context canceled"
      iintro !> %Φ HΦ
      rw [method_unfold]
      wp_auto
      iexact HΦ
  · have h := fun m => go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) m
    have hG := h go!"GRPCStatus"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hG
    have hl := EtcdGrove.deadlineExceededError_leaf (ctx_sem := ctx_sem)
      (#(zero_val _root_.Perennial.context.deadlineExceededError) : val)
    iexists ⟨_root_.Perennial.context.deadlineExceededError.ty,
      #(zero_val _root_.Perennial.context.deadlineExceededError)⟩
    iframe HDeadlineExceededTy
    isplitr
    · ipureintro
      exact ⟨hl.1, hl.2, _root_.Perennial.context.deadlineExceededError_ne_ptr,
        Or.inr (Or.inr (Or.inl rfl)), hG⟩
    · iunfold EtcdGrove.errMsgOk
      iexists go!"context deadline exceeded"
      iintro !> %Φ HΦ
      wp_method_call
      unfold _root_.Perennial.context.deadlineExceededError.Error.impl
      wp_auto
      iexact HΦ

/-- `ContextReadErrs.errs` with the two errors' `Format` facts (premise-fixes-4: `errVarLeaf`,
`ctxDeadlineLeaf`): neither has a `Format` method, from Perennial's `context.isInit` (`Canceled`'s
value is a `*errors.errorString`, `EtcdGrove.ErrorStringLeaf`; `DeadlineExceeded`'s a
`deadlineExceededError`, whose method set goose emits). -/
theorem EtcdGrove.ContextReadErrs.errs_strong
    [_root_.Perennial.context.Assumptions] [_root_.Perennial.errors.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      EtcdGrove.errVarLeaf _root_.Perennial.context.Canceled ∗
        go_etcd_io.etcd.server.v3.etcdserver.read.ctxDeadlineLeaf := by
  iintro #Hp
  ihave ⟨#HC, #HD⟩ := EtcdGrove.ContextReadErrs.errs $$ Hp
  ihave Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply _root_.Perennial.context.isInit_access $$ Hp
  iNamed Hci
  icases HCanceledCell with ⟨%x, #Hx, -⟩
  iunfold EtcdGrove.errVarLeafW at HC
  icases HC with ⟨%e, #He, %Hl, #Hm⟩
  icombine He Hx gives %Heq
  icases HD with ⟨%d, #Hd, %Hdl, #Hdm⟩
  icombine Hd HDeadlineExceededTy gives %Heq2
  have hF : methodSet e.ty !! go!"Format" = none := by
    cases Heq; exact EtcdGrove.ErrorStringLeaf.noFormat
  have hE : methodSet e.ty !! go!"Error" = some (go.signature.Signature [] false [go.string]) := by
    cases Heq; exact EtcdGrove.ErrorStringLeaf.errorSig
  have hF2 : methodSet d.ty !! go!"Format" = none := by
    cases Heq2
    have h := go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Format"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h
    exact h
  have hE2 : methodSet d.ty !! go!"Error" = some (go.signature.Signature [] false [go.string]) := by
    cases Heq2
    have h := go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Error"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h
    exact h
  isplitl
  · iunfold EtcdGrove.errVarLeaf
    iexists e; iframe He Hm
    ipureintro; exact ⟨Hl.1, Hl.2.1, Hl.2.2.1, Hl.2.2.2, hF, hE⟩
  · iexists d; iframe Hd Hdm
    ipureintro; exact ⟨Hdl.1, Hdl.2.1, Hdl.2.2.1, Hdl.2.2.2.1, Hdl.2.2.2.2, hF2, hE2⟩

end ctxFacts

namespace go_etcd_io.etcd.server.v3.etcdserver.read

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"slow_read_indexes_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"read_indexes_failed_total"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := []

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights (keyed by ID,
`EtcdGrove.prometheus.regRes`) are its initializer's resources (`ownInitResL`,
`Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regKeys)]

end go_etcd_io.etcd.server.v3.etcdserver.read

end Perennial
