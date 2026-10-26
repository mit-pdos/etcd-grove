/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.read`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`readInit`, `BaseApply.lean`): its counters `slowReadIndex` and `readIndexFailed`
(`metrics.go`, translated: `prometheus.NewCounter` of a `CounterOpts` literal, the trust-boundary
axioms `EtcdGrove.prometheus.wp_counterOptsLit` and `NewCounter.wp_proof`), `readIndexRetryTime`,
the error variables it returns or compares with, from their packages' facts (`etcdserver/errors`'
and raft's, leaf errors by the premise `EtcdGrove.ErrorStringLeaf`), and `context`'s
(`EtcdGrove.ContextReadErrs`, a premise: Perennial's `context` fact lacks them). Its translated
`init()` registers the two counters (`prometheus.MustRegister`, the trust-boundary axiom
`MustRegister.wp_proof`), which takes the right to register each name: the precondition
`EtcdGrove.read.readRegPerm` (decision D16).
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
public import Proof.github_com.prometheus.client_golang.prometheus.NewCounter
public import Proof.github_com.prometheus.client_golang.prometheus.MustRegister
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.runtime.PkgInitExt

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

/-- **The trust boundary: `context.Canceled` and `context.DeadlineExceeded` as Go defines them**
(a premise, stated locally; item 8, 2026-10-17): `Canceled = errors.New("context canceled")`, a
leaf pointer error without `Is` whose `Error()` returns, and `DeadlineExceeded =
deadlineExceededError{}`, a leaf non-pointer error (an empty struct: comparable, a safe map
key) without `Is` whose `Error()` returns (`context.go`: its methods are `Error`, `Timeout` and
`Temporary`). Perennial's `context.initialize'` stores exactly these values, but its fact
(`isInit`) keeps only that they are typed errors, and the method sets are uninterpreted: the
general fix is a Perennial change (`notes/decisions.md`, "Item 8: context's facts"). A
premise rather than an axiom: `isPkgInit context` is not sealed (any proof holding the
variables' cells could make it), so as an axiom the entailment could be used to prove `False`.
(`v3rpc`'s `context.Canceled` fact, until then the premise `ContextCanceledPtr`, follows.) -/
class EtcdGrove.ContextReadErrs : Prop where
  errs : isPkgInit (PROP := IProp GF) pkg_id.context ⊢
    EtcdGrove.errVarLeaf _root_.Perennial.context.Canceled ∗
      go_etcd_io.etcd.server.v3.etcdserver.read.ctxDeadlineLeaf

end ctxFacts

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]
variable [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable [EtcdGrove.ErrorStringLeaf]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]
variable [_root_.Perennial.log.NewModel]

namespace go_etcd_io.etcd.server.v3.etcdserver.read

theorem wp_initialize'_res (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read get_is_pkg_init) :
    {{ EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_res_self (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro ⟨Hown, HR⟩
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.time.Duration) readIndexRetryTime _ as HreadIndexRetryTime
  wp_apply wp_GlobalAlloc (V := GoInterface) readIndexFailed _ as HreadIndexFailed
  wp_apply wp_GlobalAlloc (V := GoInterface) slowReadIndex _ as HslowReadIndex
  wp_apply _root_.Perennial.go_etcd_io.raft.v3.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.traceutil.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply _root_.Perennial.go_uber_org.zap.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.context.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of slowReadIndex))
  -- translated initializer of readIndexFailed))
  -- translated initializer of readIndexRetryTime))
  wp_apply EtcdGrove.prometheus.wp_counterOptsLit as %o1 %Ho1
  try wp_auto
  wp_apply EtcdGrove.prometheus.NewCounter.wp_proof _ _ _ _ _ Ho1 (by decide) as %c1 ⟨#C1, %N1⟩
  try wp_auto
  wp_apply EtcdGrove.prometheus.wp_counterOptsLit as %o2 %Ho2
  try wp_auto
  wp_apply EtcdGrove.prometheus.NewCounter.wp_proof _ _ _ _ _ Ho2 (by decide) as %c2 ⟨#C2, %N2⟩
  try wp_auto
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  iunfold EtcdGrove.read.readRegPerm at HR
  icases HR with ⟨HR1, HR2⟩
  wp_apply wp_slice_literal (l := [GoInterface.ok c1])
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨S1, -⟩
  try wp_auto
  wp_apply EtcdGrove.prometheus.MustRegister.wp_proof _ _ _ _ N1 $$ [S1 HR1] as S1
  · iframe S1 HR1
  wp_apply wp_slice_literal (l := [GoInterface.ok c2])
  isplitr
  · ipureintro; rfl
  iintro %s2 ⟨S2, -⟩
  try wp_auto
  wp_apply EtcdGrove.prometheus.MustRegister.wp_proof _ _ _ _ N2 $$ [S2 HR2] as S2
  · iframe S2 HR2
  ipersist HslowReadIndex
  ipersist HreadIndexFailed
  ipersist HreadIndexRetryTime
  ihave HeiSTP : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd10
  icases HeiSTP with ⟨-, #HevSTP, -⟩
  ihave #NSTP := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped) (m := go!"etcdserver: server stopped") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevSTP
  ihave #LSTP := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NSTP
  iunfold EtcdGrove.errorsNewVar at NSTP
  icases NSTP with ⟨%xSTP, #HSTP, -⟩
  ihave HeiLCH : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd10
  icases HeiLCH with ⟨-, #HevLCH, -⟩
  ihave #NLCH := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged) (m := go!"etcdserver: leader changed") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevLCH
  ihave #LLCH := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NLCH
  iunfold EtcdGrove.errorsNewVar at NLCH
  icases NLCH with ⟨%xLCH, #HLCH, -⟩
  ihave HeiTMO : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd10
  icases HeiTMO with ⟨-, #HevTMO, -⟩
  ihave #NTMO := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout) (m := go!"etcdserver: request timed out") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevTMO
  ihave #LTMO := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NTMO
  iunfold EtcdGrove.errorsNewVar at NTMO
  icases NTMO with ⟨%xTMO, #HTMO, -⟩
  ihave Hri : (go_etcd_io.raft.v3.isInitialized : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd11
  iunfold go_etcd_io.raft.v3.isInitialized at Hri
  icases Hri with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, Hrr⟩
  iNamed Hrr
  ihave #LRS := EtcdGrove.errVarLeaf_of_newVar _ _ $$ ErrStoppedNew
  ihave ⟨#LCC, #LDL⟩ := EtcdGrove.ContextReadErrs.errs $$ Hd2
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold readInit
  iframe #

/-- Perennial's form with the resource (decision D16), from `wp_initialize'_res`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init ∗ EtcdGrove.read.readRegPerm (GF := GF) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read }} :=
  EtcdGrove.wp_init_of_res _ _ _ _ _ (wp_initialize'_res get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.etcdserver.read

end init

end Perennial
