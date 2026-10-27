/-
Package initialization of `go_etcd_io.etcd.client.v3.concurrency`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`concurrencyInit`, `Base.lean`): `Mutex`'s three errors and `Election`'s two each
hold a fixed non-nil error. Its initializer allocates them, initializes its imports and runs their
translated initializers (`errors.New` calls, `mutex.go`, `election.go`; Perennial's
`context.wp_New_errorString`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_uber_org.zap.Init
public import Perennial.Proof.context.NewErrorString
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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.client.v3.concurrency.Assumptions]

namespace go_etcd_io.etcd.client.v3.concurrency

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.client.v3.concurrency get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLockReleased _ as HErrLockReleased
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSessionExpired _ as HErrSessionExpired
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLocked _ as HErrLocked
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrElectionNoLeader _ as HErrElectionNoLeader
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrElectionNotLeader _ as HErrElectionNotLeader
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrElectionNotLeader))
  -- translated initializer of ErrElectionNoLeader))
  -- translated initializer of ErrLocked))
  -- translated initializer of ErrSessionExpired))
  -- translated initializer of ErrLockReleased))
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xN #MN
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xO #MO
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xL #ML
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xS #MS
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xR #MR
  try wp_auto
  ipersist HErrElectionNotLeader
  ipersist HErrElectionNoLeader
  ipersist HErrLocked
  ipersist HErrSessionExpired
  ipersist HErrLockReleased
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold concurrencyInit
  isplitr
  · iexists _; iexact HErrLocked
  isplitr
  · iexists _; iexact HErrSessionExpired
  isplitr
  · iexists _; iexact HErrLockReleased
  isplitr
  · iexists _; iexact HErrElectionNotLeader
  iexists _; iexact HErrElectionNoLeader

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.client.v3.concurrency get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.client.v3.concurrency

end init

end Perennial
