/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.wal.walpb`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`walpbInit`, `PkgInit.lean`): `ErrCRCMismatch` holds for good an error whose `Error()`
returns (`errOk`) and on which `errors.Is` returns for every pointer target (`errIsTerm`: an `*errorString`
leaf, `errIsTerm_errorString`), an `*errorString` whose field holds its message (2026-11-22, `WalDecEnvSupply`'s
proof: it differs from `io.EOF`). Its initializer stores that error (a translated `errors.New` call, record.go;
Perennial's `errors.wp_New_errorString`), initializes its imports and runs the untranslated
initializers of its protobuf descriptors and its `init` function, which the trust-boundary axioms
`opaqueInitsOk` and `initFuncsOk` say run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sync.atomic.Link
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.google_golang_org.protobuf.reflect.protoreflect.Init
public import Proof.google_golang_org.protobuf.runtime.protoimpl.Init
public import Proof.models_lab.pbcodec.Init
public import Perennial.Proof.errors.NewVar
public import Proof.errors.ErrIsTerm
public import Proof.errors.ErrorStringOk
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
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

namespace go_etcd_io.etcd.server.v3.storage.wal.walpb

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCRCMismatch _ as HErrCRCMismatch
  wp_apply (_root_.Perennial.google_golang_org.protobuf.runtime.protoimpl.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.reflect.protoreflect.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.models_lab.pbcodec.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrCRCMismatch))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xC ⟨#ECc, #EC⟩
  try wp_auto
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  ipersist HErrCRCMismatch
  ihave #TC := EtcdGrove.errIsTerm_errorString xC $$ Hd3
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold EtcdGrove.walpb.walpbInit
  iexists _
  iframe HErrCRCMismatch TC
  isplitl
  · iapply EtcdGrove.errorString_errOk
    iexact EC
  iexists xC
  iframe ECc
  ipureintro
  rfl

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal.walpb }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.storage.wal.walpb

end init

end Perennial
