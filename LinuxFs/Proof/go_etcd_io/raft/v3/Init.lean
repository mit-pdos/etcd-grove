/-
Package initialization of `go_etcd_io.raft.v3`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import LinuxFs.Proof.go_etcd_io.raft.v3.PkgInit
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.crypto.rand.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import LinuxFs.Proof.go_etcd_io.raft.v3.InitPb
public import LinuxFs.Proof.os.Init
public import LinuxFs.Proof.runtime.PkgInitExt

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
namespace go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.raft.v3`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([defaultLogger.init,
        discardLogger.init,
        raftLogger.init,
        ErrStopped.init,
        ErrProposalDropped.init,
        globalRand.init,
        stmap.init,
        errBreak.init,
        ErrStepLocalMsg.init,
        ErrStepPeerNotFound.init,
        ErrCompacted.init,
        ErrSnapOutOfDate.init,
        ErrUnavailable.init,
        ErrSnapshotTemporarilyUnavailable.init,
        isLocalMsg.init,
        isResponseMsg.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end go_etcd_io.raft.v3
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.raft.v3.Assumptions]

namespace go_etcd_io.raft.v3

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) emptyState _ as HemptyState
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.tracker _root_.Perennial.go_etcd_io.raft.v3.tracker.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_tracker _root_.Perennial.go_etcd_io.raft.v3.tracker.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.quorum _root_.Perennial.go_etcd_io.raft.v3.quorum.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_quorum _root_.Perennial.go_etcd_io.raft.v3.quorum.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.confchange _root_.Perennial.go_etcd_io.raft.v3.confchange.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_confchange _root_.Perennial.go_etcd_io.raft.v3.confchange.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.slices _root_.Perennial.slices.initialize'
      EtcdGrove.ExternalInit.slices _root_.Perennial.slices.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.crypto.rand _root_.Perennial.crypto.rand.initialize'
      EtcdGrove.ExternalInit.crypto_rand _root_.Perennial.crypto.rand.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.log _root_.Perennial.log.initialize'
      EtcdGrove.ExternalInit.log _root_.Perennial.log.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk defaultLogger.init (by mem_tac))
  wp_apply (opaqueInitsOk discardLogger.init (by mem_tac))
  wp_apply (opaqueInitsOk raftLogger.init (by mem_tac))
  -- translated initializer of emptyState))
  wp_apply (opaqueInitsOk ErrStopped.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrProposalDropped.init (by mem_tac))
  wp_apply (opaqueInitsOk globalRand.init (by mem_tac))
  wp_apply (opaqueInitsOk stmap.init (by mem_tac))
  wp_apply (opaqueInitsOk errBreak.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrStepLocalMsg.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrStepPeerNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrCompacted.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrSnapOutOfDate.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnavailable.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrSnapshotTemporarilyUnavailable.init (by mem_tac))
  wp_apply (opaqueInitsOk isLocalMsg.init (by mem_tac))
  wp_apply (opaqueInitsOk isResponseMsg.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.raft.v3

end init

end Perennial
