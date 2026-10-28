/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.apply`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`applyInit`, `Base.lean`): its gauge vector `alarms` with its label names
(`metrics.go`, untranslated: the trust-boundary axiom `alarms_init`), and the error variables it returns or compares with
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

/-- `alarms = prometheus.NewGaugeVec(..., []string{"server_id", "alarm_type"})`
(`metrics.go`): a `*GaugeVec` with those label names (`vecLabels`). -/
axiom alarms_init :
    {{ (True : IProp GF) }} (App (Val alarms.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr alarms ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"server_id", go!"alarm_type"]⌝ }}

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
  · ipureintro; exact EtcdGrove.errorString_leaf x
  unfold EtcdGrove.errMsgOk
  iapply EtcdGrove.errorMsg_triple
  iexact Hm

end errVarLeafOfNew

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.etcdserver.apply

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd27⟩
  wp_apply (_root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd26⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd25⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.cindex.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.errors.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.version.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.types.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.membershippb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.github_com.Masterminds.semver.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.lease.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.auth.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.traceutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.wait.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.pbutil.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply alarms_init as ⟨%valarms, Halarms, #Lalarms⟩
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist Halarms
  ihave HeiCOR : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd19
  icases HeiCOR with ⟨-, #HevCOR, -⟩
  ihave #NCOR := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt) (m := go!"etcdserver: corrupt cluster") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevCOR
  ihave #LCOR := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NCOR
  iunfold EtcdGrove.errorsNewVar at NCOR
  icases NCOR with ⟨%xCOR, #HCOR, -⟩
  ihave HeiNSP : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd19
  icases HeiNSP with ⟨-, #HevNSP, -⟩
  ihave #NNSP := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace) (m := go!"etcdserver: no space") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevNSP
  ihave #LNSP := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NNSP
  iunfold EtcdGrove.errorsNewVar at NNSP
  icases NNSP with ⟨%xNSP, #HNSP, -⟩
  ihave HeiKNF : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd19
  icases HeiKNF with ⟨-, #HevKNF, -⟩
  ihave #NKNF := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound) (m := go!"etcdserver: key not found") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevKNF
  ihave #LKNF := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NKNF
  iunfold EtcdGrove.errorsNewVar at NKNF
  icases NKNF with ⟨%xKNF, #HKNF, -⟩
  ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd10
  icases Hli with ⟨#HLNF0, -, -, -, -, -, -, #CLNF⟩
  ihave #LLNF : (EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound : IProp GF) $$ []
  · unfold EtcdGrove.errVarLeaf EtcdGrove.errLeaf EtcdGrove.errMsgOk
    iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at HLNF0
    iexact HLNF0
  ihave Hmi : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd18
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #NMC, #NMF, -, -, #CMC, #CMF, -⟩
  ihave #LMC := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NMC
  ihave #LMF := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NMF
  ihave HeiE : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd19
  icases HeiE with ⟨-, -, #HcE⟩
  ihave #CNSP := EtcdGrove.errVarCells_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace) (m := go!"etcdserver: no space") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HcE
  ihave #CKNF := EtcdGrove.errVarCells_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound) (m := go!"etcdserver: key not found") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HcE
  ihave #AKNF := EtcdGrove.errVarApart_of go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound go!"etcdserver: no space" go!"etcdserver: key not found" (by decide) $$ CNSP CKNF
  ihave #ALNF := EtcdGrove.errVarApart_of go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound go!"etcdserver: no space" go!"lease not found" (by decide) $$ CNSP CLNF
  ihave #AMF := EtcdGrove.errVarApart_of go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev go!"etcdserver: no space" go!"mvcc: required revision is a future revision" (by decide) $$ CNSP CMF
  ihave #AMC := EtcdGrove.errVarApart_of go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted go!"etcdserver: no space" go!"mvcc: required revision has been compacted" (by decide) $$ CNSP CMC
  ihave Hau : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd9
  icases Hau with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #AUC⟩
  ihave #AAU := EtcdGrove.errVarApart_cells go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace go!"etcdserver: no space" go_etcd_io.etcd.server.v3.auth.authErrMsgs (go_etcd_io.etcd.server.v3.auth.authErrMsgs_ne_of _ (by decide)) $$ CNSP AUC
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold applyInit applyErrVars authErrsApart
  iframe #

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.etcdserver.apply

end init

end Perennial
