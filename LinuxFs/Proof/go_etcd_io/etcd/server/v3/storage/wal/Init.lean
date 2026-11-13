/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.wal`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`walInit`, `PkgInit.lean`): `crcTable` holds the Castagnoli table (`walCrcTable`), the
metrics `walFsyncSec`, `walWriteSec` (histograms) and `walWriteBytes` (a gauge) hold metrics whose
`Observe`/`Add` return (`wal.metricsInit`), `SegmentSizeBytes` holds `64000000`, and every error
variable an error whose `Error()` returns (`wal.errVar`), read-only for good. Its initializer
allocates its variables, initializes its imports and runs their initializers: the metrics'
untranslated `prometheus` constructors (the trust-boundary axioms `<X>_init`, metrics.go), the
translated `errors.New` calls, `ErrCRCMismatch = walpb.ErrCRCMismatch` (`walpbInit`), `crcTable =
crc32.MakeTable(crc32.Castagnoli)` (`hash.crc32.MakeTable.wp_proof`), and its untranslated `init`
function (`prometheus.MustRegister` of the metrics), which the trust-boundary axiom `initFuncsOk`
says returns.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import LinuxFs.Proof.github_com.Masterminds.semver.v3.Init
public import LinuxFs.Proof.github_com.prometheus.client_golang.prometheus.Init
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Init
public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.crc.Init
public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.ioutil.Init
public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.pbutil.Init
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Init
public import LinuxFs.Proof.go_etcd_io.raft.v3.Init
public import LinuxFs.Proof.go_etcd_io.raft.v3.InitPb
public import LinuxFs.Proof.go_uber_org.zap.Init
public import LinuxFs.Proof.hash.Init
public import LinuxFs.Proof.hash.crc32.Init
public import LinuxFs.Proof.os.Init
public import LinuxFs.Proof.path.filepath.Init
public import Perennial.Proof.errors.NewVar
public import LinuxFs.Proof.hash.crc32.MakeTable
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
namespace go_etcd_io.etcd.server.v3.storage.wal
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.wal`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `walFsyncSec = prometheus.New...(...)` (`metrics.go`): a metric whose method returns. -/
axiom walFsyncSec_init :
    {{ (True : IProp GF) }} (App (Val walFsyncSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr walFsyncSec ↦ GoInterface.ok h ∗ EtcdGrove.wal.histSpec h }}

/-- `walWriteSec = prometheus.New...(...)` (`metrics.go`): a metric whose method returns. -/
axiom walWriteSec_init :
    {{ (True : IProp GF) }} (App (Val walWriteSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr walWriteSec ↦ GoInterface.ok h ∗ EtcdGrove.wal.histSpec h }}

/-- `walWriteBytes = prometheus.New...(...)` (`metrics.go`): a metric whose method returns. -/
axiom walWriteBytes_init :
    {{ (True : IProp GF) }} (App (Val walWriteBytes.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr walWriteBytes ↦ GoInterface.ok h ∗ EtcdGrove.wal.gaugeAddSpec h }}

end go_etcd_io.etcd.server.v3.storage.wal
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

namespace go_etcd_io.etcd.server.v3.storage.wal

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.wal get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Loc) crcTable _ as HcrcTable
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDecoderNotFound _ as HErrDecoderNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSliceOutOfRange _ as HErrSliceOutOfRange
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSnapshotNotFound _ as HErrSnapshotNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSnapshotMismatch _ as HErrSnapshotMismatch
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCRCMismatch _ as HErrCRCMismatch
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrFileNotFound _ as HErrFileNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrMetadataConflict _ as HErrMetadataConflict
  wp_apply wp_GlobalAlloc (V := GoFunc) openWALFilesFn _ as HopenWALFilesFn
  wp_apply wp_GlobalAlloc (V := w64) SegmentSizeBytes _ as HSegmentSizeBytes
  wp_apply wp_GlobalAlloc (V := GoInterface) errBadWALName _ as HerrBadWALName
  wp_apply (_root_.Perennial.go_etcd_io.raft.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (_root_.Perennial.hash.crc32.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.github_com.Masterminds.semver.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.path.filepath.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.ioutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.walpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.pbutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.crc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.fileutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.hash.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply walFsyncSec_init as ⟨%hwalFsyncSec, HwalFsyncSec, #SwalFsyncSec⟩
  wp_apply walWriteSec_init as ⟨%hwalWriteSec, HwalWriteSec, #SwalWriteSec⟩
  wp_apply walWriteBytes_init as ⟨%hwalWriteBytes, HwalWriteBytes, #SwalWriteBytes⟩
  -- translated initializer of errBadWALName))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xBW #EBW
  try wp_auto
  -- translated initializer of SegmentSizeBytes))
  -- translated initializer of openWALFilesFn))
  -- translated initializer of ErrMetadataConflict))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xMC #EMC
  try wp_auto
  -- translated initializer of ErrFileNotFound))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xFN #EFN
  try wp_auto
  -- translated initializer of ErrCRCMismatch))
  try wp_auto
  ihave #Hpb : (EtcdGrove.walpb.walpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd11
  icases Hpb with ⟨%eC, #HpbC, #HpbOk⟩
  try wp_auto
  -- translated initializer of ErrSnapshotMismatch))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xSM #ESM
  try wp_auto
  -- translated initializer of ErrSnapshotNotFound))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xSN #ESN
  try wp_auto
  -- translated initializer of ErrSliceOutOfRange))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xSO #ESO
  try wp_auto
  -- translated initializer of ErrDecoderNotFound))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xDN #EDN
  try wp_auto
  -- translated initializer of crcTable))
  try wp_auto
  rw [show (W32 2197175160) = _root_.Perennial.hash.crc32.castagnoliPoly from rfl]
  wp_apply _root_.Perennial.EtcdGrove.hash.crc32.MakeTable.wp_proof as %tab #Htab
  try wp_auto
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  -- translated initializer of _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.walpb.ErrCRCMismatch))
  ipersist HerrBadWALName
  ipersist HErrMetadataConflict
  ipersist HErrFileNotFound
  ipersist HErrCRCMismatch
  ipersist HErrSnapshotMismatch
  ipersist HErrSnapshotNotFound
  ipersist HErrSliceOutOfRange
  ipersist HErrDecoderNotFound
  ipersist HcrcTable
  ipersist HSegmentSizeBytes
  ipersist HwalFsyncSec
  ipersist HwalWriteSec
  ipersist HwalWriteBytes
  ihave #VerrBadWALName : (EtcdGrove.wal.errVar errBadWALName : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar EtcdGrove.errOk
    iexists _
    iframe HerrBadWALName
    iintro !> %Φ' HΦ'
    iapply EBW
    inext
    iapply HΦ'
  ihave #VErrMetadataConflict : (EtcdGrove.wal.errVar ErrMetadataConflict : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar EtcdGrove.errOk
    iexists _
    iframe HErrMetadataConflict
    iintro !> %Φ' HΦ'
    iapply EMC
    inext
    iapply HΦ'
  ihave #VErrFileNotFound : (EtcdGrove.wal.errVar ErrFileNotFound : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar EtcdGrove.errOk
    iexists _
    iframe HErrFileNotFound
    iintro !> %Φ' HΦ'
    iapply EFN
    inext
    iapply HΦ'
  ihave #VErrSnapshotMismatch : (EtcdGrove.wal.errVar ErrSnapshotMismatch : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar EtcdGrove.errOk
    iexists _
    iframe HErrSnapshotMismatch
    iintro !> %Φ' HΦ'
    iapply ESM
    inext
    iapply HΦ'
  ihave #VErrSnapshotNotFound : (EtcdGrove.wal.errVar ErrSnapshotNotFound : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar EtcdGrove.errOk
    iexists _
    iframe HErrSnapshotNotFound
    iintro !> %Φ' HΦ'
    iapply ESN
    inext
    iapply HΦ'
  ihave #VErrSliceOutOfRange : (EtcdGrove.wal.errVar ErrSliceOutOfRange : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar EtcdGrove.errOk
    iexists _
    iframe HErrSliceOutOfRange
    iintro !> %Φ' HΦ'
    iapply ESO
    inext
    iapply HΦ'
  ihave #VErrDecoderNotFound : (EtcdGrove.wal.errVar ErrDecoderNotFound : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar EtcdGrove.errOk
    iexists _
    iframe HErrDecoderNotFound
    iintro !> %Φ' HΦ'
    iapply EDN
    inext
    iapply HΦ'
  ihave #VErrCRCMismatch : (EtcdGrove.wal.errVar ErrCRCMismatch : IProp GF) $$ []
  · unfold EtcdGrove.wal.errVar
    iexists _
    iframe HErrCRCMismatch HpbOk
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold EtcdGrove.wal.walInit EtcdGrove.WalFs.walCrcTable EtcdGrove.wal.metricsInit
  iframe #

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.wal get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.storage.wal

end init

end Perennial
