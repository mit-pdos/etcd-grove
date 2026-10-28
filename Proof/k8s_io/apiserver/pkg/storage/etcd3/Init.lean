/-
Package initialization of `k8s_io.apiserver.pkg.storage.etcd3`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates its variables, initializes its imports, runs
the translated initializers (`errTooMany`, an `errors.New` error; `typeToMessage`, a map literal;
`defaultWatcherMaxLimit`) and its translated `init` functions: `compact.go`'s makes
`endpointsMap`, `logger.go`'s sets grpc's logger (`grpclog.SetLoggerV2`, names-only: the
trust-boundary axiom `grpclog.SetLoggerV2.wp_proof`), `watcher.go`'s stores in
`fatalOnDecodeError` whether `KUBE_PANIC_WATCH_DECODE_ERROR` parses as true (`os.Getenv` and
`strconv.ParseBool`, names-only in Perennial: the trust-boundary axioms `os.Getenv.wp_proof` and
`strconv.ParseBool.wp_proof`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.iter.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.json.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.grpclog.Init
public import Proof.google_golang_org.grpc.status.Init
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.unstructured.Init
public import Proof.k8s_io.apimachinery.pkg.conversion.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.util.errors.Init
public import Proof.k8s_io.apimachinery.pkg.util.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.util.wait.Init
public import Proof.k8s_io.apimachinery.pkg.watch.Init
public import Proof.k8s_io.apiserver.pkg.audit.Init
public import Proof.k8s_io.apiserver.pkg.endpoints.request.Init
public import Proof.k8s_io.apiserver.pkg.features.Init
public import Proof.k8s_io.apiserver.pkg.storage.Init
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.metrics.Init
public import Proof.k8s_io.apiserver.pkg.storage.feature.Init
public import Proof.k8s_io.apiserver.pkg.storage.value.Init
public import Proof.k8s_io.apiserver.pkg.util.feature.Init
public import Proof.k8s_io.apiserver.pkg.util.flowcontrol.Init
public import Proof.k8s_io.component_base.tracing.Init
public import Proof.k8s_io.klog.v2.Init
public import Proof.k8s_io.utils.clock.Init
public import Proof.net.http.Init
public import Proof.path.Init
public import Proof.reflect.Init
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.sync.atomic.Link
public import Proof.google_golang_org.grpc.grpclog.SetLoggerV2
public import Proof.os.Getenv
public import Proof.strconv.ParseBool
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

section toLoggerV2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `logger.go`'s conversion of a `klogWrapper` to `grpclog.LoggerV2`** (an
interface: a struct converted to it is the interface holding it). `type LoggerV2
internal.LoggerV2` names a package this translation does not import, so the type is
axiomatized (Goose's gap G3, `notes/k8s-etcd3-goose.md`) and the conversion does not step; the
axiom says it returns some interface value, which is all `SetLoggerV2`'s spec needs. -/
axiom k8s_io.apiserver.pkg.storage.etcd3.klogWrapper_toLoggerV2 (v : val) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (Convert k8s_io.apiserver.pkg.storage.etcd3.klogWrapper.ty
        google_golang_org.grpc.grpclog.LoggerV2.ty))) (Val v))
    {{ (i : GoInterface), RET #i; True }}

end toLoggerV2

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

namespace k8s_io.apiserver.pkg.storage.etcd3

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.etcd3 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.atomic.Bool') fatalOnDecodeError _ as HfatalOnDecodeError
  wp_apply wp_GlobalAlloc (V := w64) defaultWatcherMaxLimit _ as HdefaultWatcherMaxLimit
  wp_apply wp_GlobalAlloc (V := Loc) typeToMessage _ as HtypeToMessage
  wp_apply wp_GlobalAlloc (V := GoInterface) errTooMany _ as HerrTooMany
  wp_apply wp_GlobalAlloc (V := Loc) endpointsMap _ as HendpointsMap
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Mutex) endpointsMapMu _ as HendpointsMapMu
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.util.flowcontrol.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd46⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.os _root_.Perennial.os.initialize'
      EtcdGrove.ExternalInit.os _root_.Perennial.os.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd45⟩
  wp_apply (_root_.Perennial.k8s_io.component_base.tracing.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd44⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.storage.feature.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd43⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.audit.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd42⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.watch.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd41⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd40⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.api.«meta».wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd39⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.status.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd38⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.codes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd37⟩
  wp_apply (_root_.Perennial.go_opentelemetry_io.otel.«attribute».wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd36⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.v3.kubernetes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd35⟩
  wp_apply (_root_.Perennial.reflect.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd34⟩
  wp_apply (_root_.Perennial.path.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd33⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.iter _root_.Perennial.iter.initialize'
      EtcdGrove.ExternalInit.iter _root_.Perennial.iter.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd32⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd31⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd30⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.grpclog.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd29⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.metrics.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd28⟩
  wp_apply (_root_.Perennial.encoding.json.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd27⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd26⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd25⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.endpoints.request.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.conversion.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.storage.value.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.storage.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.errors.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.api.errors.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (_root_.Perennial.net.http.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.util.feature.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.features.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.wait.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.k8s_io.utils.clock.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.k8s_io.klog.v2.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of errTooMany))
  -- translated initializer of typeToMessage))
  -- translated initializer of defaultWatcherMaxLimit))
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %_ -
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoString) go.int go.string) as %mref Hmap
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := w64) (V := GoString) go.int) $$ Hmap as Hmap; try wp_auto)
  wp_alloc dd as Hdd
  try wp_auto
  wp_alloc tw as Htw
  try wp_auto
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
      (go.GoType.PointerType compactor.ty)) as %em Hem
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  wp_apply klogWrapper_toLoggerV2 as %_ -
  try wp_auto
  wp_apply EtcdGrove.grpclog.SetLoggerV2.wp_proof
  try wp_auto
  -- the translated init.«2»
  wp_func_call
  wp_call
  try wp_auto
  wp_apply EtcdGrove.os.Getenv.wp_proof as %_ -
  try wp_auto
  wp_apply EtcdGrove.strconv.ParseBool.wp_proof as %_ %_ -
  try wp_auto
  ihave Hfod : _root_.Perennial.sync.atomic.ownBool (GF := GF) (globalAddr fatalOnDecodeError) (DFrac.own 1) false $$ [HfatalOnDecodeError]
  · rw [_root_.Perennial.sync.atomic.ownBool_unseal]
    unfold _root_.Perennial.sync.atomic.ownBoolDef
    have e : (zero_val _root_.Perennial.sync.atomic.Bool') =
        ({ «_#0'» := zero_val _, v' := _root_.Perennial.sync.atomic.b32w false } :
          _root_.Perennial.sync.atomic.Bool') := rfl
    rw [← e]; iexact HfatalOnDecodeError
  wp_apply_core _root_.Perennial.sync.atomic.Bool.wp_Store $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext; iexists _; iframe Hfod; iintro _
  imod Hmask with _
  imodintro
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.etcd3 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.storage.etcd3

end init

end Perennial
