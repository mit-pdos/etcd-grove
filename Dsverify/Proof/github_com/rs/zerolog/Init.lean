/-
Package initialization of `github_com.rs.zerolog`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates its translated variables, initializes its imports,
runs their translated initializers (constants, function literals, `sync.Pool` literals, `new(int32)`)
and its two translated `init`s: `init.0` (`ctx.go`: `SetGlobalLevel(TraceLevel)`, `disabledLogger =
&Nop()`) and `init.1` (`encoder_json.go`), which stores a closure in `internal/json`'s
`JSONMarshalFunc`, another package's variable: through `internal/json`'s invariant, lending the
initializer's package state (`EtcdGrove.grpcInternal.wp_store_hook`). (dsv-retire-3, 2026-11-26: until
then names only, its `wp_initialize'` a trust-boundary axiom.)
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.math.rand.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unsafe.Link
public import Proof.encoding.json.Init
public import Dsverify.Proof.github_com.rs.zerolog.internal.json.Init
public import Dsverify.Proof.io.ioutil.Init
public import Proof.net.Init
public import Proof.os.Init
public import Proof.path.filepath.Init
public import Proof.runtime.Init
public import Dsverify.Proof.github_com.rs.zerolog.NewNil
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
variable [package_sem : _root_.Perennial.github_com.rs.zerolog.Assumptions]

namespace github_com.rs.zerolog

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.rs.zerolog get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := w32) Rarely _ as HRarely
  wp_apply wp_GlobalAlloc (V := w32) Sometimes _ as HSometimes
  wp_apply wp_GlobalAlloc (V := w32) Often _ as HOften
  wp_apply wp_GlobalAlloc (V := Loc) disableSampling _ as HdisableSampling
  wp_apply wp_GlobalAlloc (V := Loc) gLevel _ as HgLevel
  wp_apply wp_GlobalAlloc (V := GoFunc) ErrorHandler _ as HErrorHandler
  wp_apply wp_GlobalAlloc (V := Bool) DurationFieldInteger _ as HDurationFieldInteger
  wp_apply wp_GlobalAlloc (V := w64) DurationFieldUnit _ as HDurationFieldUnit
  wp_apply wp_GlobalAlloc (V := GoFunc) TimestampFunc _ as HTimestampFunc
  wp_apply wp_GlobalAlloc (V := GoString) TimeFieldFormat _ as HTimeFieldFormat
  wp_apply wp_GlobalAlloc (V := GoFunc) InterfaceMarshalFunc _ as HInterfaceMarshalFunc
  wp_apply wp_GlobalAlloc (V := GoFunc) ErrorMarshalFunc _ as HErrorMarshalFunc
  wp_apply wp_GlobalAlloc (V := GoFunc) ErrorStackMarshaler _ as HErrorStackMarshaler
  wp_apply wp_GlobalAlloc (V := GoString) ErrorStackFieldName _ as HErrorStackFieldName
  wp_apply wp_GlobalAlloc (V := GoFunc) CallerMarshalFunc _ as HCallerMarshalFunc
  wp_apply wp_GlobalAlloc (V := w64) CallerSkipFrameCount _ as HCallerSkipFrameCount
  wp_apply wp_GlobalAlloc (V := GoString) CallerFieldName _ as HCallerFieldName
  wp_apply wp_GlobalAlloc (V := GoString) ErrorFieldName _ as HErrorFieldName
  wp_apply wp_GlobalAlloc (V := GoString) MessageFieldName _ as HMessageFieldName
  wp_apply wp_GlobalAlloc (V := GoFunc) LevelFieldMarshalFunc _ as HLevelFieldMarshalFunc
  wp_apply wp_GlobalAlloc (V := GoString) LevelPanicValue _ as HLevelPanicValue
  wp_apply wp_GlobalAlloc (V := GoString) LevelFatalValue _ as HLevelFatalValue
  wp_apply wp_GlobalAlloc (V := GoString) LevelErrorValue _ as HLevelErrorValue
  wp_apply wp_GlobalAlloc (V := GoString) LevelWarnValue _ as HLevelWarnValue
  wp_apply wp_GlobalAlloc (V := GoString) LevelInfoValue _ as HLevelInfoValue
  wp_apply wp_GlobalAlloc (V := GoString) LevelDebugValue _ as HLevelDebugValue
  wp_apply wp_GlobalAlloc (V := GoString) LevelTraceValue _ as HLevelTraceValue
  wp_apply wp_GlobalAlloc (V := GoString) LevelFieldName _ as HLevelFieldName
  wp_apply wp_GlobalAlloc (V := GoString) TimestampFieldName _ as HTimestampFieldName
  wp_apply wp_GlobalAlloc (V := Loc) eventPool _ as HeventPool
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.github_com.rs.zerolog.internal.json.Encoder) enc _ as Henc
  wp_apply wp_GlobalAlloc (V := Loc) disabledLogger _ as HdisabledLogger
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.github_com.rs.zerolog.timestampHook) th _ as Hth
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Pool) consoleBufPool _ as HconsoleBufPool
  wp_apply wp_GlobalAlloc (V := Loc) arrayPool _ as HarrayPool
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math.rand _root_.Perennial.math.rand.initialize'
      EtcdGrove.ExternalInit.math_rand _root_.Perennial.math.rand.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.«unsafe» _root_.Perennial.«unsafe».initialize'
      EtcdGrove.ExternalInit.unsafe_ _root_.Perennial.«unsafe».wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.github_com.rs.zerolog.internal.json.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.io.ioutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.path.filepath.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.encoding.json.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.net.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of arrayPool))
  repeat (first | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto) | (wp_func_lits; wp_auto) | wp_auto)
  -- translated initializer of consoleBufPool))
  -- translated initializer of th))
  -- translated initializer of enc))
  -- translated initializer of eventPool))
  -- translated initializer of TimestampFieldName))
  -- translated initializer of LevelFieldName))
  -- translated initializer of LevelTraceValue))
  -- translated initializer of LevelDebugValue))
  -- translated initializer of LevelInfoValue))
  -- translated initializer of LevelWarnValue))
  -- translated initializer of LevelErrorValue))
  -- translated initializer of LevelFatalValue))
  -- translated initializer of LevelPanicValue))
  -- translated initializer of LevelFieldMarshalFunc))
  -- translated initializer of MessageFieldName))
  -- translated initializer of ErrorFieldName))
  -- translated initializer of CallerFieldName))
  -- translated initializer of CallerSkipFrameCount))
  -- translated initializer of CallerMarshalFunc))
  -- translated initializer of ErrorStackFieldName))
  -- translated initializer of ErrorMarshalFunc))
  -- translated initializer of InterfaceMarshalFunc))
  -- translated initializer of TimeFieldFormat))
  -- translated initializer of TimestampFunc))
  -- translated initializer of DurationFieldUnit))
  -- translated initializer of DurationFieldInteger))
  -- translated initializer of gLevel))
  -- translated initializer of disableSampling))
  -- translated initializer of Often))
  -- translated initializer of Sometimes))
  -- translated initializer of Rarely))
  rename_i _ _ pgl
  irename: (pgl ↦ (_ : w32) : IProp GF) => HgCell
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  -- `SetGlobalLevel(TraceLevel)`: the atomic store into `gLevel`'s cell, owned here
  unfold TraceLevel
  wp_func_call
  wp_call
  try wp_auto
  wp_apply_core sync.atomic.wp_StoreInt32 $$ [] [-]
  · iexact Hd19
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe HgCell
  iintro HgCell
  imod Hmask with -
  imodintro
  try wp_auto
  -- `Nop()`: `New(nil).Level(Disabled)`; `New(nil)` reads `ioutil.Discard` (io/ioutil's fact)
  ihave #ID : (∃ w : GoInterface, globalAddr _root_.Perennial.io.ioutil.Discard ↦□ w : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd13
  icases ID with ⟨%wdis, #HDis⟩
  wp_apply (wp_Nop wdis) $$ HDis as %lnop -
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  ihave #Hfj : (_root_.Perennial.github_com.rs.zerolog.internal.json.jsonInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd16
  try wp_auto
  unfold _root_.Perennial.github_com.rs.zerolog.internal.json.jsonInit
  icases Hfj with ⟨#Hfc, -⟩
  wp_apply (EtcdGrove.grpcInternal.wp_store_hook (hG := hG) (V := GoFunc) _ _ _ _) $$ [Hfc Hown] as Hown
  · iframe Hown Hfc
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.rs.zerolog get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.rs.zerolog

end init

end Perennial
