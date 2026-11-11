/-
Package initialization of `go_etcd_io.bbolt`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`bboltRootInit`, `Proof/go_etcd_io/bbolt/PkgInit.lean`): `runtime.GOOS` is
`"linux"` and `runtime.GOARCH` `"amd64"` (the trust-boundary axioms `runtime.GOOS_linux` and
`runtime.GOARCH_amd64` of `runtime`'s `Init.lean`; bbolt compares `GOOS` with `"windows"` in
`DB.grow`, `DB.mmap` and `DB.allocate`, and its loggers format both). Its initializer allocates its variables, initializes its imports and
runs their translated initializers: `trySolo` (an `errors.New` call, `db.go`; Perennial's
`errors.wp_New_errorString`), the deprecated aliases of
`errors`' variables (loads of them), and `discardLogger` (`&nopLogger{}`, the fork's no-op logger,
which the fact records: a `*nopLogger`).
And `DefaultOptions`' untranslated initializer (`Options` is an axiomatized type,
`Code/go_etcd_io/bbolt.toml`), which the trust-boundary axiom `opaqueInitsOk` says runs.
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unsafe.Link
public import Proof.encoding.hex.Init
public import Proof.go_etcd_io.bbolt.errors.Init
public import Proof.go_etcd_io.bbolt.internal.common.Init
public import Proof.go_etcd_io.bbolt.internal.freelist.Init
public import Proof.golang_org.x.sys.unix.Init
public import Proof.os.Init
public import Proof.runtime.Init
public import Proof.syscall.Init
public import Perennial.Proof.errors.NewVar
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
namespace go_etcd_io.bbolt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.bbolt`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([DefaultOptions.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end go_etcd_io.bbolt
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.bbolt.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.bbolt

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.bbolt get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) discardLogger _ as HdiscardLogger
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrIncompatibleValue _ as HErrIncompatibleValue
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrValueTooLarge _ as HErrValueTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrKeyTooLarge _ as HErrKeyTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrKeyRequired _ as HErrKeyRequired
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrBucketNameRequired _ as HErrBucketNameRequired
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrBucketExists _ as HErrBucketExists
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrBucketNotFound _ as HErrBucketNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrFreePagesNotLoaded _ as HErrFreePagesNotLoaded
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDatabaseReadOnly _ as HErrDatabaseReadOnly
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTxClosed _ as HErrTxClosed
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTxNotWritable _ as HErrTxNotWritable
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTimeout _ as HErrTimeout
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrChecksum _ as HErrChecksum
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrVersionMismatch _ as HErrVersionMismatch
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidMapping _ as HErrInvalidMapping
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalid _ as HErrInvalid
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDatabaseNotOpen _ as HErrDatabaseNotOpen
  wp_apply wp_GlobalAlloc (V := GoInterface) trySolo _ as HtrySolo
  wp_apply (_root_.Perennial.encoding.hex.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.log _root_.Perennial.log.initialize'
      EtcdGrove.ExternalInit.log _root_.Perennial.log.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.go_etcd_io.bbolt.internal.freelist.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.go_etcd_io.bbolt.internal.common.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.go_etcd_io.bbolt.errors.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.golang_org.x.sys.unix.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.«unsafe» _root_.Perennial.«unsafe».initialize'
      EtcdGrove.ExternalInit.unsafe_ _root_.Perennial.«unsafe».wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.syscall.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of trySolo))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xS #MS
  wp_apply (opaqueInitsOk DefaultOptions.init (by mem_tac))
  -- translated initializer of ErrDatabaseNotOpen))
  try wp_auto
  ihave #Hev : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd6
  unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars go_etcd_io.bbolt.errors.bboltErrVar
  icases Hev with ⟨%_, #HvErrBucketNotFound, %_, ⟨%vErrDatabaseNotOpen, #HvErrDatabaseNotOpen, %_, #-⟩, ⟨%vErrInvalid, #HvErrInvalid, %_, #-⟩, ⟨%vErrInvalidMapping, #HvErrInvalidMapping, %_, #-⟩, ⟨%vErrVersionMismatch, #HvErrVersionMismatch, %_, #-⟩, ⟨%vErrChecksum, #HvErrChecksum, %_, #-⟩, ⟨%vErrTimeout, #HvErrTimeout, %_, #-⟩, ⟨%vErrTxNotWritable, #HvErrTxNotWritable, %_, #-⟩, ⟨%vErrTxClosed, #HvErrTxClosed, %_, #-⟩, ⟨%vErrDatabaseReadOnly, #HvErrDatabaseReadOnly, %_, #-⟩, ⟨%vErrFreePagesNotLoaded, #HvErrFreePagesNotLoaded, %_, #-⟩, ⟨%vErrBucketExists, #HvErrBucketExists, %_, #-⟩, ⟨%vErrBucketNameRequired, #HvErrBucketNameRequired, %_, #-⟩, ⟨%vErrKeyRequired, #HvErrKeyRequired, %_, #-⟩, ⟨%vErrKeyTooLarge, #HvErrKeyTooLarge, %_, #-⟩, ⟨%vErrValueTooLarge, #HvErrValueTooLarge, %_, #-⟩, ⟨%vErrMaxSizeReached, #HvErrMaxSizeReached, %_, #-⟩, ⟨%vErrIncompatibleValue, #HvErrIncompatibleValue, %_, #-⟩, ⟨%vErrSameBuckets, #HvErrSameBuckets, %_, #-⟩, ⟨%vErrDifferentDB, #HvErrDifferentDB, %_, #-⟩, -⟩
  -- translated initializer of ErrInvalid))
  -- translated initializer of ErrInvalidMapping))
  -- translated initializer of ErrVersionMismatch))
  -- translated initializer of ErrChecksum))
  -- translated initializer of ErrTimeout))
  -- translated initializer of ErrTxNotWritable))
  -- translated initializer of ErrTxClosed))
  -- translated initializer of ErrDatabaseReadOnly))
  -- translated initializer of ErrFreePagesNotLoaded))
  -- translated initializer of ErrBucketNotFound))
  -- translated initializer of ErrBucketExists))
  -- translated initializer of ErrBucketNameRequired))
  -- translated initializer of ErrKeyRequired))
  -- translated initializer of ErrKeyTooLarge))
  -- translated initializer of ErrValueTooLarge))
  -- translated initializer of ErrIncompatibleValue))
  -- translated initializer of discardLogger))
  try wp_auto
  wp_alloc lg as Hlg
  try wp_auto
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrIncompatibleValue))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrValueTooLarge))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrKeyTooLarge))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrKeyRequired))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrBucketNameRequired))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrBucketExists))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrBucketNotFound))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrFreePagesNotLoaded))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrDatabaseReadOnly))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrTxClosed))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrTxNotWritable))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrTimeout))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrChecksum))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrVersionMismatch))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrInvalidMapping))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrInvalid))
  -- translated initializer of _root_.Perennial.go_etcd_io.bbolt.errors.ErrDatabaseNotOpen))
  try wp_auto
  ipersist HdiscardLogger
  iframe Hown
  is_pkg_init_finish
  isplitr
  · ipureintro; exact isPanic_intoVal _
  imodintro
  imodintro
  isplitr
  · ipureintro; exact ⟨runtime.GOOS_linux, runtime.GOARCH_amd64⟩
  iexists _
  iexact HdiscardLogger

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.bbolt get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.bbolt

end init

end Perennial
