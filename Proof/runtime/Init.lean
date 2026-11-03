/-
Package initialization of `runtime`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Perennial.Proof.runtime.Base
public import Proof.internal.runtime.atomic.Init
public import Proof.internal.runtime.sys.Init
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
namespace runtime
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `runtime`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([cgo_yield.init,
        containermaxprocs.init,
        debugPinnerKeepUnpin.init,
        boundsErrorFmts.init,
        boundsNegErrorFmts.init,
        fastlog2Table.init,
        inf.init,
        dumphdr.init,
        itabTableInit.init,
        itabTable.init,
        uint16Eface.init,
        uint32Eface.init,
        uint64Eface.init,
        stringEface.init,
        sliceEface.init,
        uint16Type.init,
        uint32Type.init,
        uint64Type.init,
        stringType.init,
        sliceType.init,
        emptyTypeAssertCache.init,
        emptyInterfaceSwitchCache.init,
        lockNames.init,
        lockPartialOrder.init,
        maps_errNilAssign.init,
        useCheckmark.init,
        cleanupFnPtrMask.init,
        adviseUnused.init,
        metricsSema.init,
        finalizer1.init,
        gcMarkWorkerModeStrings.init,
        oneptrmask.init,
        mSpanStateNames.init,
        levelBits.init,
        levelShift.init,
        levelLogPages.init,
        MemProfileRate.init,
        goroutineProfile.init,
        minOffAddr.init,
        maxOffAddr.init,
        doubleCheckReadMemStats.init,
        pdEface.init,
        pdType.init,
        epfd.init,
        haveHighResSleep.init,
        procAuxv.init,
        sysTHPSizePath.init,
        urandom_dev.init,
        sigset_all.init,
        shiftError.init,
        divideError.init,
        overflowError.init,
        floatError.init,
        memoryError.init,
        simdImmError.init,
        rangeDoneError.init,
        rangePanicError.init,
        rangeExhaustedError.init,
        rangeMissingPanicError.init,
        panicnil.init,
        pinnerLeakPanic.init,
        asyncPreemptStack.init,
        minhexdigits.init,
        casgstatusAlwaysTrack.init,
        stwReasonStrings.init,
        worldsema.init,
        gcsema.init,
        forcegcperiod.init,
        updatemaxprocs.init,
        traceback_cache.init,
        dbgvars.init,
        waitReasonStrings.init,
        isWaitingForSuspendG.init,
        isIdleInSynctest.init,
        sigsetAllExiting.init,
        sigtable.init,
        stackPoisonCopy.init,
        maxstacksize.init,
        maxstackceiling.init,
        ptrnames.init,
        startingStackSize.init,
        intArgRegs.init,
        traceAdvanceSema.init,
        traceShutdownSema.init,
        gStatusStrings.init,
        traceBlockReasonStrings.init,
        traceGoStopReasonStrings.init,
        mallocScanTable.init,
        mallocNoScanTable.init,
        chansendpc.init,
        chanrecvpc.init,
        adjustSignalStack2Indirect.init,
        vdsoLinuxVersion.init,
        vdsoSymbolKeys.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `runtime`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2», init.«3», init.«4», init.«5», init.«6», init.«7», init.«8»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end runtime
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.runtime.Assumptions]

namespace runtime

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.runtime get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.runtime }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.internal.runtime.atomic.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.internal.runtime.sys.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk cgo_yield.init (by mem_tac))
  wp_apply (opaqueInitsOk containermaxprocs.init (by mem_tac))
  wp_apply (opaqueInitsOk debugPinnerKeepUnpin.init (by mem_tac))
  wp_apply (opaqueInitsOk boundsErrorFmts.init (by mem_tac))
  wp_apply (opaqueInitsOk boundsNegErrorFmts.init (by mem_tac))
  wp_apply (opaqueInitsOk fastlog2Table.init (by mem_tac))
  wp_apply (opaqueInitsOk inf.init (by mem_tac))
  wp_apply (opaqueInitsOk dumphdr.init (by mem_tac))
  wp_apply (opaqueInitsOk itabTableInit.init (by mem_tac))
  wp_apply (opaqueInitsOk itabTable.init (by mem_tac))
  wp_apply (opaqueInitsOk uint16Eface.init (by mem_tac))
  wp_apply (opaqueInitsOk uint32Eface.init (by mem_tac))
  wp_apply (opaqueInitsOk uint64Eface.init (by mem_tac))
  wp_apply (opaqueInitsOk stringEface.init (by mem_tac))
  wp_apply (opaqueInitsOk sliceEface.init (by mem_tac))
  wp_apply (opaqueInitsOk uint16Type.init (by mem_tac))
  wp_apply (opaqueInitsOk uint32Type.init (by mem_tac))
  wp_apply (opaqueInitsOk uint64Type.init (by mem_tac))
  wp_apply (opaqueInitsOk stringType.init (by mem_tac))
  wp_apply (opaqueInitsOk sliceType.init (by mem_tac))
  wp_apply (opaqueInitsOk emptyTypeAssertCache.init (by mem_tac))
  wp_apply (opaqueInitsOk emptyInterfaceSwitchCache.init (by mem_tac))
  wp_apply (opaqueInitsOk lockNames.init (by mem_tac))
  wp_apply (opaqueInitsOk lockPartialOrder.init (by mem_tac))
  wp_apply (opaqueInitsOk maps_errNilAssign.init (by mem_tac))
  wp_apply (opaqueInitsOk useCheckmark.init (by mem_tac))
  wp_apply (opaqueInitsOk cleanupFnPtrMask.init (by mem_tac))
  wp_apply (opaqueInitsOk adviseUnused.init (by mem_tac))
  wp_apply (opaqueInitsOk metricsSema.init (by mem_tac))
  wp_apply (opaqueInitsOk finalizer1.init (by mem_tac))
  wp_apply (opaqueInitsOk gcMarkWorkerModeStrings.init (by mem_tac))
  wp_apply (opaqueInitsOk oneptrmask.init (by mem_tac))
  wp_apply (opaqueInitsOk mSpanStateNames.init (by mem_tac))
  wp_apply (opaqueInitsOk levelBits.init (by mem_tac))
  wp_apply (opaqueInitsOk levelShift.init (by mem_tac))
  wp_apply (opaqueInitsOk levelLogPages.init (by mem_tac))
  wp_apply (opaqueInitsOk MemProfileRate.init (by mem_tac))
  wp_apply (opaqueInitsOk goroutineProfile.init (by mem_tac))
  wp_apply (opaqueInitsOk minOffAddr.init (by mem_tac))
  wp_apply (opaqueInitsOk maxOffAddr.init (by mem_tac))
  wp_apply (opaqueInitsOk doubleCheckReadMemStats.init (by mem_tac))
  wp_apply (opaqueInitsOk pdEface.init (by mem_tac))
  wp_apply (opaqueInitsOk pdType.init (by mem_tac))
  wp_apply (opaqueInitsOk epfd.init (by mem_tac))
  wp_apply (opaqueInitsOk haveHighResSleep.init (by mem_tac))
  wp_apply (opaqueInitsOk procAuxv.init (by mem_tac))
  wp_apply (opaqueInitsOk sysTHPSizePath.init (by mem_tac))
  wp_apply (opaqueInitsOk urandom_dev.init (by mem_tac))
  wp_apply (opaqueInitsOk sigset_all.init (by mem_tac))
  wp_apply (opaqueInitsOk shiftError.init (by mem_tac))
  wp_apply (opaqueInitsOk divideError.init (by mem_tac))
  wp_apply (opaqueInitsOk overflowError.init (by mem_tac))
  wp_apply (opaqueInitsOk floatError.init (by mem_tac))
  wp_apply (opaqueInitsOk memoryError.init (by mem_tac))
  wp_apply (opaqueInitsOk simdImmError.init (by mem_tac))
  wp_apply (opaqueInitsOk rangeDoneError.init (by mem_tac))
  wp_apply (opaqueInitsOk rangePanicError.init (by mem_tac))
  wp_apply (opaqueInitsOk rangeExhaustedError.init (by mem_tac))
  wp_apply (opaqueInitsOk rangeMissingPanicError.init (by mem_tac))
  wp_apply (opaqueInitsOk panicnil.init (by mem_tac))
  wp_apply (opaqueInitsOk pinnerLeakPanic.init (by mem_tac))
  wp_apply (opaqueInitsOk asyncPreemptStack.init (by mem_tac))
  wp_apply (opaqueInitsOk minhexdigits.init (by mem_tac))
  wp_apply (opaqueInitsOk casgstatusAlwaysTrack.init (by mem_tac))
  wp_apply (opaqueInitsOk stwReasonStrings.init (by mem_tac))
  wp_apply (opaqueInitsOk worldsema.init (by mem_tac))
  wp_apply (opaqueInitsOk gcsema.init (by mem_tac))
  wp_apply (opaqueInitsOk forcegcperiod.init (by mem_tac))
  wp_apply (opaqueInitsOk updatemaxprocs.init (by mem_tac))
  wp_apply (opaqueInitsOk traceback_cache.init (by mem_tac))
  wp_apply (opaqueInitsOk dbgvars.init (by mem_tac))
  wp_apply (opaqueInitsOk waitReasonStrings.init (by mem_tac))
  wp_apply (opaqueInitsOk isWaitingForSuspendG.init (by mem_tac))
  wp_apply (opaqueInitsOk isIdleInSynctest.init (by mem_tac))
  wp_apply (opaqueInitsOk sigsetAllExiting.init (by mem_tac))
  wp_apply (opaqueInitsOk sigtable.init (by mem_tac))
  wp_apply (opaqueInitsOk stackPoisonCopy.init (by mem_tac))
  wp_apply (opaqueInitsOk maxstacksize.init (by mem_tac))
  wp_apply (opaqueInitsOk maxstackceiling.init (by mem_tac))
  wp_apply (opaqueInitsOk ptrnames.init (by mem_tac))
  wp_apply (opaqueInitsOk startingStackSize.init (by mem_tac))
  wp_apply (opaqueInitsOk intArgRegs.init (by mem_tac))
  wp_apply (opaqueInitsOk traceAdvanceSema.init (by mem_tac))
  wp_apply (opaqueInitsOk traceShutdownSema.init (by mem_tac))
  wp_apply (opaqueInitsOk gStatusStrings.init (by mem_tac))
  wp_apply (opaqueInitsOk traceBlockReasonStrings.init (by mem_tac))
  wp_apply (opaqueInitsOk traceGoStopReasonStrings.init (by mem_tac))
  wp_apply (opaqueInitsOk mallocScanTable.init (by mem_tac))
  wp_apply (opaqueInitsOk mallocNoScanTable.init (by mem_tac))
  wp_apply (opaqueInitsOk chansendpc.init (by mem_tac))
  wp_apply (opaqueInitsOk chanrecvpc.init (by mem_tac))
  wp_apply (opaqueInitsOk adjustSignalStack2Indirect.init (by mem_tac))
  wp_apply (opaqueInitsOk vdsoLinuxVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk vdsoSymbolKeys.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  wp_apply (initFuncsOk init.«2» (by mem_tac))
  wp_apply (initFuncsOk init.«3» (by mem_tac))
  wp_apply (initFuncsOk init.«4» (by mem_tac))
  wp_apply (initFuncsOk init.«5» (by mem_tac))
  wp_apply (initFuncsOk init.«6» (by mem_tac))
  wp_apply (initFuncsOk init.«7» (by mem_tac))
  wp_apply (initFuncsOk init.«8» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.runtime get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.runtime }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end runtime

end init

end Perennial
