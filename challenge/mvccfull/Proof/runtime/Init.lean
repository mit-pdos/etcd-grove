/-
Package initialization of `runtime`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.

And the trust-boundary assumptions `GOOS_linux` and `GOARCH_amd64`: the program runs on
linux/amd64 (`runtime.GOOS` and `runtime.GOARCH`, constants that goose leaves axiom `val`s, are
`"linux"` and `"amd64"`), as the repository's other platform facts
assume linux/amd64 (`os.Getpagesize` returns 4096, `Spec/os/Getpagesize.lean`; the Linux file
extension `fsExt`). `runtime`'s `IsPkgInit` instance is Perennial's, with the fact `True`, so the
packages that read `GOOS`/`GOARCH` state them in their own facts from these axioms (bbolt's root package,
`bboltRootInit`).
-/
module

public import Perennial.Proof.runtime.Base
public import Perennial.Proof.internal.runtime.atomic.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»
public import Proof.internal.runtime.sys.Init

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

namespace runtime

/-- **The trust boundary: the program runs on Linux.** `runtime.GOOS` is the constant
`"linux"` (Go's `GOOS` of the build; goose translates `runtime` names-only, so it is an
axiom `val` with no value). Satisfiable: `GOOS` is an uninterpreted constant. -/
axiom GOOS_linux [GooseExts] [GoGlobalContext] :
    _root_.Perennial.runtime.GOOS = #(go!"linux")

/-- **The trust boundary: the program runs on amd64.** `runtime.GOARCH` is the constant
`"amd64"` (Go's `GOARCH` of the build; an axiom `val` with no value, as `GOOS`). Satisfiable:
`GOARCH` is an uninterpreted constant. -/
axiom GOARCH_amd64 [GooseExts] [GoGlobalContext] :
    _root_.Perennial.runtime.GOARCH = #(go!"amd64")

end runtime

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.runtime.Assumptions]

namespace runtime

end runtime

end init

end Perennial
