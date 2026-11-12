/-
**Laws of the weak handler context and of etcd's stream wrapper** (k8s 7f-4, step 3 of
`notes/k8s-7f4-rebaseline.md` §4). Lean-first.

* R-4: an error `srvCtxWeak`'s `"#HErrDone"` gives (`isCtxErr ∨ noLeaderErr`) is one grpc's server
  and the prometheus interceptor take (`srvErrOk`): `v3rpc.srvErrOk_of_weakErr`.
* The library facts of etcd's wrapper `*cancellableContext` `l` over the `WithCancel` child `c` of
  grpc's run context `ci`: the wrapper's `Value` is promoted from its embedded `Context` field
  (`v3rpc.ccField l ↦□ c`), so a WP fact of `c.Value` is one of the wrapper's
  (`v3rpc.valueAt_cc`); `c`'s come from `ci`'s chain forms (`context.libCtxOkC`,
  `trace.spanCtxOkC`, which grpc's model gives of a stream's run context, `srvRawStreamIs`) through
  `ctxValueFrom ci c` (`v3rpc.wp_WithCancel_cancelCtx`): `v3rpc.wrapperLibCtx`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WrapperMd
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.context.LibKeysChain
public import Proof.go_opentelemetry_io.otel.trace.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [server_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **R-4: a weak context's error after `Done` is one the gRPC layer takes**: a context error
(`applyErrIs_of_isCtxErr`, `applyErrIs_srvErrOk`) or `rpctypes.ErrGRPCNoLeader`'s value, a
`*status.Error` (`interceptorVars`' `errVarSet`). -/
theorem v3rpc.srvErrOk_of_weakErr :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      □ ∀ err : GoInterface, (context.isCtxErr err ∨ noLeaderErr err) -∗
        go_etcd_io.etcd.cache.v3.srvErrOk err := by
  iintro ⟨#Hpv, #Hpe⟩
  ihave #HCtxE := applyErrIs_of_isCtxErr $$ Hpe
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpv
  icases Hinit with ⟨-, -, -, -, #Hiv, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.interceptorVars at Hiv
  icases Hiv with ⟨-, -, -, -, #HeNoL, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeNoL
  icases HeNoL with ⟨%e, #He, #Se⟩
  iintro !> %err (#Hc | #Hn)
  · iapply applyErrIs_srvErrOk
    iapply HCtxE $$ Hc
  · iunfold noLeaderErr at Hn
    icases Hn with ⟨%e', #He', %Heq⟩
    icombine He He' gives %h
    subst Heq
    rw [← h]
    iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk
    iexact Se

/-- **A thread token lends its level 4** (k8s 7f-4 item 7: a goroutine holding a whole thread token
pays a weak context's `Err()`, `levelTok v3rpc.ctxErrLvl`, from it and takes it back). -/
theorem threadTok_lend4 (HT : 5 ≤ threadBound GF) :
    threadTok (GF := GF) ⊢ levelTok 4 ∗ (levelTok 4 -∗ threadTok) := by
  iintro H
  icases (threadTok_level0 (GF := GF)).1 $$ H with ⟨H0, H⟩
  icases (threadTokFrom_succ (GF := GF) 1 (by omega)).1 $$ H with ⟨H1, H⟩
  icases (threadTokFrom_succ (GF := GF) 2 (by omega)).1 $$ H with ⟨H2, H⟩
  icases (threadTokFrom_succ (GF := GF) 3 (by omega)).1 $$ H with ⟨H3, H⟩
  icases (threadTokFrom_succ (GF := GF) 4 (by omega)).1 $$ H with ⟨H4, H⟩
  iframe H4
  iintro H4
  iapply (threadTok_level0 (GF := GF)).2
  iframe H0
  iapply (threadTokFrom_succ (GF := GF) 1 (by omega)).2
  iframe H1
  iapply (threadTokFrom_succ (GF := GF) 2 (by omega)).2
  iframe H2
  iapply (threadTokFrom_succ (GF := GF) 3 (by omega)).2
  iframe H3
  iapply (threadTokFrom_succ (GF := GF) 4 (by omega)).2
  iframe

/-- **etcd's no-leader error is a status error** (`rpctypes.ErrGRPCNoLeader`, from the package's
error facts): what `errors.Is` takes of it (`errors.IsStatusErr.spec`). -/
theorem v3rpc.statusErrOk_of_noLeaderErr :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ⊢
      □ ∀ err : GoInterface, noLeaderErr err -∗ go_etcd_io.etcd.cache.v3.statusErrOk err := by
  iintro #Hpv
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpv
  icases Hinit with ⟨-, -, -, -, #Hiv, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.interceptorVars at Hiv
  icases Hiv with ⟨-, -, -, -, #HeNoL, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeNoL
  icases HeNoL with ⟨%e, #He, #Se⟩
  iintro !> %err #Hn
  iunfold noLeaderErr at Hn
  icases Hn with ⟨%e', #He', %Heq⟩
  icombine He He' gives %h
  subst Heq
  rw [← h]
  iexact Se

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The wrapper's promoted `Value` is its embedded context's**: `(*cancellableContext).Value(k)`
loads the `Context` field and calls its `Value(k)`. -/
theorem v3rpc.valueAt_cc (l : Loc) (c : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop) :
    (v3rpc.ccField l ↦□ (GoInterface.ok c) : IProp GF) ∗ context.valueAt c k R ⊢
      context.valueAt (v3rpc.ccCtx l) k R := by
  iintro ⟨#Hf, #Hv⟩
  unfold context.valueAt
  iintro !> %Φ HΦ
  rw [method_unfold (t := go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty)]
  wp_auto
  iapply Hv
  inext
  iexact HΦ

/-- **The wrapper has its embedded context's library values** (`libCtxOk`, the WP form). -/
theorem v3rpc.libCtxOk_cc (l : Loc) (c : GoInterfaceOk) :
    (v3rpc.ccField l ↦□ (GoInterface.ok c) : IProp GF) ∗ context.libCtxOk c ⊢
      context.libCtxOk (v3rpc.ccCtx l) := by
  iintro ⟨#Hf, #H⟩
  unfold context.libCtxOk metadata.incomingCtxOk metadata.outgoingCtxOk peer.peerCtxOk
    trace.spanValOk
  icases H with ⟨⟨%vi, %hvi, #Hi⟩, ⟨%vo, %hvo, #Ho⟩, #Hp, #Hs⟩
  isplitl []
  · iexists vi; iframe %hvi
    iapply v3rpc.valueAt_cc; iframe #
  isplitl []
  · iexists vo; iframe %hvo
    iapply v3rpc.valueAt_cc; iframe #
  isplitl []
  · iapply v3rpc.valueAt_cc; iframe #
  · iapply v3rpc.valueAt_cc; iframe #

/-- **The wrapper has its embedded context's span fact** (`trace.spanCtxOk`). -/
theorem v3rpc.spanCtxOk_cc (l : Loc) (c : GoInterfaceOk) :
    (v3rpc.ccField l ↦□ (GoInterface.ok c) : IProp GF) ∗ trace.spanCtxOk c ⊢
      trace.spanCtxOk (v3rpc.ccCtx l) := by
  iintro ⟨#Hf, #H⟩
  unfold trace.spanCtxOk
  icases H with ⟨%R, #HR, #Hv⟩
  iexists R
  iframe #
  imodintro
  iintro %Φ !> - HΦ
  rw [method_unfold (t := go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty)]
  wp_auto
  iapply Hv
  · itrivial
  inext
  iexact HΦ

variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **The library facts of etcd's stream wrapper** (step 3): the `*cancellableContext` `l` whose
`Context` field holds `c`, a child of grpc's run context `ci` by `WithCancel` (`ctxValueFrom ci c`,
`v3rpc.wp_WithCancel_cancelCtx`), has the WP-form library values and span fact that the handlers
take (`libCtxOk`, `trace.spanCtxOk`), from `ci`'s chain forms (`srvRawStreamIs`'s
`context.libCtxOkC ci`, `trace.spanCtxOkC ci`). -/
theorem v3rpc.wrapperLibCtx (l : Loc) (c ci : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      (v3rpc.ccField l ↦□ (GoInterface.ok c) : IProp GF) ∗
      _root_.Perennial.context.ctxValueFrom ci c ∗ context.libCtxOkC ci ∗ trace.spanCtxOkC ci ⊢
      context.libCtxOk (v3rpc.ccCtx l) ∗ trace.spanCtxOk (v3rpc.ccCtx l) := by
  iintro ⟨#Hpkg, #Hf, #Hfrom, #Hlib, #Hspan⟩
  ihave #Hlib' := context.libCtxOkC_from ci c $$ [$Hfrom $Hlib]
  ihave #Hspan' := trace.spanCtxOkC_from ci c $$ [$Hfrom $Hspan]
  ihave #Hl := context.libCtxOk_of_libCtxOkC c $$ [$Hpkg $Hlib']
  ihave #Hs := trace.spanCtxOk_of_spanCtxOkC c $$ [$Hpkg $Hspan']
  isplitl []
  · iapply v3rpc.libCtxOk_cc; iframe #
  · iapply v3rpc.spanCtxOk_cc; iframe #

end laws

end EtcdGrove
end Perennial
