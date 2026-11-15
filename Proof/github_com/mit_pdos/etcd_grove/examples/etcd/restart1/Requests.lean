/-
**What restart1's in-process calls take of their arguments** (restart S7.5, steps c and f,
2026-11-14; P1's local lemmas, `notes/restart-s7-probe.md`). Lean-first (no Rocq counterpart).

- `putRequestIs_alloc`, `rangeRequestIs_alloc`: a request the program allocates
  (`&pb.PutRequest{...}`, `&pb.RangeRequest{...}`) denotes its operation (`txn.putRequestIs`,
  `txn.rangeRequestIs`): its fields made read-only, and a put's size cache in its invariant. (The
  server's requests otherwise arrive decoded by gRPC's model.)
- `bgCtx_facts`: the context `context.WithTimeout(context.Background(), _)` returns (a child of
  `Background()`, `ctxValueFrom`) carries the library's keys (`context.libCtxOk`) and no span
  (`trace.spanCtxOk`) and no trace (`traceutil.ctxTraceIs _ none`: `traceutil.ctxTraceIs_bgFrom`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.context.LibKeys
public import Proof.context.LibKeysChain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **An allocated `*pb.PutRequest` denotes its put** (see the file header). -/
theorem putRequestIs_alloc (r : Loc) (v : etcdserverpb.PutRequest) (k val : GoString)
    (hk : sint.Z v.Key'.len < 2 ^ 63 - 1) :
    (r ↦ v : IProp GF) ∗ v.Key' ↦*□ k ∗ v.Value' ↦*□ val ⊢
      |={⊤}=> txn.putRequestIs r
        (txn.putOpOf k val v.Lease' v.PrevKv' v.IgnoreValue' v.IgnoreLease') := by
  iintro ⟨Hr, #Hk, #Hv⟩
  icases typedPointsto_not_null_dup r v _ $$ Hr with ⟨Hr, %Hnn⟩
  iStructNamed Hr
  ipersist Key
  ipersist Value
  ipersist Lease
  ipersist PrevKv
  ipersist IgnoreValue
  ipersist IgnoreLease
  imod inv_alloc (nroot .@ "txn.putSizeCache") ⊤
    iprop(∃ sc : w32, structFieldRef etcdserverpb.PutRequest go!"sizeCache" r ↦ sc)
    $$ [sizeCache] with #Hinv
  · inext; iexists v.sizeCache'; iexact sizeCache
  imodintro
  iunfold txn.putRequestIs
  isplitr; · ipureintro; exact Hnn
  iexists v.Key', v.Value', k, val, v.Lease', v.PrevKv', v.IgnoreValue', v.IgnoreLease'
  iframe #
  ipureintro; exact ⟨rfl, hk⟩

/-- **An allocated `*pb.RangeRequest` denotes its range** (see the file header). -/
theorem rangeRequestIs_alloc (r : Loc) (v : etcdserverpb.RangeRequest) (k e : GoString)
    (hk : sint.Z v.Key'.len < 2 ^ 63 - 1) :
    (r ↦ v : IProp GF) ∗ v.Key' ↦*□ k ∗ v.RangeEnd' ↦*□ e ⊢
      |={⊤}=> txn.rangeRequestIs r
        (txn.rangeOpOf k (txn.rangeEndOf v.RangeEnd' e) v.Revision' v.Limit' v.SortOrder'
          v.SortTarget' v.Serializable' v.KeysOnly' v.CountOnly' v.MinModRevision'
          v.MaxModRevision' v.MinCreateRevision' v.MaxCreateRevision') := by
  iintro ⟨Hr, #Hk, #He⟩
  icases typedPointsto_not_null_dup r v _ $$ Hr with ⟨Hr, %Hnn⟩
  iStructNamed Hr
  ipersist Key
  ipersist RangeEnd
  ipersist Limit
  ipersist Revision
  ipersist SortOrder
  ipersist SortTarget
  ipersist Serializable
  ipersist KeysOnly
  ipersist CountOnly
  ipersist MinModRevision
  ipersist MaxModRevision
  ipersist MinCreateRevision
  ipersist MaxCreateRevision
  imodintro
  iunfold txn.rangeRequestIs
  isplitr; · ipureintro; exact Hnn
  iexists v.Key', v.RangeEnd', k, e, v.Revision', v.Limit', v.SortOrder', v.SortTarget',
    v.Serializable', v.KeysOnly', v.CountOnly', v.MinModRevision', v.MaxModRevision',
    v.MinCreateRevision', v.MaxCreateRevision'
  iframe #
  ipureintro; exact ⟨rfl, hk⟩

end laws

/-- `TraceKey{}` is no `*int` key. -/
theorem traceKeyVal_notIntPtr [GooseExts] [GoGlobalContext] : _root_.Perennial.context.notIntPtrKey traceutil.traceKeyVal := by
  intro ki h
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h
  unfold go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty
  simp

section ctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **A child of `Background()` carries no trace** (`traceutil.ctxTraceIs _ none`; see the file
header): its `Value(TraceKey{})` is `Background()`'s, `nil`. -/
theorem traceutil.ctxTraceIs_bgFrom (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxValueFrom _root_.Perennial.context.backgroundCtxVal ctx ⊢
      traceutil.ctxTraceIs ctx none := by
  iintro ⟨#Hpkg, #Hf⟩
  ihave #Hv : _root_.Perennial.context.ctxValue ctx traceutil.traceKeyVal (· = interface.nil) $$ []
  · iunfold _root_.Perennial.context.ctxValueFrom at Hf
    iapply Hf
    · ipureintro; exact traceKeyVal_notIntPtr
    iapply _root_.Perennial.context.ctxValue_background
  iunfold traceutil.ctxTraceIs
  imodintro
  iintro %Φ HΦ
  wp_apply _root_.Perennial.context.ctxValue_Value ctx traceutil.traceKeyVal _ $$ [] as %w %Hw
  · iframe #
  iapply HΦ
  ipureintro; left; exact Hw

/-- **What a request context made from `Background()` carries** (see the file header). -/
theorem bgCtx_facts (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxValueFrom _root_.Perennial.context.backgroundCtxVal ctx ⊢
      context.libCtxOk ctx ∗ trace.spanCtxOk ctx ∗ traceutil.ctxTraceIs ctx none := by
  iintro ⟨#Hpkg, #Hf⟩
  isplitl []
  · iapply context.libCtxOk_bgFrom; iframe #
  isplitl []
  · iapply trace.spanCtxOk_of_spanCtxOkC
    iframe #
    iapply trace.spanCtxOkC_from _root_.Perennial.context.backgroundCtxVal ctx
    iframe #
    iunfold trace.spanCtxOkC
    iexists (· = interface.nil)
    isplitl []
    · imodintro; iintro %v %hv; ileft; ipureintro; exact hv
    iapply _root_.Perennial.context.ctxValue_background
  iapply traceutil.ctxTraceIs_bgFrom; iframe #

end ctx

end etcd_restart1
end EtcdGrove
end Perennial
