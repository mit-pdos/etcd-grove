/-
**etcd's `*cancellableContext`, the handle** (k8s 7f-4, step 4; after Addendum T-f'). Lean-first.

`newCancellableContext(parent)` (fork `673da07c8f` `server/etcdserver/api/v3rpc/interceptor.go:278`)
returns `l` with `Context: c1 = WithCancel(parent)` and `cancel`; `Cancel(reason)` stores `reason`
under `lock.Lock()` then calls `cancel()`; `Err()` reads `cancelReason` under `lock.RLock()` and
returns it if non-nil, else `c1.Err()`. The only `Cancel` callers pass `nil` (the interceptor's
`defer`) or `rpctypes.ErrGRPCNoLeader` (`monitorLeader`), so `cancelReason` is always one of them
(`v3rpc.reasonOk`).

* `v3rpc.ccReasonP l e q`: the share `q` of `cancelReason`, holding `nil` or `e` (fractional, for
  `sync.init_RWMutex_threadPoolL`).
* `v3rpc.ccHandle l c1 cd` (persistent): the fields read-only (`Context ↦□ c1`, `cancel ↦□`), `c1`
  a `*cancelCtx` (`isContext c1 cd`, `isCancelCtxOf`, for `"#HParentCC"`), `cancel`'s
  `cancelSpec`, `e` the value of `ErrGRPCNoLeader`, the lock's writer guard and its reader tokens
  in a thread pool at `v3rpc.ctxErrLvl` (Addendum T-f').
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeakLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section names
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The `lock` field of the `*cancellableContext` `l`. -/
abbrev v3rpc.ccLockF (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext go!"lock" l
/-- The `cancel` field. -/
abbrev v3rpc.ccCancelF (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext go!"cancel" l
/-- The `cancelReason` field. -/
abbrev v3rpc.ccReasonF (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext
    go!"cancelReason" l

/-- The namespace of a wrapper's reader pool. -/
abbrev v3rpc.ccPoolN : Namespace := nroot.@"v3rpcCancellablePool"

/-- A cancel reason the program stores: `nil` or `ErrGRPCNoLeader`'s value `e`. -/
def v3rpc.reasonOk (e r : GoInterface) : Prop := r = GoInterface.nil ∨ r = e

end names

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The share `q` of the wrapper's `cancelReason`**, holding `nil` or `e`. -/
def v3rpc.ccReasonP (l : Loc) (e : GoInterface) (q : Qp) : IProp GF :=
  iprop(∃ r : {r : GoInterface // v3rpc.reasonOk e r}, v3rpc.ccReasonF l ↦{DFrac.own q} r.1)

instance v3rpc.ccReasonP_fractional (l : Loc) (e : GoInterface) :
    Fractional (v3rpc.ccReasonP (GF := GF) l e) := by
  unfold v3rpc.ccReasonP
  exact fractional_exists_agree
    (fun (r : {r : GoInterface // v3rpc.reasonOk e r}) q =>
      iprop(v3rpc.ccReasonF l ↦{DFrac.own q} r.1))
    (fun r => fractional_of_dfractional (fun dq => typedPointsto (v3rpc.ccReasonF l) r.1 dq))
    (fun x y q1 q2 => by
      iintro ⟨H1, H2⟩
      icombine H1 H2 gives %H
      ipureintro; exact Subtype.ext H)

instance v3rpc.ccReasonP_timeless (l : Loc) (e : GoInterface) (q : Qp) :
    Timeless (v3rpc.ccReasonP (GF := GF) l e q) := by
  unfold v3rpc.ccReasonP; infer_instance

variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **The `*cancellableContext` `l` over `c1`, described by `cd`** (persistent; see the file
header). -/
def v3rpc.ccHandle (l : Loc) (c1 : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(∃ (c : Loc) (γ : context.ContextNames) (cancel : GoFunc) (e : GoInterfaceOk) (γp : GName),
    ⌜c1 = interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c⌝ ∗
    ⌜cd.Done_gn = γ⌝ ∗
    v3rpc.ccField l ↦□ (GoInterface.ok c1) ∗ v3rpc.ccCancelF l ↦□ cancel ∗
    context.isContext c1 cd ∗ context.isCancelCtxOf c γ iprop(True) ∗
    context.cancelSpec cancel γ iprop(True) ∗ noLeaderErr (GoInterface.ok e) ∗
    sync.isRWMutexGuard (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e)) ∗
    threadPool.isThreadPoolL v3rpc.ccPoolN v3rpc.ctxErrLvl γp
      (sync.ownRWMutex (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e))))

instance v3rpc.ccHandle_persistent (l : Loc) (c1 : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) : Persistent (v3rpc.ccHandle l c1 cd) := by
  unfold v3rpc.ccHandle; infer_instance

end defs

end EtcdGrove
end Perennial
