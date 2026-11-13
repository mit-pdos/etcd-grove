/-
**The server's stream interceptor** (`v3rpc/interceptor.go`'s `newStreamInterceptor` and
`monitorLeader`; the watch slice's unit W-W, 2026-10-15): the vocabulary of their specs.
Lean-first (no Rocq counterpart).

* `v3rpc.streamsMapIs smap` (persistent): the `*streamsMap` `monitorLeader` returns: its `mu` a
  mutex whose invariant says the `streams` field holds a map (owned under the local key instance
  `v3rpc.streamKeys`, `StreamMapKey.lean`) whose every key is a `serverStreamWithCtx` (`v3rpc.sKey t
  ls l`) over a wrapper `l` with its handle (`v3rpc.ccHandle`, `InvCancellable.lean`; k8s 7f-4): the
  interceptor's require-leader branch inserts such keys, and the monitor cancels each
  (`l.Cancel(ErrGRPCNoLeader)`) and waits for its context's `Done`.
(k8s 7f-4, step 6, the user's decision of 2026-11-08) The deployment premise `v3rpc.runsNoRequireLeader`
(no client asks for a leader on a stream), which excluded the interceptor's require-leader branch, is
deleted: the branch is proved (the wrapper's handle, `srvCtxWeak`, the weak stream end
`srvRawStreamIsW`; `notes/k8s-7f4-freeze.md`), so the closed theorems no longer assume it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.StreamMapKey
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvCancellable
public import Spec.google_golang_org.grpc.metadata.FromIncomingContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- A key of the monitor's map: a `serverStreamWithCtx` over a wrapper with its handle
(persistent). -/
def v3rpc.streamKeyOk (k : GoInterface) : IProp GF :=
  iprop(∃ (t : go.GoType) (ls l : Loc) (c1 : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    ⌜k = v3rpc.sKey t ls l⌝ ∗ v3rpc.ccHandle l c1 cd)

instance v3rpc.streamKeyOk_persistent (k : GoInterface) :
    Persistent (v3rpc.streamKeyOk (GF := GF) k) := by
  unfold v3rpc.streamKeyOk; infer_instance

attribute [local instance 1100] v3rpc.streamKeys in
/-- The invariant of a `*streamsMap`'s mutex: the `streams` field holds a map (under the key
instance `v3rpc.streamKeys`) whose keys are `v3rpc.streamKeyOk` (see the file header). -/
def v3rpc.streamsMapInv (smap : Loc) : IProp GF :=
  iprop(∃ (mp : GoMap) (m : GMap GoInterface Unit),
    structFieldRef v3rpc.streamsMap go!"streams" smap ↦ mp ∗ mp ↦$ m ∗
    [∗map] k ↦ _u ∈ m, v3rpc.streamKeyOk k)

/-- **The `*streamsMap` `smap`** (persistent; see the file header). -/
def v3rpc.streamsMapIs (smap : Loc) : IProp GF :=
  sync.isMutex (structFieldRef v3rpc.streamsMap go!"mu" smap) (v3rpc.streamsMapInv smap)

instance v3rpc.streamsMapIs_persistent (smap : Loc) :
    Persistent (v3rpc.streamsMapIs (GF := GF) smap) := by
  unfold v3rpc.streamsMapIs; infer_instance

end defs

end EtcdGrove
end Perennial
