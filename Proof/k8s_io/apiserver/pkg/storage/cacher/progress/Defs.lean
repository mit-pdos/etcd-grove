/-
**The watch cache's progress requester, as the specs see it** (KEP-6404, `notes/kep-6404-plan.md`;
2026-10-26). Lean-first (no Rocq counterpart).

`ConditionalProgressRequester` (`progress/watch_progress.go`) counts the requests waiting for the
watch cache to be fresh (`waiting`, under `mux`), and its loop (`Run`) asks etcd for a progress
notification while there are some. `isPR pr`: its mutex guards the counter and the `stopped` flag
(any values), and `cond` is a condition variable over the mutex (`NewConditionalProgressRequester`:
`sync.NewCond(&pr.mux)`).
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.storage.cacher.progress
public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher.progress

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The requester's lock invariant: its counter and flag. -/
def prLockInv (pr : Loc) : IProp GF :=
  iprop(∃ (n : w64) (b : Bool),
    structFieldRef ConditionalProgressRequester go!"waiting" pr ↦ n ∗
    structFieldRef ConditionalProgressRequester go!"stopped" pr ↦ b)

/-- **A progress requester** (persistent; see the file header). -/
def isPR (pr : Loc) : IProp GF :=
  iprop(∃ c : Loc, structFieldRef ConditionalProgressRequester go!"cond" pr ↦□ c ∗
    sync.isCond c (interface.mk (go.GoType.PointerType sync.Mutex.ty)
      #(structFieldRef ConditionalProgressRequester go!"mux" pr)) ∗
    sync.isMutex (structFieldRef ConditionalProgressRequester go!"mux" pr) (prLockInv pr))

instance isPR_persistent (pr : Loc) : Persistent (isPR (GF := GF) pr) := by
  unfold isPR; infer_instance

end defs

end cacher
end EtcdGrove
end Perennial
