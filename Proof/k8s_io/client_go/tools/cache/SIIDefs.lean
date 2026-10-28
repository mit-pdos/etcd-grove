/-
The shared informer as its own event handler (`shared_informer.go`'s `sharedIndexInformer`
`OnAdd`/`OnUpdate`/`OnDelete`, which `processDeltas` calls under `blockDeltas`): what their specs,
and the discharge of `handleDeltas`' premise `handlerOk`, are stated with. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the processor and listeners).

* `infH p γp γe evs`: the informer's view of the events it has handled, `evs`: the processor's
  sender (`procSend`: every listener has been sent their notifications), a reader slot of the
  listeners' lock, and the authoritative event history `γe` (a mono list of the notifications),
  whose `i`-th element is the persistent contract of every listener's `i`-th notification
  (`notifQ γe`: "it is the informer's `i`-th event"). So a listener's handler sees exactly the
  informer's events, in order.
* `isSII s p` (persistent): the informer's processor `p` (its lock and condition variable) and
  its mutation detector, whose `AddObject` returns (`mdOk`: the dummy detector's, or the real one's
  when `KUBE_CACHE_MUTATION_DETECTOR` is set, which copies the object; the package variable
  choosing it is untranslated, C7).
* `accRet OK`: apimachinery's `meta.Accessor` returns on an object meeting `OK` or `nil`, and its
  accessor's `GetResourceVersion` returns (outside client-go; the client discharges it for its
  object types, as `rvAcc`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.ProcDefs
public import Perennial.Ghost.MonoList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **A listener's `i`-th notification's contract**: it is the informer's `i`-th event's. -/
def notifQ (γe : GName) (i : Nat) (e : Ev) : IProp GF := monoListIdxOwn γe i (notifOf e)

instance notifQ_persistent (γe : GName) (i : Nat) (e : Ev) :
    Persistent (notifQ (GF := GF) γe i e) := by
  unfold notifQ; infer_instance

/-- **The informer's view of the events it handled** (`handlerOk`'s `H`). -/
def infH (p : Loc) (γp : ProcNames) (γe : GName) (evs : List Ev) : IProp GF :=
  iprop(procSend γp (notifQ γe) evs ∗ procReader p γp ∗
    monoListAuthOwn γe 1 (evs.map notifOf))

/-- The mutation detector's `AddObject` returns. -/
def mdOk (d : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜d = interface.ok i⌝ ∗
    □ (∀ o : GoInterface, {{ True }} (App (Val #(methods i.ty go!"AddObject" i.v)) (Val #o))
        {{ RET #(); True }}))

instance mdOk_persistent (d : GoInterface) : Persistent (mdOk (GF := GF) d) := by
  unfold mdOk; infer_instance

/-- **The informer** (persistent): its processor and mutation detector. -/
def isSII (s p : Loc) : IProp GF :=
  iprop(structFieldRef sharedIndexInformer go!"processor" s ↦□ p ∗
    (∃ d : GoInterface, structFieldRef sharedIndexInformer go!"cacheMutationDetector" s ↦□ d ∗
      mdOk d) ∗
    isProc p)

instance isSII_persistent (s p : Loc) : Persistent (isSII (GF := GF) s p) := by
  unfold isSII; infer_instance

/-- **`meta.Accessor` returns** on an object meeting `OK` or `nil`, and if it gives no error, its
accessor's `GetResourceVersion` returns. -/
def accRet (OK : GoInterface → IProp GF) : IProp GF :=
  iprop(∀ o : GoInterface, {{ okNil OK o }}
    (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.api.«meta».Accessor)) (Val #o))
    {{ (m err : GoInterface), RET (PairV #m #err);
        ⌜err ≠ interface.nil⌝ ∨ (⌜err = interface.nil⌝ ∗ ∃ rv : GoString, getRVOk m rv) }})

instance accRet_persistent (OK : GoInterface → IProp GF) : Persistent (accRet OK) := by
  unfold accRet; infer_instance

end defs

end cache
end EtcdGrove
end Perennial
