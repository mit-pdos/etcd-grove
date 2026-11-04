/-
**The shared index informer as an object** (`shared_informer.go`'s `*sharedIndexInformer`): what
its own methods' specs are stated with (internal to client-go's proofs; clients see the informer
through `isInformer`, `InformerApi.lean`). Lean-first; the DaemonSet run's track A. A first cut,
for the Stage 3 stubs: the proofs of `NewSharedIndexInformerWithOptions` and `RunWithContext` fix
the lock's resource.

* `syncedChOk ch γi` (persistent): the informer's `synced` channel, closed once its controller has
  synced (`RunWithContext`'s third goroutine), broadcasting the first list's facts
  (`syncedFacts γi true`): `HasSynced`'s non-blocking receive.
* `siiPre I`: the informer invariant's halves its goroutines will own, held until the start: the
  reflector's last version (none), the processing goroutine's popped deltas (none) and store view,
  the FIFO's lock halves (`fifoPre`: `I.γf.st`/`sy`, allocated before the FIFO, at the initial
  queue), as `infInv_alloc` (`InformerAlloc.lean`) gives them.
* `siiLocked s I`: `startedLock`'s resource: `started`, `stopped` (only once started),
  `controller`, the not-started token's start-lock half at `started` (`nsLock`), and `siiPre I`
  until the start.
* `siiAt s γa cfg r I Fam` (persistent): the informer's fixed fields (its store `storeVal I`, its
  list-watch, of the model server's resource `r` (`lwOk`), its key function, its `synced`
  channel), its processor and mutation detector (`isSII`), the store and invariant (`infView`), the
  reader pool (`infReaders`), the lock.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerAlloc
public import Proof.k8s_io.client_go.tools.cache.SIIDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI apimodel cache k8s_io.client_go.tools.cache

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The informer's `synced` channel** (persistent): see the file header. -/
def syncedChOk (ch : GoChan) (γi : InfNames) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan ch γc (syncedFacts γi true) .Unknown)

/-- **The invariant's halves the informer's goroutines will own**, held until the start. -/
def siiPre (I : InfH) : IProp GF :=
  iprop(reflLast I.γi none ∗
    ghostVar I.γi.pop (1 : Qp).half (([] : List FD), false) ∗
    (∃ fn : GMap GoString Nat, ghostVar I.γi.sw (1 : Qp).half (⟨∅, [], fn⟩ : cache.St)) ∗
    fifoPre I.γf.st I.γf.sy)

/-- **`startedLock`'s resource.** -/
def siiLocked (s : Loc) (I : InfH) : IProp GF :=
  iprop(∃ (started stopped : Bool) (c : Controller),
    s.[sharedIndexInformer, go!"started"] ↦ started ∗
    s.[sharedIndexInformer, go!"stopped"] ↦ stopped ∗
    s.[sharedIndexInformer, go!"controller"] ↦ c ∗
    ⌜stopped = true → started = true⌝ ∗ nsLock I.γi.ns started ∗
    (if started then iprop(True) else siiPre I))

/-- **The informer `s`** (persistent): see the file header. -/
def siiAt (s : Loc) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res)
    (I : InfH) (Fam : Nat → Fn GF) : IProp GF :=
  iprop(∃ (p : Loc) (sch : GoChan) (lw : GoInterfaceOk) (q : Loc),
    s.[sharedIndexInformer, go!"indexer"] ↦□ (storeVal I : Indexer) ∗
    s.[sharedIndexInformer, go!"keyFunc"] ↦□ I.kf ∗
    s.[sharedIndexInformer, go!"synced"] ↦□ sch ∗ syncedChOk sch I.γi ∗
    s.[sharedIndexInformer, go!"listerWatcher"] ↦□ (GoInterface.ok lw : ListerWatcher) ∗
    lwOk lw γa cfg r ∗ keysOk γa ∗
    s.[sharedIndexInformer, go!"objectType"] ↦□
      (interface.mkOk (go.GoType.PointerType (resObjTy r)) #q :
        k8s_io.apimachinery.pkg.runtime.Object) ∗
    isSII s p ∗ infView γa r I Fam ∗ infReaders I r Fam ∗
    sync.isMutex (s.[sharedIndexInformer, go!"startedLock"]) (siiLocked s I))

/-- **The informer's listeners' contract on their `i`-th event** (the processor's `QP`, one for
all listeners): the informer's `i`-th event (`notifQ`), with its facts (`evFacts`). (Its delivery
from the informer's handling of a delta, `handleDeltas`, is the next step: the run's report.) -/
def infEvQ (γa : ApiNames) (r : Res) (γi : InfNames) (γe : GName) (i : Nat) (e : Ev) : IProp GF :=
  iprop(notifQ γe i e ∗ □ evFacts γa r γi e)

open Iris.ProofMode in
/-- **A listener's contract weakens with its events' contract.** -/
theorem lhOk_mono (h : GoInterface) (H : List Ev → IProp GF) (Q Q' : Nat → Ev → IProp GF)
    (hQ : ∀ i e, Q i e ⊢ Q' i e) : lhOk h H Q' ⊢ lhOk h H Q := by
  unfold lhOk
  iintro ⟨%i, %hi, #HA, #HU, #HD⟩
  iexists i
  isplitr
  · ipureintro; exact hi
  isplitr
  · iintro !> %evs %o %b %Φ !> ⟨HH, HQ⟩ HΦ
    ihave HQ' := (hQ _ _) $$ HQ
    iapply HA $$ [HH HQ'] HΦ
    iframe
  isplitr
  · iintro !> %evs %old %new %Φ !> ⟨HH, HQ⟩ HΦ
    ihave HQ' := (hQ _ _) $$ HQ
    iapply HU $$ [HH HQ'] HΦ
    iframe
  · iintro !> %evs %o %Φ !> ⟨HH, HQ⟩ HΦ
    ihave HQ' := (hQ _ _) $$ HQ
    iapply HD $$ [HH HQ'] HΦ
    iframe

open Iris.ProofMode in
/-- **A handler meeting the informer API's contract is a listener's handler** of the informer's
events with their facts. -/
theorem handlerSpec_lhOk (γa : ApiNames) (r : Res) (γi : InfNames) (γe : GName) (h : GoInterface)
    (H : List Ev → IProp GF) : handlerSpec γa r γi h H ⊢ lhOk h H (infEvQ γa r γi γe) := by
  unfold handlerSpec
  apply lhOk_mono
  intro i e
  unfold infEvQ
  iintro ⟨-, #He⟩
  iexact He

end defs

end informer
end EtcdGrove
end Perennial
