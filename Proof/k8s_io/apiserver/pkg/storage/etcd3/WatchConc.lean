/-
Lean-first (no Rocq counterpart).

# The etcd3 watcher's concurrent processing branch: its channels (k8s 7f-5b)

`notes/k8s-7f5b-draft.md` §3. With `ConcurrentWatchObjectDecode` on, `concurrentProcessEvents` starts a
scheduler and a collector (`watcher.go:577-660`): the scheduler takes each raw event from
`incomingEventChan`, makes a response channel `rc` (capacity 1), queues it on `processingQueue` (in the
incoming order) and starts a goroutine that `transform`s the event and sends the result on `rc`; the
collector takes the response channels in order and sends each result as the serial goroutine does.
Here:

- `kResOf`: what `transform` returns for the raw event `r` at `σ` (`nil` for a filtered event, else
  an owned `watch.Event` holding its model);
- `kRcElem`: the response channel's element (an SPSC: producer the per-event goroutine, consumer the
  collector; never closed), an owned `*processingResult` with `transform`'s result and no error;
- `kQElem`: `processingQueue`'s `i`-th element (an SPSC: producer the scheduler, consumer the
  collector; never closed): the `i`-th element of `incomingEventChan` (`kInElem`'s facts, with the raw
  event `r` and its state `σ` exposed) and the consumer half of a response channel for `r` at `σ`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchCons

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE go_etcd_io.etcd.server.v3.etcdserver

section conc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {Obj : Type} [DecidableEq Obj]

/-- **`transform`'s result `res` for the raw event `r` at `σ`**: `nil` when it is filtered out, else
an owned `watch.Event` holding its model (`transform.spec`'s post). -/
def kResOf (c : StoreCfg GF Obj) (W : WatchSpec Obj) (sel : Obj → Bool) (emp : Bool) (σ : KVState)
    (r : KRaw) (res : Loc) : IProp GF :=
  match kRawToEv c.S.dec sel emp c.S.zero σ r with
  | none => iprop(⌜res = null⌝)
  | some e => iprop(∃ v : k8s_io.apimachinery.pkg.watch.Event, res ↦ v ∗ wevAt c.S W v e)

/-- **A response channel's element** (its only one): an owned `*processingResult` holding
`transform`'s result for `r` at `σ` and no error. -/
def kRcElem (c : StoreCfg GF Obj) (W : WatchSpec Obj) (sel : Obj → Bool) (emp : Bool) (σ : KVState)
    (r : KRaw) : Int → Loc → IProp GF :=
  fun _ v => iprop(∃ res : Loc,
    v ↦ k8s_io.apiserver.pkg.storage.etcd3.processingResult.mk res GoInterface.nil ∗
    kResOf c W sel emp σ r res)

/-- **`processingQueue`'s `i`-th element**: the `i`-th element of `incomingEventChan` (`kInElem`'s
body, the raw event `r` at `σ` exposed) and the consumer half of the response channel `rc`, whose
element is `transform`'s result for `r` at `σ`. -/
def kQElem [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (i : Int) (rc : Loc) : IProp GF :=
  iprop(∃ (p : Loc) (r : KRaw) (raws : List KRaw) (lb lb0 st : Nat) (σ σ0 : KVState)
      (γrc : SpscNames),
    eventAt σ p r ∗ ⌜raws.length = i.toNat⌝ ∗
    ([∗list] j ↦ r' ∈ raws ++ [r], monoListIdxOwn γ.raws j r') ∗
    □ Q lb σ ∗ □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st⌝ ∗ ⌜kRawStreamSub inS m σ st (raws ++ [r])⌝ ∗
    (⌜kRawStreamOk inS m σ st (raws ++ [r])⌝ ∨ kCancelled γ cd ∨ kProcExited γ) ∗
    isSpsc γrc rc (kRcElem c W sel emp σ r) (fun _ => iprop(False)) ∗
    spscConsumer γrc ([] : List Loc))

end conc

end k8s
end EtcdGrove
end Perennial
