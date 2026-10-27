/-
The informer's processing of a delta (`controller.go`'s `processDeltas`, the shared informer's
`handleDeltas`): what its specs are stated with. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md`.

* `Ev`: a handler event (`OnAdd(obj, isInInitialList)`, `OnUpdate(old, new)`, `OnDelete(obj)`).
* `storeWriter γ SW`: the client's exclusive writer view `SW σ` of the store (the store is at `σ`
  and nobody else writes it: the informer's `processDeltas` runs under `blockDeltas`, the store's
  only writer), with an accessor that hands out the store's state for one of its logically atomic
  operations and takes the new state back. Readers (the listers) linearize through the client's
  invariant, not through `SW`.
* `handlerOk OK h H`: the handler `h` (a `ResourceEventHandler`) takes each event from `H evs` to
  `H (evs ++ [e])` (`H`: the client's view of the events delivered so far; for the shared informer,
  the processor's distribution, `shared_informer.go`).
* `stepFD`: what processing one queued delta does: the store's next state and the handler's events
  (`ReplacedAll`'s deletions in some order: `ListKeys`' map order).
-/
module

public import Proof.k8s_io.client_go.tools.cache.FIFODefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- A handler event. -/
inductive Ev [FfiSyntax] where
  | add (o : GoInterface) (b : Bool)
  | update (old new : GoInterface)
  | delete (o : GoInterface)

section model
variable [FfiSyntax] [GoGlobalContext]

/-- The tombstone of the key `k` whose last known object is `o` (`DeletedFinalStateUnknown`). -/
def tombstone (k : GoString) (o : GoInterface) : GoInterface :=
  interface.mkOk DeletedFinalStateUnknown.ty #(DeletedFinalStateUnknown.mk k o)

/-- The event of storing `o` at key `k` over the items `it`: an update of the old object if there
was one, an add otherwise. -/
def putEv (it : Items) (k : GoString) (o : GoInterface) (b : Bool) : Ev :=
  if k ∈ it then .update (objAt it k) o else .add o b

/-- A relist's event for storing `o` at key `k` (`processReplacedAllInfo`: an update when the old
object is not `nil`, an add otherwise). -/
def putEvR (it : Items) (k : GoString) (o : GoInterface) (b : Bool) : Ev :=
  if objAt it k ≠ interface.nil then .update (objAt it k) o else .add o b

/-- **One queued delta processed** (`processDeltas` on `Deltas{d}`), at the store's state `σ`: the
store's next state `σ'` and the events `evs`, the objects keyed by `KF` with versions `rvOf`. -/
def stepFD (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (b : Bool)
    (σ : St) : FD → St → List Ev → Prop
  | .obj t o, σ', evs =>
      (t = go!"Deleted" ∧ σ' = σ.delete (KF o) (rvOfObj rvOf o) ∧ evs = [.delete o]) ∨
      (t ≠ go!"Deleted" ∧ σ' = σ.update (KF o) o (rvOf o) ∧ evs = [putEv σ.items (KF o) o b])
  | .replaced objs rv, σ', evs => σ' = σ.replace (keyedItems KF objs) rv ∧
      ∃ dks : List GoString, dks.Nodup ∧
        (∀ k, k ∈ dks ↔ k ∈ σ.items ∧ k ∉ objs.map KF) ∧
        evs = dks.map (fun k => Ev.delete (tombstone k (objAt σ.items k))) ++
          objs.map (fun x => putEvR σ.items (KF x) x b)
  | .bookmark rv, σ', evs => σ' = σ.bookmark rv ∧ evs = []

/-- The objects of a queued delta. -/
def FD.objs : FD → List GoInterface
  | .obj _ o => [o]
  | .replaced objs _ => objs
  | .bookmark _ => []

/-- The delta types the atomic FIFO queues for an object (`RealFIFO.Add`/`Update`/`Delete`). -/
def FD.kindOk : FD → Prop
  | .obj t _ => t = go!"Added" ∨ t = go!"Updated" ∨ t = go!"Deleted"
  | _ => True

end model

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The store's exclusive writer** (persistent): from `SW σ`, the store's state `σ` for one
atomic operation, and `SW σ'` back for its new state `σ'`. -/
def storeWriter (γ : TsNames) (SW : St → IProp GF) : IProp GF :=
  iprop(□ ∀ σ : St, SW σ ={⊤, ∅}=∗ storeSt γ σ ∗ (∀ σ' : St, storeSt γ σ' ={∅, ⊤}=∗ SW σ'))

instance storeWriter_persistent (γ : TsNames) (SW : St → IProp GF) :
    Persistent (storeWriter γ SW) := by
  unfold storeWriter; infer_instance

open Iris.ProofMode in
/-- **The exclusive writer's step**: it discharges a store operation's atomic update at its
state `σ`, the store becoming `f σ`. -/
theorem writer_step (γ : TsNames) (SW : St → IProp GF) (σ : St) (f : St → St) (K : St → IProp GF) :
    ⊢ storeWriter γ SW -∗ SW σ -∗ (SW (f σ) -∗ K σ) -∗
      |={⊤ \ ∅, ∅}=> ∃ σ', storeSt γ σ' ∗ (storeSt γ (f σ') ={∅, ⊤ \ ∅}=∗ K σ') := by
  iintro #Hw HSW HK
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold storeWriter at Hw
  ihave Hacc := Hw $$ %σ HSW
  imod Hacc with ⟨Hst, Hback⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  ihave Hb := Hback $$ %(f σ) Hst
  imod Hb with HSW
  imodintro
  iapply HK $$ HSW

open Iris.ProofMode in
/-- **The exclusive writer's read**: a reader's atomic update at its state `σ`, unchanged. -/
theorem writer_read (γ : TsNames) (SW : St → IProp GF) (σ : St) (K : St → IProp GF) :
    ⊢ storeWriter γ SW -∗ SW σ -∗ (SW σ -∗ K σ) -∗
      |={⊤ \ ∅, ∅}=> ∃ σ', storeSt γ σ' ∗ (storeSt γ σ' ={∅, ⊤ \ ∅}=∗ K σ') :=
  writer_step γ SW σ id K

/-- What `OnDelete` is given: an object meeting `OK`, or a tombstone of one (or of `nil`). -/
def delOk (OK : GoInterface → IProp GF) (o : GoInterface) : IProp GF :=
  iprop(□ OK o ∨ ∃ (k : GoString) (x : GoInterface), ⌜o = tombstone k x⌝ ∗ okNil OK x)

instance delOk_persistent (OK : GoInterface → IProp GF) (o : GoInterface) :
    Persistent (delOk OK o) := by
  unfold delOk; infer_instance

/-- **The handler's contract** (persistent): each method call takes the delivered events `H evs`
to `H (evs ++ [e])`. -/
def handlerOk (OK : GoInterface → IProp GF) (h : GoInterface) (H : List Ev → IProp GF) :
    IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜h = interface.ok i⌝ ∗
    □ (∀ (evs : List Ev) (o : GoInterface) (b : Bool), {{ H evs ∗ □ OK o }}
        (App (App (Val #(methods i.ty go!"OnAdd" i.v)) (Val #o)) (Val #b))
        {{ RET #(); H (evs ++ [Ev.add o b]) }}) ∗
    □ (∀ (evs : List Ev) (old new : GoInterface), {{ H evs ∗ okNil OK old ∗ □ OK new }}
        (App (App (Val #(methods i.ty go!"OnUpdate" i.v)) (Val #old)) (Val #new))
        {{ RET #(); H (evs ++ [Ev.update old new]) }}) ∗
    □ (∀ (evs : List Ev) (o : GoInterface), {{ H evs ∗ delOk OK o }}
        (App (Val #(methods i.ty go!"OnDelete" i.v)) (Val #o))
        {{ RET #(); H (evs ++ [Ev.delete o]) }}))

instance handlerOk_persistent (OK : GoInterface → IProp GF) (h : GoInterface)
    (H : List Ev → IProp GF) : Persistent (handlerOk OK h H) := by
  unfold handlerOk; infer_instance

end defs

end cache
end EtcdGrove
end Perennial
