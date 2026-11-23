/-
Package `proxy`'s definitions behind the batch store's sealed slots (`isStore`, `storeHas`).

Changed against the lab: the map is `sync.Map` with the hypotheses' vocabulary (`Hyp.lean`'s
`MapVocab`, packed in `isStoreDef` with its `MapHyp`), in place of the lab's syncmap model, its
registry and its assumptions (`storeAssm`).
-/
module

public import Dsverify.Proof.raxos.ReplicaDefs
public import Dsverify.Proof.raxos.Hyp
public import Dsverify.Proof.raxos.StoreInst

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.sync (MapVocab MapHyp strKey)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def storeN : Namespace := ndot raxosN "store"

/-- A store entry: id `x` holds (an interface holding) a registered, well-formed batch with
that id. -/
def storeEnt (γ : QNames) (x : GoString) (v : GoInterface) : IProp GF :=
  iprop(∃ (cbv : raxos.proto.client.ClientBatch) (b : Batch),
    ⌜v = interface.mkOk raxos.proto.client.ClientBatch.ty #cbv ∧ b.id = x ∧ batchFit b⌝ ∗
    repCBVal cbv .discard b ∗ batchReg γ x b)

instance repCSingle_timeless (l : Loc) (dq : DFrac) (m : GoString) :
    Timeless (repCSingle (GF := GF) l dq m) := by
  unfold repCSingle; infer_instance

instance repCSingle_discard_persistent (l : Loc) (m : GoString) :
    Persistent (repCSingle (GF := GF) l .discard m) := by
  unfold repCSingle; infer_instance

instance repCBVal_discard_persistent (x : raxos.proto.client.ClientBatch) (b : Batch) :
    Persistent (repCBVal (GF := GF) x .discard b) := by
  unfold repCBVal repList repCSingle; infer_instance

instance repCB_discard_persistent (l : Loc) (b : Batch) :
    Persistent (repCB (GF := GF) l .discard b) := by
  unfold repCB; infer_instance

instance storeEnt_timeless (γ : QNames) (x : GoString) (v : GoInterface) :
    Timeless (storeEnt (GF := GF) γ x v) := by
  unfold storeEnt repCBVal repList batchReg; infer_instance

instance storeEnt_persistent (γ : QNames) (x : GoString) (v : GoInterface) :
    Persistent (storeEnt (GF := GF) γ x v) := by
  unfold storeEnt; infer_instance

/-- The store's invariant: the map's contents `M`, each entry registered; the ids known to be
there (`γs`'s persistent elements) are in `M`. -/
def storeInv (MV : MapVocab GF) (γ : QNames) (γs : GName) (m : Loc) : IProp GF :=
  iprop(∃ (M : GMap GoString GoInterface) (S : GMap GoString Unit),
    MV.own m M ∗ ghostMapAuth γs 1 S ∗
    ([∗map] x ↦ u ∈ S, ghostMapElem γs x .discard u) ∗ ⌜∀ x, (S !! x).isSome → (M !! x).isSome⌝ ∗
    [∗map] x ↦ v ∈ M, storeEnt (GF := GF) γ x v)

end defs

end Perennial.raxos

namespace Perennial.raxos
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.sync (MapVocab MapHyp strKey)

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def isStoreDef (γ : QNames) (γs : GName) (cb : Loc) : IProp GF :=
  iprop(∃ MV : MapVocab GF, ⌜MapHyp MV⌝ ∗
    ⌜cb.[ClientBatchStore, go!"clientBatches"] ≠ null⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    inv storeN (storeInv MV γ γs (cb.[ClientBatchStore, go!"clientBatches"])))

instance isStoreDef_persistent (γ : QNames) (γs : GName) (cb : Loc) :
    Persistent (isStoreDef (GF := GF) γ γs cb) := by
  unfold isStoreDef; infer_instance

def storeHasDef (γs : GName) (x : GoString) : IProp GF := ghostMapElem γs x .discard ()

instance storeHasDef_persistent (γs : GName) (x : GoString) :
    Persistent (storeHasDef (GF := GF) γs x) := by
  unfold storeHasDef; infer_instance

/-- The ids known to be in the store: one more, if the map has it. -/
theorem storeHas_get (γs : GName) (M : GMap GoString GoInterface) (S : GMap GoString Unit)
    (x : GoString) (hM : (M !! x).isSome) (Hsub : ∀ y, (S !! y).isSome → (M !! y).isSome) :
    ⊢@{IProp GF} ghostMapAuth γs 1 S -∗ ([∗map] y ↦ u ∈ S, ghostMapElem γs y .discard u) ==∗
      ∃ S' : GMap GoString Unit, ghostMapAuth γs 1 S' ∗
        ([∗map] y ↦ u ∈ S', ghostMapElem γs y .discard u) ∗
        ⌜∀ y, (S' !! y).isSome → (M !! y).isSome⌝ ∗ storeHasDef γs x := by
  iintro Hauth #Hels
  cases hS : S !! x with
  | some u =>
    ihave #Hx := BigSepM.bigSepM_lookup (Φ := fun y u => ghostMapElem (GF := GF) γs y .discard u)
      (show PartialMap.get? S x = some u from hS) $$ Hels
    imodintro
    iexists S
    iframe Hauth Hels
    isplitr
    · ipureintro; exact Hsub
    unfold storeHasDef
    iexact Hx
  | none =>
    imod ghost_map_insert_persist x () hS $$ Hauth with ⟨Hauth, #Hx⟩
    imodintro
    iexists S.insert x ()
    iframe Hauth
    isplitl []
    · iapply (BigSepM.bigSepM_insert (Φ := fun y u => ghostMapElem (GF := GF) γs y .discard u)
        (show PartialMap.get? S x = none from hS)).2
      iframe Hx Hels
    isplitr
    · ipureintro
      intro y hy
      by_cases hxy : y = x
      · subst hxy; exact hM
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxy)] at hy
        exact Hsub y hy
    unfold storeHasDef
    iexact Hx

end defs2
end Perennial.raxos
