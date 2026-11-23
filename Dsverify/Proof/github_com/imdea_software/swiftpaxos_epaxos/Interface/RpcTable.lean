/-
The `rpc` package (`rpc/rpc.go`): the code table `Table` (`id`, the next code; `pairs`, a map
from a code to its `Pair{Obj, Chan}`), generic over what the entries are (the replica framework
and epaxos say what they register: `Epaxos/Interface/Replica.lean`, `tableOk`).

* `ownTable t n E` (exclusive, while registering): the table's next code is `n`, its entries `E`.
* `isTable t E` (persistent, once frozen: `ownTable_freeze`): read-only entries `E`.
* Specs: `NewTableId(id)` (empty, next code `id`), `Register(obj, ch)` (returns the next code,
  adds the pair), `Get(id)` (the entry and `true`, or the zero pair and `false`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Marshal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions]

/-- The table at `t` has next code `n` and entries `E` (exclusive). -/
def ownTableDef (t : Loc) (n : w8) (E : GMap w8 rpc.Pair') : IProp GF :=
  iprop(∃ pm : GoMap, t ↦ rpc.Table.mk n pm ∗ ownMap pm (DFrac.own 1) E)

@[irreducible] def ownTable (t : Loc) (n : w8) (E : GMap w8 rpc.Pair') : IProp GF :=
  ownTableDef t n E

theorem ownTable_unseal : ownTable (GF := GF) = ownTableDef := by funext; with_unfolding_all rfl

/-- The table at `t` has entries `E`, read-only (persistent). -/
def isTableDef (t : Loc) (E : GMap w8 rpc.Pair') : IProp GF :=
  iprop(∃ (n : w8) (pm : GoMap), t ↦□ rpc.Table.mk n pm ∗ ownMap pm DFrac.discard E)

@[irreducible] def isTable (t : Loc) (E : GMap w8 rpc.Pair') : IProp GF := isTableDef t E

theorem isTable_unseal : isTable (GF := GF) = isTableDef := by funext; with_unfolding_all rfl

instance isTable_persistent (t : Loc) (E : GMap w8 rpc.Pair') : Persistent (isTable (GF := GF) t E) := by
  rw [isTable_unseal]; unfold isTableDef; infer_instance

/-- Freeze the table (no more registrations). -/
theorem ownTable_freeze (t : Loc) (n : w8) (E : GMap w8 rpc.Pair') :
    ownTable (GF := GF) t n E ==∗ isTable t E := by
  rw [ownTable_unseal, isTable_unseal]; unfold ownTableDef isTableDef
  iintro ⟨%pm, Ht, Hm⟩
  ipersist Ht
  imod ownMap_persist $$ Hm with #Hm
  imodintro
  iexists n, pm
  iframe Ht Hm

/-- `NewTableId(id)`. -/
def rpc.NewTableId.spec : Prop :=
  ∀ (id : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.rpc }}
    (App (Val (@! rpc.NewTableId)) (Val #id))
  {{ (t : Loc), RET #t; ownTable t id ∅ }}

/-- `t.Register(obj, ch)`: the next code, with the pair added. -/
def rpc.Table.Register.spec : Prop :=
  ∀ (t : Loc) (n : w8) (E : GMap w8 rpc.Pair') (obj : GoInterface) (ch : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.rpc ∗
      ownTable t n E }}
    (App (App (Val (t @!! go.GoType.PointerType rpc.Table.ty @!! go!"Register")) (Val #obj))
      (Val #ch))
  {{ RET #n; ownTable t (n + 1) (E.insert n (rpc.Pair'.mk obj ch)) }}

/-- `t.Get(id)` on a frozen table. -/
def rpc.Table.Get.spec : Prop :=
  ∀ (t : Loc) (E : GMap w8 rpc.Pair') (id : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.rpc ∗
      isTable t E }}
    (App (Val (t @!! go.GoType.PointerType rpc.Table.ty @!! go!"Get")) (Val #id))
  {{ RET (PairV #((E.lookup id).getD (zeroValDef : rpc.Pair')) #(E.lookup id).isSome); True }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
