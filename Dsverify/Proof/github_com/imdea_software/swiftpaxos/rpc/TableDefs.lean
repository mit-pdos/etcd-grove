/-
The definitions, specs and lemmas of `Table.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [rpc.Assumptions]

/-- The table at `t` (see the file header). -/
def rpc.isTable (t : Loc) (dq : DFrac) (nid : w8) (ents : GMap w8 rpc.Pair'') :
    IProp netDistGF :=
  iprop(∃ mp : GoMap, t ↦{dq} rpc.Table.mk nid mp ∗ mp ↦${dq} ents)

theorem rpc.isTable_persist (t : Loc) (nid : w8) (ents : GMap w8 rpc.Pair'') :
    rpc.isTable t (DFrac.own 1) nid ents ⊢ |==> rpc.isTable t DFrac.discard nid ents := by
  unfold rpc.isTable
  iintro ⟨%mp, Ht, Hm⟩
  ipersist Ht
  imod ownMap_persist _ _ _ $$ Hm with Hm
  imodintro
  iexists mp
  isplitl []
  · iexact Ht
  iexact Hm

instance rpc.isTable_persistent (t : Loc) (nid : w8) (ents : GMap w8 rpc.Pair'') :
    Persistent (rpc.isTable t DFrac.discard nid ents) := by
  unfold rpc.isTable; infer_instance

/-- `NewTableId(id)`: an empty table whose next id is `id`. -/
abbrev rpc.NewTableId.spec : Prop :=
  ∀ (id : w8),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.rpc }}
    (App (Val (@! rpc.NewTableId)) (Val #id))
  {{ (t : Loc), RET #t; rpc.isTable t (DFrac.own 1) id ∅ }}

/-- `t.Register(obj, notify)`: the pair is registered under the next id, which is returned. -/
abbrev rpc.Table.Register.spec : Prop :=
  ∀ (t : Loc) (nid : w8) (ents : GMap w8 rpc.Pair'') (obj : GoInterface) (ch : GoChan),
  {{ rpc.isTable t (DFrac.own 1) nid ents }}
    (App (App (Val (t @!! go.GoType.PointerType rpc.Table.ty @!! go!"Register")) (Val #obj))
      (Val #ch))
  {{ RET #nid; rpc.isTable t (DFrac.own 1) (nid + 1) (ents.insert nid (rpc.Pair''.mk obj ch)) }}

/-- `t.Get(id)` on the table, fixed (after the registrations): the pair registered under `id`
(the zero pair if none) and whether there is one. -/
abbrev rpc.Table.Get.spec : Prop :=
  ∀ (t : Loc) (nid : w8) (ents : GMap w8 rpc.Pair'') (id : w8),
  {{ rpc.isTable t DFrac.discard nid ents }}
    (App (Val (t @!! go.GoType.PointerType rpc.Table.ty @!! go!"Get")) (Val #id))
  {{ RET (PairV #((ents !! id).getD (Perennial.zero_val rpc.Pair'')) #(decide ((ents !! id).isSome)));
      True }}

end defs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [rpc.Assumptions]

set_option goose.wp.extras true

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
