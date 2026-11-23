/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/rpc/TableC.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The `rpc` package's message table (rpc/rpc.go; internal specs, proved from its code): a
`*Table` (`tblOwn t id M`: its next id and its map from type bytes to `Pair{Obj, Chan}`),
`NewTableId`, `Register` (the next id, with the pair), and `Get` on a table that no longer
changes (read-only, shared by the client's readers: `tblRO`).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.rpc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace rpc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The table `t`: next id `id`, entries `M`. -/
def tblOwn (t : Loc) (id : w8) (M : GMap w8 rpc.Pair') : IProp GF :=
  iprop(∃ pm : GoMap, t ↦ rpc.Table.mk id pm ∗ pm ↦$ M)

/-- The table `t` read-only (persistent): entries `M`. -/
def tblRO (t : Loc) (M : GMap w8 rpc.Pair') : IProp GF :=
  iprop(∃ (id : w8) (pm : GoMap), t ↦□ rpc.Table.mk id pm ∗ pm ↦$□ M)

instance tblRO_persistent (t : Loc) (M : GMap w8 rpc.Pair') : Persistent (tblRO (GF := GF) t M) := by
  unfold tblRO; infer_instance

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [rpc.Assumptions]

set_option goose.wp.extras true

theorem tblOwn_persist (t : Loc) (id : w8) (M : GMap w8 rpc.Pair') :
    tblOwn (GF := GF) t id M ⊢ |==> tblRO t M := by
  unfold tblOwn tblRO
  iintro ⟨%pm, Ht, Hm⟩
  ipersist Ht
  ipersist Hm
  imodintro
  iexists id, pm
  iframe #

theorem wp_NewTableId (id : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! rpc.NewTableId)) (Val #id))
    {{ (t : Loc), RET #t; tblOwn t id ∅ }} := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w8) (V := rpc.Pair')) as %m Hm
  iapply HΦ
  unfold tblOwn
  iexists m
  iframe

theorem wp_Register (t : Loc) (id : w8) (M : GMap w8 rpc.Pair') (obj : GoInterface) (ch : GoChan) :
    {{ tblOwn (GF := GF) t id M }}
      (App (App (Val (t @!! go.GoType.PointerType rpc.Table.ty @!! go!"Register")) (Val #obj)) (Val #ch))
    {{ RET #id; tblOwn t (id + W8 1) (<[id := rpc.Pair'.mk obj ch]> M) }} := by
  wp_start as Ht
  unfold tblOwn
  icases Ht with ⟨%pm, Ht, Hm⟩
  wp_auto
  wp_apply (wp_mapInsert (K := w8) (V := rpc.Pair')) $$ [Hm] as Hm
  · iexact Hm
  wp_auto
  iapply HΦ
  iexists pm
  iframe

theorem wp_Get (t : Loc) (M : GMap w8 rpc.Pair') (k : w8) :
    {{ tblRO (GF := GF) t M }}
      (App (Val (t @!! go.GoType.PointerType rpc.Table.ty @!! go!"Get")) (Val #k))
    {{ RET (PairV #((M !! k).getD (zero_val rpc.Pair')) #(decide ((M !! k).isSome))); True }} := by
  wp_start as #Ht
  unfold tblRO
  icases Ht with ⟨%id, %pm, #Ht, #Hm⟩
  iStructNamed Ht
  wp_auto
  wp_apply (wp_map_lookup2 (K := w8) (V := rpc.Pair')) $$ [$Hm] as -
  iapply HΦ
  itrivial

end proofs

end rpc

end Perennial.github_com.imdea_software.swiftpaxos
