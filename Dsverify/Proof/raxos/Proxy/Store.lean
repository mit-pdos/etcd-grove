/-
Package `proxy`: the batch store (`clientbatchstore.go`): `Add` and `Get`.
-/
module

public import Dsverify.Proof.raxos.Replica

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.sync (MapVocab MapHyp strKey)

section proofs
attribute [-instance] Perennial.raxos.replica.src.ClientBatchStore.ClientBatchStore_typed_pointsto
  Perennial.raxos.replica.src.ClientBatchStore.ClientBatchStore_into_val_typed
  Perennial.raxos.replica.src.ClientBatchStore.ClientBatchStore_access_load_clientBatches
  Perennial.raxos.replica.src.ClientBatchStore.ClientBatchStore_access_store_clientBatches
  Perennial.sync.Map.Map_typed_pointsto Perennial.sync.Map.Map_into_val_typed
  Perennial.internal.sync.HashTrieMap.HashTrieMap_typed_pointsto
  Perennial.internal.sync.HashTrieMap.HashTrieMap_into_val_typed
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

theorem store_add_proof [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions] :
    ClientBatchStore.Add.spec (GF := GF) (hG := hG) := by
  intro γ γs cb v b
  wp_start as ⟨#Hst, #Hrep, #Hreg, %Hok⟩
  iunfold isStore at Hst
  iunfold isStoreDef at Hst
  icases Hst with ⟨%MV, %hMV, %Hnn, #Hsm, #Hinv⟩
  wp_auto
  ihave %Hid : ⌜sint.Z v.Sender' = b.sender ∧ v.Id' = b.id⌝ $$ [Hrep]
  · iunfold repCBVal at Hrep
    icases Hrep with ⟨%ps, %H, -⟩
    ipureintro; exact H
  rw [Hid.2]
  wp_bind
  iapply (hMV.Load _ b.id _) $$ Hsm
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  iunfold storeInv at Hi
  icases Hi with ⟨%M, %S, >Hm, >Hauth, >#Hels, >%Hsub, >#Hents⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists ⟨M, ()⟩
  dsimp only [Tele.app, BI.tforall_nil]
  iframe Hm
  isplit
  · iintro Hm
    imod Hmask with -
    imod Hclose $$ [Hm Hauth] with -
    · inext; iunfold storeInv; iexists M, S; iframe; iframe Hents Hels; ipureintro; exact Hsub
    imodintro
    iframe
  iintro Hm
  imod Hmask with -
  cases hx : M !! b.id with
  | some w =>
    imod storeHas_get γs M S b.id (by simp [hx]) Hsub $$ Hauth Hels with ⟨%S', Hauth, #Hels', %Hsub', #Hhas⟩
    imod Hclose $$ [Hm Hauth] with -
    · inext; iunfold storeInv; iexists M, S'; iframe; iframe Hents Hels'; ipureintro; exact Hsub'
    imodintro
    simp only [Option.isSome_some]
    wp_auto
    iapply HΦ
    unfold storeHas
    iexact Hhas
  | none =>
    imod Hclose $$ [Hm Hauth] with -
    · inext; iunfold storeInv; iexists M, S; iframe; iframe Hents Hels; ipureintro; exact Hsub
    imodintro
    simp only [Option.isSome_none]
    wp_auto
    rw [Hid.2]
    wp_bind
    iapply (hMV.Store _ b.id _ _) $$ Hsm
    iauintro
    unfold atomic_acc
    iinv Hinv with Hi Hclose
    iunfold storeInv at Hi
    icases Hi with ⟨%M, %S, >Hm, >Hauth, >#Hels, >%Hsub, >#Hents⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists ⟨M, ()⟩
    dsimp only [Tele.app, BI.tforall_nil]
    iframe Hm
    isplit
    · iintro Hm
      imod Hmask with -
      imod Hclose $$ [Hm Hauth] with -
      · inext; iunfold storeInv; iexists M, S; iframe; iframe Hents Hels; ipureintro; exact Hsub
      imodintro
      iframe
    iintro Hm
    imod Hmask with -
    imod storeHas_get γs (M.insert b.id (interface.mkOk raxos.proto.client.ClientBatch.ty #v)) S b.id (by simp)
      (fun y hy => by
        by_cases hxy : y = b.id
        · subst hxy; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxy)]; exact Hsub y hy) $$ Hauth Hels
      with ⟨%S', Hauth, #Hels', %Hsub', #Hhas⟩
    imod Hclose $$ [Hm Hauth] with -
    · inext; iunfold storeInv; iexists _, S'; iframe; iframe Hels'
      isplitr
      · ipureintro; exact Hsub'
      iapply BigSepM.bigSepM_insert_elim $$ [] Hents
      unfold storeEnt
      iexists v, b
      iframe Hrep Hreg
      ipureintro; exact ⟨rfl, rfl, Hok⟩
    imodintro
    wp_auto
    iapply HΦ
    unfold storeHas
    iexact Hhas

instance ite_persistent' {c : Prop} [Decidable c] (P Q : IProp GF) [Persistent P] [Persistent Q] :
    Persistent (if c then P else Q) := by
  split <;> infer_instance

theorem store_get_proof [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions] :
    ClientBatchStore.Get.spec (GF := GF) (hG := hG) := by
  intro γ γs cb x known
  wp_start as ⟨#Hst, #Hknown⟩
  iunfold isStore at Hst
  iunfold isStoreDef at Hst
  icases Hst with ⟨%MV, %hMV, %Hnn, #Hsm, #Hinv⟩
  wp_auto
  wp_bind
  iapply (hMV.Load _ x _) $$ Hsm
  iauintro
  unfold atomic_acc
  iinv Hinv with Hi Hclose
  iunfold storeInv at Hi
  icases Hi with ⟨%M, %S, >Hm, >Hauth, >#Hels, >%Hsub, >#Hents⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists ⟨M, ()⟩
  dsimp only [Tele.app, BI.tforall_nil]
  iframe Hm
  isplit
  · iintro Hm
    imod Hmask with -
    imod Hclose $$ [Hm Hauth] with -
    · inext; iunfold storeInv; iexists M, S; iframe; iframe Hents Hels; ipureintro; exact Hsub
    imodintro
    iframe
  iintro Hm
  imod Hmask with -
  ihave %Hkn : ⌜known = true → (M !! x).isSome⌝ $$ [Hknown Hauth]
  · cases known
    · ipureintro; intro h; cases h
    · simp only [↓reduceIte]
      iunfold storeHas at Hknown
      iunfold storeHasDef at Hknown
      ihave %HS := ghost_map_lookup $$ Hauth Hknown
      ipureintro; intro _; exact Hsub x (by simp [HS])
  cases hx : M !! x with
  | some w =>
    ihave #Hent := BigSepM.bigSepM_lookup (Φ := fun y u => storeEnt (GF := GF) γ y u)
      (show PartialMap.get? M x = some w from hx) $$ Hents
    iunfold storeEnt at Hent
    icases Hent with ⟨%cbv, %b, %Hw, #Hrep, #Hreg⟩
    imod storeHas_get γs M S x (by simp [hx]) Hsub $$ Hauth Hels with ⟨%S', Hauth, #Hels', %Hsub', #Hhas⟩
    imod Hclose $$ [Hm Hauth] with -
    · inext; iunfold storeInv; iexists M, S'; iframe; iframe Hents Hels'; ipureintro; exact Hsub'
    imodintro
    simp only [Option.isSome_some, Hw.1]
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; intro _; rfl
    simp only [↓reduceIte]
    iexists b
    iframe Hrep Hreg
    isplitr
    · ipureintro; exact Hw.2
    unfold storeHas
    iexact Hhas
  | none =>
    imod Hclose $$ [Hm Hauth] with -
    · inext; iunfold storeInv; iexists M, S; iframe; iframe Hents Hels; ipureintro; exact Hsub
    imodintro
    simp only [Option.isSome_none]
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; intro hk; have := Hkn hk; simp [hx] at this
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

/-- A fresh store (`server.go`'s `&ClientBatchStore{}`), for package `replica`: from the zero
`sync.Map` memory of its field (its points-to the deployment's `qv.map.tp`, `StoreInst.lean`), with
the `sync.Map` hypotheses, a store with no id known yet. -/
theorem isStore_alloc_proof [hMV : MapHyp qv.map] (γ : QNames) (cb : Loc)
    (E : CoPset) (Hnn : cb.[ClientBatchStore, go!"clientBatches"] ≠ null) :
    ⊢@{IProp GF} isPkgInit (PROP := IProp GF) pkg_id.sync -∗
      cb.[ClientBatchStore, go!"clientBatches"] ↦ (zero_val Perennial.sync.Map) ={E}=∗
        ∃ γs, isStore γ γs cb := by
  iintro #Hsm Hz
  imod hMV.own_zero _ $$ Hz with Hm
  imod ghost_map_alloc_empty (K := GoString) (V := Unit) with ⟨%γs, Hauth⟩
  imod inv_alloc storeN E (storeInv qv.map γ γs cb.[ClientBatchStore, go!"clientBatches"])
    $$ [Hm Hauth] with #Hinv
  · inext
    iunfold storeInv
    iexists ∅, ∅
    iframe Hm Hauth
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · ipureintro; intro x hx; simp at hx
    iapply BigSepM.bigSepM_empty.2; itrivial
  imodintro
  iexists γs
  iunfold isStore
  iunfold isStoreDef
  iexists qv.map
  iframe Hsm Hinv
  ipureintro; exact ⟨hMV, Hnn⟩

end proofs
end Perennial.raxos
