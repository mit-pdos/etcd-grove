/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/state/Command__Execute.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
variable [sync.Assumptions] [SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem state.Command.Execute.wp_proof (wp_NIL : state.NIL.spec (GF := GF))
    (wp_Put : github_com.emirpasic.gods.maps.treemap.Map.Put.spec (GF := GF))
    (wp_Get : github_com.emirpasic.gods.maps.treemap.Map.Get.spec (GF := GF))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF)) (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF)) :
    state.Command.Execute.spec (GF := GF) := fun c dq op k vsl v st σ => by
  wp_start as ⟨Hc, #Hv, Hst, %Hop⟩
  iunfold state.ownState at Hst
  icases Hst with ⟨%mu, %tm, %es, Hst, #Hmu, Htm, #Hvals⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  ihave %Hcn := typedPointsto_not_null _ _ _ $$ Hc
  ihave %Hstn := typedPointsto_not_null _ _ _ $$ Hst
  iStructNamed Hc
  iStructNamed Hst
  ihave ⟨Htm, %Hs⟩ := github_com.emirpasic.gods.maps.treemap.isTreeMap_sorted _ _ _ $$ Htm
  wp_auto
  wp_if_destruct
  · -- PUT
    rw [show interface.mkOk state.Key.ty #k = state.keyEnc k from rfl]
    wp_apply wp_Put tm state.keyEnc es k (interface.mkOk state.Value.ty #vsl) $$ [$Htm] as Htm
    wp_apply wp_NIL as %r Hr
    ipersist Hr
    wp_apply wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    iapply HΦ
    simp only [state.execS, if_pos]
    iframe Hr
    isplitl [Op K V]
    · iapply typedPointsto_combine _ _ _ (by assumption); simp only [TypedPointsto.typedPointstoDef]; iframe
    iunfold state.ownState
    iexists mu, tm, _
    iframe Htm Hmu
    isplitl [mutex Store]
    · iapply typedPointsto_combine _ _ _ (by assumption); simp only [TypedPointsto.typedPointstoDef]; iframe
    iapply state.valsOk_put es σ k vsl v Hs $$ [$Hvals $Hv]
  have h1 : ¬ op = W8 1 := Hif
  wp_if_destruct
  · -- GET
    rw [show interface.mkOk state.Key.ty #k = state.keyEnc k from rfl]
    wp_apply wp_Get tm state.keyEnc es k $$ [$Htm] as Htm
    iunfold state.valsOk at Hvals
    ihave Hk := Hvals $$ %k
    rcases hl : github_com.emirpasic.gods.maps.treemap.lookupE es k with _ | x
    · icases Hk with %Hk
      simp only [Option.getD_none, Option.isSome_none]
      wp_auto
      wp_apply wp_NIL as %r Hr
      ipersist Hr
      wp_apply wp_Unlock $$ [$Hmu $Hlocked]
      · inext; itrivial
      iapply HΦ
      simp only [state.execS, show ¬ (W8 2 : w8) = W8 1 by decide, if_false, if_true, Hk,
        Option.getD_none]
      iframe Hr
      isplitl [Op K V]
      · iapply typedPointsto_combine _ _ _ (by assumption); simp only [TypedPointsto.typedPointstoDef]; iframe
      iunfold state.ownState
      iexists mu, tm, es
      iframe Htm Hmu
      isplitl [mutex Store]
      · iapply typedPointsto_combine _ _ _ (by assumption); simp only [TypedPointsto.typedPointstoDef]; iframe
      iunfold state.valsOk; iexact Hvals
    · icases Hk with ⟨%sl, %bs, %Hx, #Hbs⟩
      obtain ⟨rfl, Hσ⟩ := Hx
      simp only [Option.getD_some, Option.isSome_some]
      wp_auto
      wp_apply wp_Unlock $$ [$Hmu $Hlocked]
      · inext; itrivial
      iapply HΦ
      simp only [state.execS, show ¬ (W8 2 : w8) = W8 1 by decide, if_false, if_true, Hσ,
        Option.getD_some]
      iframe Hbs
      isplitl [Op K V]
      · iapply typedPointsto_combine _ _ _ (by assumption); simp only [TypedPointsto.typedPointstoDef]; iframe
      iunfold state.ownState
      iexists mu, tm, es
      iframe Htm Hmu
      isplitl [mutex Store]
      · iapply typedPointsto_combine _ _ _ (by assumption); simp only [TypedPointsto.typedPointstoDef]; iframe
      iunfold state.valsOk; iexact Hvals
  · -- not SCAN: NONE or another operation
    have h2 : ¬ op = W8 2 := Hif
    wp_if_destruct
    · exact absurd rfl Hop
    wp_apply wp_NIL as %r Hr
    ipersist Hr
    wp_apply wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    iapply HΦ
    simp only [state.execS, h1, h2, if_false]
    iframe Hr
    isplitl [Op K V]
    · iapply typedPointsto_combine _ _ _ (by assumption); simp only [TypedPointsto.typedPointstoDef]; iframe
    iunfold state.ownState
    iexists mu, tm, es
    iframe Htm Hmu Hvals
    iapply typedPointsto_combine _ _ _ Hstn; simp only [TypedPointsto.typedPointstoDef]; iframe


end proof

end Perennial.github_com.imdea_software.swiftpaxos
