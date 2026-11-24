/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GhostSteps2.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/prove-s2-g.md; notes/proph-swiftpaxos.md): the specs of the recovery's prophecy-only
resolvers (etc/proph-patches/dsv-swiftpaxos): `resolveReport` (a replica's report,
`fillNewLeaderAckN`'s end) and `resolveComputeSync` (the new leader's `MSync`,
`handleNewLeaderAckNs`), in the style of GhostSteps.lean: each builds its event's string
(`sp.strW (sp.encP e)`) and resolves the node's prophecy once with it (`swift.wp_resolveStep`), the
caller's update (`swift.resolveUpd`) running inside the node prophecy's invariant.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `swift.ackObj` with its ballot `bl` exposed (`resolveReport` resolves `m.Ballot`). -/
def swift.ackObjB (p : Loc) (bl : w32) (a : Nat × sp.Report) : IProp netDistGF :=
  iprop(∃ (rep cb : w32) (ids ph cm dp : GoSlice) (cmL : List state.Command)
      (dpL : List swift.SDep),
    p ↦□ swift.MNewLeaderAckN.mk rep bl cb ids ph cm dp ∗
    ids ↦*□ (a.2.entries.map (fun e => ofCmdId e.id)) ∗
    ph ↦*□ (a.2.entries.map (·.phase)) ∗ cm ↦*□ cmL ∗ dp ↦*□ dpL ∗
    ⌜sint.Z rep = a.1 ∧ sint.Z cb = a.2.cbal ∧ cmL.length = a.2.entries.length ∧
      dpL.length = a.2.entries.length⌝ ∗
    [∗list] i ↦ e ∈ a.2.entries, ∃ (c : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj c sd e)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.ackObjB_persistent (p : Loc) (bl : w32) (a : Nat × sp.Report) :
    Persistent (swift.ackObjB p bl a) := by
  unfold swift.ackObjB; infer_instance

theorem swift.ackObjB_ackObj (p : Loc) (bl : w32) (a : Nat × sp.Report) :
    swift.ackObjB p bl a ⊢ swift.ackObj p a := by
  iintro H
  iunfold swift.ackObjB at H
  icases H with ⟨%rep, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, H⟩
  iunfold swift.ackObj
  iexists rep, bl, cb, ids, ph, cm, dp, cmL, dpL
  iexact H

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [client.Assumptions]

set_option goose.wp.extras true

theorem swift.sint_w32_lt (x : w32) : sint.Z x < 2 ^ 31 := by
  have := BitVec.toInt_lt (x := x)
  show x.toInt < _
  simp at this
  omega

/-- `computeSync`'s words. -/
theorem swift.encP_computeSync (b : Nat) (ids : List Nat) :
    sp.encP (.computeSync b ids) =
      [W64 10, sp.natW b, W64 (ids.length : Int)] ++ ids.flatMap (fun r => [sp.natW r]) := by
  simp [sp.encP, sp.listW]

/-- `resolveComputeSync(b, msgs)`: the reports' replicas in `msgs`' order. -/
theorem swift.wp_resolveComputeSync (γ : sp.Names) (k : Nat) (b : w32) (msl : GoSlice) (dq : DFrac)
    (ms : List GoInterface) (reps : List (Nat × sp.Report)) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      msl ↦*{dq} ms ∗ swift.acksIs ms reps ∗
      swift.resolveUpd γ k (.computeSync (sp.bal b) (reps.map Prod.fst)) Q }}
    (App (App (Val (@! swift.resolveComputeSync)) (Val #b)) (Val #msl))
  {{ RET #(); msl ↦*{dq} ms ∗ Q }} := by
  wp_start as ⟨#Hok, %Hb, Hmsl, #Hacks, Hupd⟩
  iunfold swift.acksIs at Hacks
  icases Hacks with ⟨%prs, %Hprs, #Hprs⟩
  obtain ⟨rfl, rfl⟩ := Hprs
  ihave %Hlen := ownSlice_len $$ Hmsl
  simp only [List.length_map] at Hlen
  iunfold client.nodeGhostOk at Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  wp_auto
  simp only [sp.strW1_eval]
  obtain ⟨S0, hS0⟩ : ∃ S0 : List w8, S0 = [] ++ sp.strW1 (W64 10) ++ sp.strW1 (W64 (sint.Z b)) ++
      sp.strW1 msl.len := ⟨_, rfl⟩
  rw [← hS0]
  ihave IH : iprop(∃ (j wv : w64),
      "i" ∷ i_ptr ↦ j ∗ "w" ∷ w_ptr ↦ wv ∗
      "s" ∷ s_ptr ↦ (S0 ++ sp.strW ((prs.take (sint.Z j).toNat).map (fun q => sp.natW q.2.1))) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (prs.length : Int) ∧
        ∀ q ∈ prs.take (sint.Z j).toNat, q.2.1 < 2 ^ 31⌝) $$ [i w s]
  · iexists _, _
    iframe
    isplitl [s]
    · simp [sp.strW]; iexact s
    ipureintro; exact ⟨by word, by word, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z j).toNat < prs.length := by have := Hlen.1; word
    obtain ⟨q, Hq⟩ : ∃ q, prs[(sint.Z j).toNat]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl.len from ⟨Hj.1, Hif⟩]
    ihave #Hqo := (BigSepL.bigSepL_lookup (Φ := fun _ q => swift.ackObj q.1 q.2) Hq) $$ Hprs
    iunfold swift.ackObj at Hqo
    icases Hqo with ⟨%rep, %bl, %cb, %ids, %ph, %cm, %dp, %cmL, %dpL, #Hpq, -, -, -, -, %Hqf, -⟩
    iStructNamed Hpq
    wp_apply wp_load_slice_index msl (sint.Z j) _ dq
      (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #q.1) Hj.1 $$ [Hmsl] as Hmsl
    · iframe; ipureintro; rw [List.getElem?_map, Hq]; rfl
    try wp_auto
    simp only [sp.strW1_eval]
    wp_for_post
    iframe
    iexists _, _
    iframe
    have Hsucc : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
    have h0 : 0 ≤ sint.Z rep := by rw [Hqf.1]; omega
    isplitl [s]
    · iExactEq s
      rw [Hsucc, List.take_add_one, Hq]
      have hr : (W64 (sint.Z rep)) = sp.natW q.2.1 := by
        simp only [sp.natW]; rw [← Hqf.1]
      simp [sp.strW, ← hr]
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [Hsucc, List.take_add_one, Hq]
    intro q' hq'
    rcases List.mem_append.mp hq' with h | h
    · exact Hj.2.2 q' h
    · simp only [Option.toList_some, List.mem_singleton] at h
      subst h
      have := Hqf.1
      have := swift.sint_w32_lt rep
      omega
  · have hk : (sint.Z j).toNat = prs.length := by have := Hlen.1; word
    have hl : msl.len = W64 (prs.length : Int) := by have := Hlen.1; word
    have hfull : prs.take (sint.Z j).toNat = prs := by
      rw [hk, List.take_of_length_le (Nat.le_refl _)]
    have Hall := Hj.2.2
    rw [hfull] at Hall
    rw [hfull]
    have hwf : sp.PEvWf (.computeSync (sp.bal b) ((prs.map Prod.snd).map Prod.fst)) := by
      refine ⟨by have := swift.bal_lt b; omega, by simp; have := Hlen.1; word, ?_⟩
      intro r hr
      simp only [List.map_map, List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      have := Hall q hq
      simp only [Function.comp]
      omega
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    wp_bind (ResolveProph _ _)
    iapply (swift.wp_resolveStep γ k p _ hwf Q _ _ ?hs)
    case hs =>
      have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
      rw [hS0]
      simp [sp.encP, sp.natW, sp.bal, h, sp.strW, sp.listW, hl, List.flatMap_map, Function.comp_def, List.flatMap_assoc]
    iframe Hi Hupd
    iintro HQ
    wp_auto
    iapply HΦ
    iframe

/-- `report`'s words. -/
theorem swift.encP_report (b : Nat) (R : sp.Report) :
    sp.encP (.report b R) =
      [W64 9, sp.natW b, sp.natW R.cbal, W64 (R.entries.length : Int)] ++
        R.entries.flatMap sp.repEntryW := by
  simp [sp.encP, sp.listW]

/-- `resolveReport(m)`: the report's ballot, `cballot`, then each entry's id, phase, command and
dependencies (`sp.repEntryW`). TODO (proph-swiftpaxos, WIP): the proof (the old `wp_ghostReport`'s
loop, building the string instead of the slice; nested loops over a command's value and an entry's
dependencies, the elements' fields read through `ownSlice_elem_acc` + `iStructNamed`, as
`wp_resolvePreaccept` does). -/
theorem swift.wp_resolveReport (γ : sp.Names) (k : Nat) (p : Loc) (bl : w32) (a : Nat × sp.Report)
    (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z bl⌝ ∗ swift.ackObjB p bl a ∗
      swift.resolveUpd γ k (.report (sp.bal bl) a.2) Q }}
    (App (Val (@! swift.resolveReport)) (Val #p))
  {{ RET #(); Q }} := by
  sorry

end proof

end Perennial.github_com.imdea_software.swiftpaxos
