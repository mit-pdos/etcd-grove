/-
Package `proxy`: the ghost step of committing a slot (`smr_exec_slot`), and the answers it
gives the executed batches.
-/
module

public import Dsverify.Proof.raxos.Proxy.Send
public import Dsverify.Proof.raxos.Proxy.SumPure

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] HeapGS.goose_globalGS

instance decided_persistent_px (γ : QNames) (i : Int) (ids : List GoString) :
    Persistent (decided (GF := GF) γ i ids) := by
  unfold decided; infer_instance

/-- The flattened log's ids, as the law wants them. -/
theorem known_flatten (γ : QNames) (Bn : GMap GoString Batch) (l : List GoString)
    (hdom : ∀ x ∈ l, (Bn !! x).isSome) :
    knownP (GF := GF) γ Bn ⊢
      [∗list] x ∈ l, ∃ b, ⌜Bn !! x = some b ∧ msg.batchFit b⌝ ∗ batchReg γ x b := by
  induction l with
  | nil => iintro _; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons y ys ih =>
    iintro #Hk
    iapply BigSepL.bigSepL_cons.2
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hdom y (by simp))
    isplitl []
    · iunfold knownP at Hk
      ihave Hb := BigSepM.bigSepM_lookup (Φ := fun z c => iprop(batchReg (GF := GF) γ z c ∗ ⌜batchFit c⌝))
        (show PartialMap.get? Bn y = some b from hb) $$ Hk
      icases Hb with ⟨#Hr, %Hok⟩
      iexists b
      iframe Hr
      ipureintro; exact ⟨hb, Hok⟩
    iapply (ih (fun x hx => hdom x (List.mem_cons_of_mem _ hx))) $$ Hk

/-- Committing slot `|D| + 1`, decided `ids`, executed with the batches `Bn`: the executed
prefix grows, and every result batch is the `"nil"` batch's or an answer. -/
theorem commit_ghost (γ : QNames) (D : List (List GoString)) (ids : List GoString)
    (Bn : GMap GoString Batch) (outs : List raxos.proto.client.ClientBatch)
    (hdom : ∀ x ∈ (D ++ [ids]).flatten, (Bn !! x).isSome)
    (_hid : ∀ x b, Bn !! x = some b → b.id = x) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ inv smrN (smrInv γ) -∗ £ 2 -∗ execLb γ D -∗
      decided γ (D.length + 1) ids -∗ knownP γ Bn -∗ batchReg γ go!"nil" nilBatch -∗
      ([∗list] k ↦ o ∈ outs, ∃ x b r, ⌜(freshIds (execLog (fun y => Bn !! y) D).done ids)[k]? = some x ∧
          Bn !! x = some b ∧
          (execIds (fun y => Bn !! y) (execLog (fun y => Bn !! y) D) ids).results x = some r⌝ ∗
          repCBVal o .discard ⟨x, b.sender, r⟩) ={⊤}=∗
      execLb γ (D ++ [ids]) ∗ [∗list] o ∈ outs, ansP γ o := by
  iintro #Hcons #Hsmr Hlc #Hlb #Hdec #Hknown #Hnil Houts
  imod smr_exec_slot γ D ids (fun y => Bn !! y) $$ Hcons Hsmr Hlc Hlb Hdec [] with ⟨#Hlb', #Hans⟩
  · iapply known_flatten γ Bn _ hdom $$ Hknown
  imodintro
  iframe Hlb'
  iapply BigSepL.bigSepL_impl $$ Houts
  imodintro
  iintro %k %o %hk ⟨%x, %b, %r, %Hxbr, #Hrep⟩
  obtain ⟨hxk, hb, hr⟩ := Hxbr
  have hfx := (freshIds_nodup ids (execLog (fun y => Bn !! y) D).done).2 x (List.mem_of_getElem? hxk)
  iunfold knownP at Hknown
  ihave Hb := BigSepM.bigSepM_lookup (Φ := fun z c => iprop(batchReg (GF := GF) γ z c ∗ ⌜batchFit c⌝))
    (show PartialMap.get? Bn x = some b from hb) $$ Hknown
  icases Hb with ⟨#Hregx, %Hokb⟩
  ihave %Hshape := batchReg_shape γ x b $$ Hregx
  by_cases hs1 : b.sender = -1
  · iunfold ansP
    ileft
    iunfold repCBVal at Hrep
    icases Hrep with ⟨%ps, %Hp, -⟩
    ipureintro; simpa [hs1] using Hp.1
  · obtain ⟨c, hc6, hsender⟩ : ∃ c : Nat, c < 6 ∧ b.sender = clientName c := by
      rcases Hshape with ⟨_, ⟨_, rfl⟩ | ⟨rfl, _⟩ | h⟩
      · exact absurd rfl hs1
      · exact absurd rfl hs1
      · exact h.2.1
    ihave Ha := Hans $$ %x
    icases Ha $$ [] with ⟨%r', %Hr', #Hop⟩
    · ipureintro; exact ⟨hfx.2, hfx.1, b, hb, hs1⟩
    rw [px_execLog_snoc, hr] at Hr'
    cases Hr'
    iunfold ansP
    iright
    iexists c, x, r'
    isplitl []
    · rw [← hsender]; iexact Hrep
    iframe Hop
    ipureintro; exact hc6

end proofs
end Perennial.raxos

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] HeapGS.goose_globalGS

/-- The known batches grow by a registered batch from the store. -/
theorem known_extend (γ : QNames) (Bn : GMap GoString Batch) (x : GoString) (b : Batch)
    (hcmd : ∀ y c, Bn !! y = some c → ∀ m ∈ c.cmds, cmdOk m) (hid : ∀ y c, Bn !! y = some c → c.id = y)
    (hb : batchFit b ∧ b.id = x) :
    ⊢@{IProp GF} knownP γ Bn -∗ batchReg γ x b -∗
      ∃ Bn' : GMap GoString Batch, knownP γ Bn' ∗
        ⌜(∀ y c, Bn !! y = some c → Bn' !! y = some c) ∧ Bn' !! x = some b ∧
          (∀ y c, Bn' !! y = some c → ∀ m ∈ c.cmds, cmdOk m) ∧ (∀ y c, Bn' !! y = some c → c.id = y)⌝ := by
  iintro #Hk #Hr
  cases hx : Bn !! x with
  | some b' =>
    iunfold knownP at Hk
    ihave Hb := BigSepM.bigSepM_lookup (Φ := fun z c => iprop(batchReg (GF := GF) γ z c ∗ ⌜batchFit c⌝))
      (show PartialMap.get? Bn x = some b' from hx) $$ Hk
    icases Hb with ⟨#Hr', -⟩
    ihave %Heq := batchReg_agree γ x b b' $$ Hr Hr'
    subst Heq
    iexists Bn
    iunfold knownP
    iframe Hk
    ipureintro; exact ⟨fun _ _ h => h, hx, hcmd, hid⟩
  | none =>
    ihave %Hshape := batchReg_shape γ x b $$ Hr
    iexists Bn.insert x b
    isplitl []
    · iunfold knownP at Hk
      iunfold knownP
      iapply (BigSepM.bigSepM_insert (Φ := fun z c => iprop(batchReg (GF := GF) γ z c ∗ ⌜batchFit c⌝))
        (show PartialMap.get? Bn x = none from hx)).2
      iframe Hr Hk
      ipureintro; exact hb.1
    ipureintro
    refine ⟨fun y c h => ?_, by simp, fun y c h => ?_, fun y c h => ?_⟩
    · have hyx : y ≠ x := by intro e; subst e; rw [hx] at h; cases h
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hyx)]; exact h
    · by_cases hyx : y = x
      · subst hyx; simp at h; subst h
        rcases Hshape.2 with ⟨_, rfl⟩ | ⟨rfl, p, rfl, hp⟩ | ⟨_, _, inp, hinp, hc⟩
        · intro m hm; simp [nilBatch] at hm
        · intro m hm; simp at hm; subst hm; exact summaryId_cmdOk p hp
        · rw [hc]; intro m hm; simp at hm; subst hm; exact (execCmd_step (fun _ => none) inp hinp).1
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyx)] at h; exact hcmd y c h
    · by_cases hyx : y = x
      · subst hyx; simp at h; subst h; exact hb.2
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyx)] at h; exact hid y c h

end proofs2
end Perennial.raxos
