/-
The common ghost step of a replica from idle (a handler, `handlePropose`, a recovery): its state,
outboxes, pending broadcast and channel move with the authority; the outboxes and the pending
broadcast are handed out, with the re-proposal tokens of the outputs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostLaws

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The outboxes of an idle replica move to `new` (each authority half was `[]`). -/
theorem outboxes_update (γ : EpNames) (i : Nat) (cur new : Nat → List Msg) :
    ([∗list] to ∈ List.range nR, ghostVar (γ.proto.outbox i to) (1 : Qp).half (cur to)) -∗
    ([∗list] to ∈ List.range nR, outboxFragB (GF := GF) γ i to []) ==∗
      ⌜∀ to < nR, cur to = []⌝ ∗
      ([∗list] to ∈ List.range nR, ghostVar (γ.proto.outbox i to) (1 : Qp).half (new to)) ∗
      ([∗list] to ∈ List.range nR, outboxFragB γ i to (new to)) := by
  iintro Ha Hf
  ihave H := (BigSepL.bigSepL_sep_eqv
    (Φ := fun _ to => ghostVar (GF := GF) (γ.proto.outbox i to) (1 : Qp).half (cur to))
    (Ψ := fun _ to => outboxFragB γ i to [])).2 $$ [Ha Hf]
  · isplitl [Ha]
    · iexact Ha
    · iexact Hf
  imod bigSepL_bupd_mono (List.range nR)
    (fun to => iprop(ghostVar (γ.proto.outbox i to) (1 : Qp).half (cur to) ∗ outboxFragB γ i to []))
    (fun to => iprop(⌜cur to = []⌝ ∗ ghostVar (γ.proto.outbox i to) (1 : Qp).half (new to) ∗
      outboxFragB γ i to (new to))) (fun to _ => by
        unfold outboxFragB
        iintro ⟨H1, %h, H2⟩
        ihave %e := gvar_agree _ _ _ $$ H1 H2
        imod gvar_update _ _ _ (new to) $$ H1 H2 with ⟨H1, H2⟩
        imodintro
        iframe
        ipureintro; exact ⟨e, h⟩) $$ H with H
  ihave ⟨Hp, H⟩ := BigSepL.bigSepL_sep_eqv.1 $$ H
  ihave %hp := (BigSepL.bigSepL_pure (φ := fun _ to => cur to = []) (l := List.range nR)).1 $$ Hp
  ihave ⟨Ha, Hf⟩ := BigSepL.bigSepL_sep_eqv.1 $$ H
  imodintro
  iframe
  ipureintro
  intro to hto
  exact hp to to (range_getElem? hto)

theorem ghost_step_idle (γ : EpNames) (i : Nat) (S S' : Sys) (σ σ' : RState) (outs : List Out)
    (hi : i < nR)
    (hrest : ∀ j, j ≠ i → sameAt S S' j)
    (hrep : S'.rep i = σ') (hcrt : ∀ q, zz (σ.crtInstance q) ≤ zz (σ'.crtInstance q))
    (hout : ∀ to, S'.outbox i to = S.outbox i to ++ sendsToB outs to)
    (hpend : S'.pending i = pendOf outs)
    (hcur : S'.execCur i = S.execCur i ∧ S'.execIdx i = S.execIdx i)
    (hchan : S'.proposeChan i = S.proposeChan i ++ outs.filterMap Out.reprop) :
    sysAuthB (GF := GF) γ S -∗ repFragB γ i σ -∗ repIdleB γ i ==∗
      ⌜S.rep i = σ ∧ S.pending i = none ∧ S.execCur i = [] ∧ S.execIdx i = 0 ∧
        ∀ to < nR, S.outbox i to = []⌝ ∗
      sysAuthB γ S' ∗ repFragB γ i σ' ∗
      ([∗list] to ∈ List.range nR, outboxFragB γ i to (sendsToB outs to)) ∗
      pendFragB γ i (pendOf outs) ∗ curFragB γ i [] 0 ∗
      [∗list] p ∈ outs.filterMap Out.reprop, chanTok γ i p := by
  iintro Ha Hf Hidle
  ihave ⟨Hi, Hclose⟩ := sysAuthB_acc γ S i hi $$ Ha
  ihave %hσ := rep_agree γ S i σ $$ Hi Hf
  iunfold sysAuthRepB at Hi
  iunfold repFragB at Hf
  iunfold repIdleB at Hidle
  icases Hi with ⟨⟨%L, HL, %hL⟩, Hob, Hpd, Hcu, Hch⟩
  icases Hf with ⟨-, %L', HL', %hL'⟩
  ihave %hLL := rsAuth_agree _ _ _ _ _ $$ HL HL'
  obtain ⟨-, rfl⟩ := hLL
  icases Hidle with ⟨Hobf, Hpdf, Hcuf⟩
  imod rep_update γ i L σ σ' hi hL'.1 hL'.2 hcrt $$ HL HL' with ⟨HL, Hf⟩
  imod outboxes_update γ i (S.outbox i) (sendsToB outs) $$ Hob Hobf with ⟨%hob, Hob, Hobf⟩
  iunfold pendFragB at Hpdf
  iunfold curFragB at Hcuf
  icases Hpdf with ⟨-, Hpdf⟩
  ihave %hpd := gvar_agree _ _ _ $$ Hpd Hpdf
  imod gvar_update _ _ _ (pendOf outs) $$ Hpd Hpdf with ⟨Hpd, Hpdf⟩
  icases Hcuf with ⟨-, Hcuf⟩
  ihave %hcu := gvar_agree _ _ _ $$ Hcu Hcuf
  imod chan_mint γ i (outs.filterMap Out.reprop) (S.proposeChan i) $$ Hch with ⟨Hch, Htoks⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨hσ, hpd, (Prod.mk.inj hcu).1, (Prod.mk.inj hcu).2, hob⟩
  isplitl [Hclose HL Hob Hpd Hcu Hch]
  · iapply Hclose $$ %S' %hrest
    iunfold sysAuthRepB
    isplitl [HL]
    · rw [hrep]; iexact HL
    have eo : ∀ to < nR, S'.outbox i to = sendsToB outs to := fun to hto => by
      rw [hout, hob to hto, List.nil_append]
    isplitl [Hob]
    · iapply BigSepL.bigSepL_mono ?_ $$ Hob
      intro k to hk
      obtain ⟨rfl, hk'⟩ := range_getElem?_eq hk
      rw [eo to hk']
    isplitl [Hpd]
    · rw [hpend]; iexact Hpd
    isplitl [Hcu]
    · rw [hcur.1, hcur.2]; iexact Hcu
    · rw [hchan]; iexact Hch
  iframe Hf Hobf Htoks
  isplitl [Hpdf]
  · iunfold pendFragB
    isplitr; · ipureintro; exact hi
    iexact Hpdf
  · iunfold curFragB
    isplitr; · ipureintro; exact hi
    iexact Hcuf

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
