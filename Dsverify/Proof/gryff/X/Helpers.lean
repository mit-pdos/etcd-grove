/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Helpers.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: helper lemmas for the executor's proofs (taking the lock again, the stack)
-/
module

public import Dsverify.Proof.gryff.X.Facts

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out committedCopy executedB inBox depR)
open Perennial.gryff.replica (XS Node sccStep stackElems euOwn euOwn_open keyLt)
open Perennial.gryff.replica2 (Repl2Names)
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

theorem sccStep_perm {E : Node → Node → Prop} {X L L' : List Node} (hp : L.Perm L')
    (h : sccStep E X L) : sccStep E X L' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, hp.nodup_iff.1 h2, fun u hu => h3 u (hp.mem_iff.2 hu),
    fun u hu w hw => (h4 u (hp.mem_iff.2 hu) w hw).imp id (fun h => hp.mem_iff.1 h),
    fun u hu w hw => h5 u (hp.mem_iff.2 hu) w (hp.mem_iff.2 hw)⟩
  intro e; subst e; exact h1 (List.Perm.nil_eq hp.symm).symm

theorem sorted_stable {s s' : RState} (hs : Stable s s') {Ls : List Node}
    (hc : ∀ u ∈ Ls, (committedCopy s u).isSome)
    (h : Ls.Pairwise (fun a b => keyLt (keyS s a) (keyS s b))) :
    Ls.Pairwise (fun a b => keyLt (keyS s' a) (keyS s' b)) := by
  rw [List.pairwise_iff_getElem] at h ⊢
  intro i j hi hj hij
  rw [keyS_stable hs (hc _ (List.getElem_mem hi)), keyS_stable hs (hc _ (List.getElem_mem hj))]
  exact h i j hi hj hij

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}

/-- The boot state has no instance: a known instance pointer refutes it. -/
theorem boot_absurd (xs : XS) (n : Node) (p' : Loc) :
    epaxosOwnG (GF := GF) ρ h r xs (model.RState.init k.val) ∗
      ghostMapElem ρ.ptrs n DFrac.discard p' ⊢ False := by
  iintro ⟨H, Hn⟩
  icases (epaxosOwnG_open ..).1 $$ H with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
    %cu, %pm, -, -, -, -, -, -, -, -, -, -, -, HM, -, -, Hinsts, -, -, -, -, -, -⟩
  ihave %HnM := ghost_map_lookup $$ HM Hn
  icases instsG_upd ρ xs _ M n p' HnM $$ Hinsts with ⟨⟨%c, %hc, -⟩, -⟩
  simp [model.RState.init] at hc

/-- **Taking the lock again** (after a wait): the trace has moved forward, the committed copies
are stable, the search state is the executor's (its half of `ρ.xs`). -/
theorem ExecLaws.relock (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) (n : Node)
    (p' : Loc) :
    L.Inv ∗ L.LI ∗ ghostVar ρ.xs (1 : Qp).half xs ∗ L.TLb t ∗
        ghostMapElem ρ.ptrs n DFrac.discard p' ⊢
      |={⊤}=> ∃ t', L.LA t' xs ∗ ghostVar ρ.xs (1 : Qp).half xs ∗
        ⌜t <+: t' ∧ Stable (stOf k t) (stOf k t')⌝ := by
  iintro ⟨#HInv, HLI, Hxs, #HTLb, #Hn⟩
  icases L.li_open $$ [HInv HLI] with (⟨%t', %xs', HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩ | ⟨%xs', HEP, -, -⟩)
  · iframe; iframe #
  · icombine Hxs Hxs1 gives %Hxseq
    obtain ⟨-, rfl⟩ := Hxseq
    imod L.th_relock t t' $$ [HTH] with ⟨HTH, %Hst⟩
    · iframe; iframe #
    imodintro
    iexists t'
    isplitl [HTH HPr HRs HEP Hxs1 HPO HBt]
    · iapply (L.LA_open ..).2; iframe
    iframe; ipureintro; exact Hst
  · iexfalso
    iapply boot_absurd (k := k) xs' n p' $$ [HEP]
    iframe; iframe #

theorem stackElems_take (ρ : replica.ReplNames) (S X : List Node) (ptrs : List Loc) :
    stackElems (GF := GF) ρ (S ++ X) ptrs ⊢ stackElems ρ S (ptrs.take S.length) := by
  unfold stackElems
  iintro H
  ihave ⟨H, -⟩ := BigSepL.bigSepL_append.1 $$ H
  iapply BigSepL.bigSepL_mono (fun {i n} hin => ?_) $$ H
  iintro ⟨%p', %hp, Hp⟩
  iexists p'; iframe; ipureintro
  have hi : i < S.length := (List.getElem?_eq_some_iff.1 hin).1
  rw [List.getElem?_take, if_pos hi]; exact hp

theorem stackElems_rel (ρ : Repl2Names) (Sx : List Node) (ptrs : List Loc) (M : GMap Node Loc) :
    stackElems (GF := GF) ρ.toR1 Sx ptrs ∗ ghostMapAuth ρ.ptrs 1 M ⊢
      ghostMapAuth ρ.ptrs 1 M ∗
      ⌜∀ (i : Nat) (n : Node), Sx[i]? = some n → ∃ p', ptrs[i]? = some p' ∧ M.lookup n = some p'⌝ := by
  unfold stackElems
  simp only [Repl2Names.toR1]
  iintro ⟨#HS, HM⟩
  ihave %H : ⌜∀ (i : Nat) (n : Node), Sx[i]? = some n → ∃ p', ptrs[i]? = some p' ∧
      M.lookup n = some p'⌝ $$ [HM]
  · iintro %i %n %hin
    ihave Hi := BigSepL.bigSepL_lookup hin $$ HS
    icases Hi with ⟨%p', %hp, Hp⟩
    ihave %HpM := ghost_map_lookup $$ HM Hp
    ipureintro; exact ⟨p', hp, HpM⟩
  iframe; ipureintro; exact H

theorem euOwn_mono (euS : GoSlice) (X Y : List Node) :
    euOwn (GF := GF) euS X ⊢ euOwn euS (X ++ Y) := by
  iintro H
  icases (euOwn_open ..).1 $$ H with ⟨%euv, Hs, %Hf⟩
  iapply (euOwn_open ..).2
  iexists euv; iframe; ipureintro
  refine ⟨Hf.1, fun q e he => ⟨(Hf.2 q e he).1, fun i h0 h1 => ?_⟩⟩
  exact List.mem_append_left _ ((Hf.2 q e he).2 i h0 h1)

theorem ExecLaws.LA_lb (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) :
    L.LA t xs ⊢ |={⊤}=> L.LA t xs ∗ L.TLb t := by
  iintro H
  icases (L.LA_open ..).1 $$ H with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  imod L.th_lb t $$ HTH with ⟨HTH, #HTLb⟩
  imodintro
  iframe #
  iapply (L.LA_open ..).2; iframe

theorem stackElems_elem (ρ : Repl2Names) (Sx : List Node) (ptrs : List Loc) (i : Nat) (n : Node)
    (hi : Sx[i]? = some n) :
    stackElems (GF := GF) ρ.toR1 Sx ptrs ⊢
      ∃ p', ⌜ptrs[i]? = some p'⌝ ∗ ghostMapElem ρ.ptrs n DFrac.discard p' := by
  unfold stackElems
  simp only [Repl2Names.toR1]
  iintro #HS
  ihave Hi := BigSepL.bigSepL_lookup hi $$ HS
  iexact Hi

theorem ExecLaws.LA_ok (L : ExecLaws (GF := GF) k ρ r h p) (t : List Ev) (xs : XS) :
    L.LA t xs ⊢ L.LA t xs ∗ ⌜HeapOk xs (stOf k t)⌝ := by
  iintro H
  icases (L.LA_open ..).1 $$ H with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  ihave ⟨HEP, %Hok⟩ := epaxosOwnG_ok ρ h r xs (stOf k t) $$ HEP
  isplitl
  · iapply (L.LA_open ..).2; iframe
  ipureintro; exact Hok

theorem ExecLaws.LA_kept (L : ExecLaws (GF := GF) k ρ r h p) (t t' : List Ev) (xs : XS) :
    L.Inv ∗ L.LA t' xs ∗ L.TLb t ⊢ |={⊤}=> L.LA t' xs ∗
      ⌜∀ q i : w32, ((stOf k t).inst q i).isSome → ((stOf k t').inst q i).isSome⌝ := by
  iintro ⟨#HInv, H, #HTLb⟩
  icases (L.LA_open ..).1 $$ H with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  imod L.th_kept t t' $$ [HTH] with ⟨HTH, %Hk⟩
  · iframe; iframe #
  imodintro
  isplitl
  · iapply (L.LA_open ..).2; iframe
  ipureintro; exact Hk

theorem ExecLaws.LA_stable (L : ExecLaws (GF := GF) k ρ r h p) (t t' : List Ev) (xs : XS) :
    L.Inv ∗ L.LA t' xs ∗ L.TLb t ⊢ |={⊤}=> L.LA t' xs ∗
      ⌜t <+: t' ∧ Stable (stOf k t) (stOf k t')⌝ := by
  iintro ⟨#HInv, H, #HTLb⟩
  icases (L.LA_open ..).1 $$ H with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  imod L.th_relock t t' $$ [HTH] with ⟨HTH, %Hk⟩
  · iframe; iframe #
  imodintro
  isplitl
  · iapply (L.LA_open ..).2; iframe
  ipureintro; exact Hk

end

end Perennial.gryff.X
