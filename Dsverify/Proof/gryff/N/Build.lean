/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Build.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: `RegisterRPC`, `RegisterClientRPC` over `genericBuilt`'s body (`netN.genericBuiltB`)
-/
module

public import Dsverify.Proof.gryff.N.SpecsDefs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]



theorem code_succ (n : Nat) : W8 (8 + (n : Int)) + W8 1 = W8 (8 + ((n + 1 : Nat) : Int)) := by
  have : (8 + ((n + 1 : Nat) : Int)) = (8 + (n : Int)) + 1 := by omega
  rw [this]
  unfold W8; simp only [BitVec.ofInt_add]

theorem code_ne (i n : Nat) (hi : i < n) (hn : n < 248) :
    W8 ((8 + i : Nat) : Int) ≠ W8 (8 + (n : Int)) := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [W8, BitVec.toNat_ofInt] at this
  omega

theorem regs_codes (regs : List (w8 × GoInterface × Loc))
    (h : regs.map Prod.fst = (List.range regs.length).map (fun i : Nat => W8 ((8 + i : Nat) : Int)))
    (hlen : regs.length < 248) : ∀ c ∈ regs, c.1 ≠ W8 (8 + (regs.length : Int)) := by
  intro c hc
  have hm : c.1 ∈ regs.map Prod.fst := List.mem_map_of_mem hc
  rw [h] at hm
  obtain ⟨i, hi, he⟩ := List.mem_map.1 hm
  rw [← he]
  exact code_ne i _ (List.mem_range.1 hi) hlen

theorem regs_codes_snoc (regs : List (w8 × GoInterface × Loc)) (e : GoInterface × Loc)
    (h : regs.map Prod.fst = (List.range regs.length).map (fun i : Nat => W8 ((8 + i : Nat) : Int))) :
    (regs ++ [(W8 (8 + (regs.length : Int)), e)]).map Prod.fst =
      (List.range (regs ++ [(W8 (8 + (regs.length : Int)), e)]).length).map
        (fun i : Nat => W8 ((8 + i : Nat) : Int)) := by
  simp only [List.map_append, h, List.length_append, List.length_singleton, List.range_succ,
    List.map_cons, List.map_nil]
  push_cast; rfl

theorem lastReg_snoc (cregs : List (w8 × Loc)) (op op' : w8) (ch : Loc) :
    lastReg (cregs ++ [(op, ch)]) op' = if op = op' then some ch else lastReg cregs op' := by
  unfold lastReg
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.find?_cons]
  by_cases h : op = op'
  · simp [h]
  · have : (op == op') = false := by simpa using h
    simp only [this, if_neg h]

set_option goose.wp.extras true

theorem RegisterRPC_wp (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) (obj : GoInterface)
    (ch : Loc) (hlen : regs.length < 248) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericBuiltB gR id nodes regs cregs }}
      (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"RegisterRPC"))
        (Val #obj)) (Val #ch))
    {{ (code : w8), RET #code; genericBuiltB gR id nodes (regs ++ [(code, obj, ch)]) cregs ∗
        ⌜∀ c ∈ regs, c.1 ≠ code⌝ }} := by
  wp_start as Hb
  iunfold genericBuiltB at Hb
  icases Hb with ⟨%rt, %ct, %M, %CM, #Hrt, HM, Hcode, %Hregs, Hent, #Hct, HCM, #Hcent, Hrest⟩
  wp_auto
  ipersist «$r0»
  wp_apply (wp_mapInsert (V := Loc) go.uint8 rt M _ _) $$ HM as HM
  have hne := regs_codes regs Hregs.1 hlen
  rw [code_succ]
  iapply HΦ
  isplitl
  · iunfold genericBuiltB
    iexists rt, ct, _, CM
    simp only [List.length_append, List.length_singleton]
    iframe
    iframe #
    isplitr
    · ipureintro
      have h := regs_codes_snoc regs (obj, ch) Hregs.1
      simp only [List.length_append, List.length_singleton] at h
      exact ⟨h, by omega⟩
    isplitl [Hent]
    · iapply BigSepL.bigSepL_mono $$ Hent
      intro i e he
      iintro ⟨%pp, %hpp, Hpp⟩
      iexists pp; iframe Hpp; ipureintro
      rw [GMap.lookup_insert_ne _ _ (Ne.symm (hne e (List.mem_of_getElem? he)))]; exact hpp
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    · iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial
  · ipureintro; exact hne

theorem RegisterClientRPC_wp (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) (obj : GoInterface) (op : w8)
    (ch : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericBuiltB gR id nodes regs cregs }}
      (App (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"RegisterClientRPC"))
        (Val #obj)) (Val #op)) (Val #ch))
    {{ RET #(); genericBuiltB gR id nodes regs (cregs ++ [(op, ch)]) }} := by
  wp_start as Hb
  iunfold genericBuiltB at Hb
  icases Hb with ⟨%rt, %ct, %M, %CM, #Hrt, HM, Hcode, %Hregs, Hent, #Hct, HCM, #Hcent, Hrest⟩
  wp_auto
  ipersist «$r0»
  wp_apply (wp_mapInsert (V := Loc) go.uint8 ct CM _ _) $$ HCM as HCM
  iapply HΦ
  iunfold genericBuiltB
  iexists rt, ct, M, _
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hregs
  imodintro
  iintro %op' %ch' %hl
  rw [lastReg_snoc] at hl
  by_cases h : op = op'
  · subst h
    simp only [if_true] at hl
    cases hl
    iexists _, obj; iframe #; ipureintro; exact GMap.lookup_insert _ _ _
  · simp only [h, if_false] at hl
    ihave ⟨%pp, %o, %hpp, Hpp⟩ := Hcent $$ %op' %ch' %hl
    iexists pp, o; iframe Hpp; ipureintro
    rw [GMap.lookup_insert_ne _ _ h]; exact hpp

end

end Perennial.gryff.netN
