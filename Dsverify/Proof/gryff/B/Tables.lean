/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Tables.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B3: `genericBuilt`'s rpc tables apart from the rest of the generic replica (`netN.builtRest`),
so that `NewReplica` can open the rest (its channels' ghost names, for `Repl2Names`) and keep
registering: `RegisterRPC` / `RegisterClientRPC` over the tables alone (unit N's proofs,
`N/Build.lean`, which only frame the rest).
-/
module

public import Dsverify.Proof.gryff.N.Build
public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.netN (lastReg builtRest genericBuiltB code_succ regs_codes regs_codes_snoc
  lastReg_snoc)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]


/-- `genericBuiltB` without `builtRest`: the rpc tables (the client registrations `cregs` with
their objects, of distinct op codes). -/
def tblB (gR : Loc) (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × GoInterface × Loc)) :
    IProp GF :=
  iprop(∃ (rt ct : Loc) (M CM : GMap w8 Loc),
    gR.[src.genericsmr.Replica, go!"rpcTable"] ↦□ rt ∗ rt ↦$ M ∗
    gR.[src.genericsmr.Replica, go!"rpcCode"] ↦ W8 (8 + regs.length) ∗
    ⌜regs.map Prod.fst = (List.range regs.length).map (fun i : Nat => W8 ((8 + i : Nat) : Int)) ∧
      regs.length ≤ 248⌝ ∗
    ([∗list] e ∈ regs, ∃ (pp : Loc), ⌜M !! e.1 = some pp⌝ ∗
      pp ↦□ src.genericsmr.RPCPair.mk e.2.1 e.2.2) ∗
    gR.[src.genericsmr.Replica, go!"clientRpcTable"] ↦□ ct ∗ ct ↦$ CM ∗
    ([∗list] e ∈ cregs, ∃ (pp : Loc), ⌜CM !! e.1 = some pp⌝ ∗
      pp ↦□ src.genericsmr.ClientRPCPair.mk e.2.1 e.2.2))

theorem genericBuilt_split (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) :
    replica2.genericBuilt (GF := GF) gR id nodes regs [] ⊢ tblB gR regs [] ∗ builtRest gR id nodes := by
  unfold replica2.genericBuilt genericBuiltB tblB
  iintro ⟨%rt, %ct, %M, %CM, #H1, H2, H3, %H4, H5, #H6, H7, -, Hrest⟩
  iframe Hrest
  iexists rt, ct, M, CM
  iframe; iframe #
  isplitr
  · ipureintro; exact H4
  iapply BigSepL.bigSepL_nil.2; iempintro

set_option goose.wp.extras true

theorem RegisterRPC_tbl (gR : Loc) (regs : List (w8 × GoInterface × Loc))
    (cregs : List (w8 × GoInterface × Loc)) (obj : GoInterface) (ch : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ tblB gR regs cregs ∗
        ⌜regs.length < 248⌝ }}
      (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"RegisterRPC"))
        (Val #obj)) (Val #ch))
    {{ (code : w8), RET #code; tblB gR (regs ++ [(code, obj, ch)]) cregs ∗
        ⌜code = W8 (8 + (regs.length : Int)) ∧ ∀ c ∈ regs, c.1 ≠ code⌝ }} := by
  wp_start as ⟨Hb, %hlen⟩
  iunfold tblB at Hb
  icases Hb with ⟨%rt, %ct, %M, %CM, #Hrt, HM, Hcode, %Hregs, Hent, #Hct, HCM, Hcent⟩
  wp_auto
  ipersist «$r0»
  wp_apply (wp_mapInsert (V := Loc) go.uint8 rt M _ _) $$ HM as HM
  have hne := regs_codes regs Hregs.1 hlen
  rw [code_succ]
  iapply HΦ
  isplitl
  · iunfold tblB
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
  · ipureintro; exact ⟨rfl, hne⟩

theorem RegisterClientRPC_tbl (gR : Loc) (regs : List (w8 × GoInterface × Loc))
    (cregs : List (w8 × GoInterface × Loc)) (obj : GoInterface) (op : w8) (ch : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ tblB gR regs cregs ∗
        ⌜∀ c ∈ cregs, c.1 ≠ op⌝ }}
      (App (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"RegisterClientRPC"))
        (Val #obj)) (Val #op)) (Val #ch))
    {{ RET #(); tblB gR regs (cregs ++ [(op, obj, ch)]) }} := by
  wp_start as ⟨Hb, %hne⟩
  iunfold tblB at Hb
  icases Hb with ⟨%rt, %ct, %M, %CM, #Hrt, HM, Hcode, %Hregs, Hent, #Hct, HCM, Hcent⟩
  wp_auto
  ipersist «$r0»
  wp_apply (wp_mapInsert (V := Loc) go.uint8 ct CM _ _) $$ HCM as HCM
  iapply HΦ
  iunfold tblB
  iexists rt, ct, M, _
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hregs
  isplitl [Hcent]
  · iapply BigSepL.bigSepL_mono $$ Hcent
    intro i e he
    iintro ⟨%pp, %hpp, Hpp⟩
    iexists pp; iframe Hpp; ipureintro
    rw [GMap.lookup_insert_ne _ _ (Ne.symm (hne e (List.mem_of_getElem? he)))]; exact hpp
  isplitr
  · ipureintro; exact GMap.lookup_insert _ _ _
  iapply BigSepL.bigSepL_nil.2; iempintro

end

end Perennial.gryff.unitB
