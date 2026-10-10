/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__do.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__do
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.encode
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.do.wp_proof
    (wp_encode : register.encode.spec (GF := GF) (hG := hG))
    (wp_node_Propose : node.Propose.spec (GF := GF) (hG := hG)) :
    Register.do.spec (GF := GF) (hG := hG) := by
  intro γr γp r kind val Ψ Hval
  wp_start as ⟨#Hreg, Hcr, Hau⟩
  iunfold isRegister at Hreg
  icases Hreg with ⟨%id, %n, %st, #Hrep⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iNamed HR
  imod opCred_spend γp c $$ Hcred Hcr with ⟨%Hc1, Hcred⟩
  have Hns : uint.Z ns + 1 < 2 ^ 64 := by omega
  wp_auto
  -- the operation's datum, minted
  imod reg_mint γr id ns kind val ⊤ CoPset.subseteq_top Hns $$ Hinv Hseq with ⟨Hseq, #Hmint, Hfresh⟩
  generalize Hd : encodeOp id (ns + W64 1) kind val = d
  wp_apply chan.wp_make2 (V := GoString) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc GoString (.Buffered []) $$ Hoc
  imod start_handoff ch (waitP γr d) iprop(True) iprop(False) γc $$ Hch Hoc
    with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  have HWfresh : W !! (ns + W64 1) = none := by
    cases h : W !! (ns + W64 1) with
    | none => rfl
    | some ch' => have := HWdom _ _ h; word
  wp_apply wp_mapInsert go.uint64 mW W (ns + W64 1) ch $$ [$HW] as HW
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters Hprod]
  · inext
    unfold lockInv
    iexists ns + W64 1, mW, W.insert (ns + W64 1) ch, c - 1
    iframe Hns HmW HW Hseq Hcred
    isplitr
    · ipureintro; word
    isplitr
    · ipureintro
      intro s ch' Hs
      by_cases Hss : s = ns + W64 1
      · subst Hss; exact Int.le_refl _
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hss)] at Hs
        have := HWdom _ _ Hs; word
    iapply (BigSepM.bigSepM_insert (Φ := fun s ch => waiterOk (GF := GF) γr id s ch) HWfresh).2
    iframe Hwaiters
    unfold waiterOk
    iexists d, γh
    iframe Hmint Hho Hprod
  -- the client's atomic update, as the one `Node.Propose` deposits
  ihave Hpau := reg_propAu γr d kind val (by rw [← Hd]; exact (regApply_encodeOp · id (ns + W64 1) kind val)) Ψ
    $$ Hinv Hau
  rw [← Hraft]
  ihave HI : iprop(propArg γp.node.raft d (fun L => Ψ (regFold (L ++ [d]))) true ∨
      propRes γp.node.raft d (fun L => Ψ (regFold (L ++ [d]))) true) $$ [Hfresh Hpau]
  · ileft
    unfold propArg
    simp only [↓reduceIte]
    iframe Hfresh Hpau
  wp_for HI
  wp_apply context.wp_Background
  wp_apply wp_encode id (ns + W64 1) kind val Hval as %b ⟨Hb, Hbcap⟩
  rw [Hd]
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  -- `Propose`: the first time with the update, after that with `d` deposited
  icases (show ⊢ iprop((propArg γp.node.raft d (fun L => Ψ (regFold (L ++ [d]))) true ∨
      propRes γp.node.raft d (fun L => Ψ (regFold (L ++ [d]))) true) -∗
      ∃ fresh : Bool, propArg γp.node.raft d (fun L => Ψ (regFold (L ++ [d]))) fresh ∗
        (if fresh then True else
          ∃ γq, isProp γp.node.raft d γq (fun L => Ψ (regFold (L ++ [d]))) ∗ propTok γq)) by
      iintro (Harg | Hres)
      · iexists true; iframe Harg; simp only [↓reduceIte]; itrivial
      · unfold propRes
        icases Hres with ⟨#Hdep, Hrest⟩
        iexists false
        unfold propArg
        simp only [Bool.false_eq_true, ↓reduceIte] at *
        iframe Hdep Hrest) $$ HI with ⟨%fresh, Harg, Hrest⟩
  wp_apply wp_node_Propose γp.node id n b d _ fresh $$ [$HisNode $Hb $Harg] as %err Hres
  ihave Hres : propRes γp.node.raft d (fun L => Ψ (regFold (L ++ [d]))) true $$ [Hres Hrest]
  · cases fresh
    · unfold propRes
      icases Hres with ⟨#Hdep, -⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hdep Hrest
    · iexact Hres
  cases err with
  | ok i =>
    -- dropped: propose again
    wp_auto
    simp only [show decide ((#true : val) = #true) = true from decide_eq_true rfl, ↓reduceIte,
      _root_.decide_true]
    wp_auto
    wp_for_post
    iframe
    iright
    iexact Hres
  | nil =>
    wp_auto
    rw [if_neg (by simp only [decide_eq_true_eq]; intro h; cases go.intoVal_inj (V := Bool) h),
      if_pos (by simp)]
    wp_auto_lc 2
    wp_apply +noauto wp_handoff_receive (t := go.string) γh ch (waitP γr d) iprop(True) iprop(False)
      false $$ [$Hho $Hcons] as %v %ok ⟨Hcons, Hgot⟩
    unfold handoffGot
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hgot with ⟨-, Hf⟩
      iexfalso; iexact Hf
    simp only [↓reduceIte]
    icases Hgot with ⟨Hw, -⟩
    iunfold waitP at Hw
    icases Hw with ⟨%l, %ods, %m, #Hl, #Hods, %Hm⟩
    obtain ⟨Hm1, Hm2, Hv⟩ := Hm
    unfold propRes
    simp only [↓reduceIte]
    icases Hres with ⟨-, %γq, #Hp, Htok⟩
    rw [← Hraft]
    imod node_collect γp.node id n d γq _ l ods m ⊤ CoPset.subseteq_top Hm1 Hm2
      $$ HisNode Hp Htok Hl Hods with HQ
    imod lc_fupd_elim_later $$ Hlc1 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    wp_auto
    rw [← Hv]
    iapply HΦ $$ HQ

end proof

end register
end EtcdGrove
end Perennial
