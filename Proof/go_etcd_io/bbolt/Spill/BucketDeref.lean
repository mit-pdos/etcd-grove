/-
`Bucket.dereference` on any live bucket (U9b, `notes/bbolt-proof-plan.md`): `b.rootNode.root()`
dereferenced (`node.dereference`), then every cached child bucket, by Löb induction: afterwards
every bucket reached from `b` holds no view slice below its root node's root (`bktCov`), and
nothing but node records changed (`derefStep`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeDeref
public import Spec.go_etcd_io.bbolt.node__root

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.dereference.wp_aux (hRoot : node.root.spec (GF := GF) (hG := hG))
    (hND : node.dereference.spec (GF := GF) (hG := hG)) :
    ⊢ (∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (b : Loc) (B : BRec),
      ⌜X.t.bs !! b = some B ∧ b ∈ X.live ∧ derefPre X ∧ liveFresh X⌝ →
      ∀ Φ, wtxW K tx r m X -∗
        ▷ (∀ X', wtxW K tx r m X' ∗ ⌜derefStep X X' ∧ bktCov X' b⌝ -∗ Φ #()) -∗
        WP (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"dereference")) (Val #())) {{ Φ }}
      : IProp GF) := by
  iloeb as IH
  iintro %K %tx %r %m %X %b %B %Hh %Φ Hw HΦ
  obtain ⟨HB, Hlive, Hpre, Hfresh⟩ := Hh
  have HbPre := Hpre.2.1 b B HB Hlive
  have Hnull := (Hpre.2.2.1 b B HB).2
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  icases wtxHeap_bkt_peek tx _ X b B HB Hlive $$ Hh with ⟨Ho, Hhb⟩
  unfold objOwn
  icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
  wp_method_call
  wp_call
  try wp_auto
  ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
  · dsimp only; iframe
  ihave Hw := Hclose $$ %X [] Hh Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  wp_join iprop(∃ X1 : WX, wtxW K tx r m X1 ∗
      ⌜derefStep X X1 ∧ ∀ rt, nodeRootIn B B.bv.rootNode' rt → covered X1 b rt⌝ ∗ b_ptr ↦ b)
    with [Hw b] as ⟨%X1, Hw, %HX1, b⟩
  · iexists X
    iframe
    ipureintro
    refine ⟨derefStep_refl X, fun rt hrt => ?_⟩
    have := nodeRootIn_ns hrt
    rw [Hif, Hnull] at this
    exact absurd this (by simp)
  · obtain ⟨rt, Hrt, Hrtl⟩ := HbPre.2 Hif
    icases wtxW_open K tx r m X $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
    icases wtxHeap_bkt_peek tx _ X b B HB Hlive $$ Hh with ⟨Ho, Hhb⟩
    unfold objOwn
    icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
    try wp_auto
    ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
    · dsimp only; iframe
    wp_apply hRoot tx (DFrac.own 1) X b B B.bv.rootNode' rt HB Hrt $$ [Hh] as Hh
    · iframe
    ihave Hw := Hclose $$ %X [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨rr, Hrr⟩ := nodeRootIn_root Hrt
    wp_apply hND K tx r m X b rt B HB (by simp [Hrr]) Hrtl Hpre Hfresh $$ [Hw] as ⟨%X1, Hw, %HX1⟩
    · iexact Hw
    try wp_auto
    wp_join_done
    iexists X1
    iframe
    ipureintro
    refine ⟨HX1.1, fun rt' hrt' => ?_⟩
    rw [nodeRootIn_unique hrt' Hrt]; exact HX1.2
  obtain ⟨B1, HB1, Hs1⟩ := optRel_some_l (HB ▸ derefStep_bs HX1.1 b)
  have Hf1 := bktStep_fields Hs1
  have Hlive1 : b ∈ X1.live := by rw [HX1.1.2.1]; exact Hlive
  icases wtxW_open K tx r m X1 $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
  icases wtxHeap_bkt_peek tx _ X1 b B1 HB1 Hlive1 $$ Hh with ⟨Ho, Hhb⟩
  unfold objOwn
  icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
  rw [Hf1.1, Hf1.2.2.2.1]
  try wp_auto
  ihave Hwand : (B.bv.buckets' ↦$ B.bm -∗ wtxW K tx r m X1 : IProp GF)
    $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hpo Hhb Hclose Hv Hst]
  · iintro Hbm
    ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
    · dsimp only; rw [Hf1.1, Hf1.2.2.2.1]; iframe
    iapply Hclose $$ %X1 [] Hh Hv Hst
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List GoString) (i : Nat) (m' : GMap GoString Loc) =>
      iprop(∃ (Xi : WX) (cv : Loc),
        ⌜m' = B.bm ∧ derefStep X Xi ∧
          (∀ rt, nodeRootIn B B.bv.rootNode' rt → covered Xi b rt) ∧
          ∀ k c, k ∈ keys.take i → B.bm !! k = some c → bktCov Xi c⌝ ∗
        (B.bv.buckets' ↦$ B.bm -∗ wtxW K tx r m Xi) ∗ child_ptr ↦ cv)) $$ Hbm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  isplitl [Hwand child]
  · iexists X1, zero_val Loc
    iframe
    ipureintro
    exact ⟨rfl, HX1.1, HX1.2, by simp⟩
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hkey, %Hv⟩ ⟨%Xi, %cv, %HP, Hwand, child⟩ Hm
    obtain ⟨rfl, HXi, Hroot, Hcov⟩ := HP
    ihave Hw := Hwand $$ Hm
    obtain ⟨Bi, HBi, Hsi⟩ := optRel_some_l (HB ▸ derefStep_bs HXi b)
    have HpreI := derefPre_step HXi Hpre
    have HfreshI := liveFresh_step HXi Hfresh
    have HliveI : b ∈ Xi.live := by rw [HXi.2.1]; exact Hlive
    obtain ⟨Hvl, Hvb⟩ := (HpreI.2.1 b Bi HBi HliveI).1 key v
      (by rw [(bktStep_fields Hsi).2.2.2.1]; exact Hv)
    obtain ⟨Bv, HBv⟩ := Option.isSome_iff_exists.1 Hvb
    try wp_auto
    have Hcpre : Xi.t.bs !! v = some Bv ∧ v ∈ Xi.live ∧ derefPre Xi ∧ liveFresh Xi :=
      ⟨HBv, Hvl, HpreI, HfreshI⟩
    wp_apply IH $$ %K %tx %r %m %Xi %v %Bv %Hcpre [Hw] as %X' ⟨Hw, %HX'⟩
    · iexact Hw
    obtain ⟨B', HB', Hs'⟩ := optRel_some_l (HB ▸ derefStep_bs (derefStep_trans _ _ _ HXi HX'.1) b)
    have Hf' := bktStep_fields Hs'
    have Hlive' : b ∈ X'.live := by rw [HX'.1.2.1]; exact HliveI
    icases wtxW_open K tx r m X' $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
    icases wtxHeap_bkt_peek tx _ X' b B' HB' Hlive' $$ Hh with ⟨Ho, Hhb⟩
    unfold objOwn
    icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
    rw [Hf'.1, Hf'.2.2.2.1]
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists B.bm
    iframe
    iexists X'
    isplitr
    · ipureintro
      refine ⟨rfl, derefStep_trans _ _ _ HXi HX'.1, fun rt hrt => covered_step HX'.1 (Hroot rt hrt),
        fun k c hk hc => ?_⟩
      rw [List.take_add_one, Hkey] at hk
      rcases List.mem_append.1 hk with h | h
      · exact bktCov_step HX'.1 (Hcov k c h hc)
      · simp at h; subst h; rw [Hv] at hc; cases hc; exact HX'.2
    iintro Hbm
    ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
    · dsimp only; rw [Hf'.1, Hf'.2.2.2.1]; iframe
    iapply Hclose $$ %X' [] Hh Hv Hst
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  isplitr
  · imodintro
    iintro %i %key %m' ⟨%Hkey, %Hv⟩ ⟨%Xi, %cv, %HP, Hwand, child⟩
    obtain ⟨rfl, -⟩ := HP
    have h1 := (Hkset key).1 (List.mem_of_getElem? Hkey)
    rw [Hv] at h1
    exact absurd h1 (by simp)
  iintro %m' ⟨%Xf, %cv, %HP, Hwand, child⟩ Hm
  obtain ⟨rfl, HXf, Hroot, Hcov⟩ := HP
  ihave Hw := Hwand $$ Hm
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  refine ⟨HXf, ?_⟩
  intro bl Bl rt hr hBl hrt
  cases hr with
  | self =>
    obtain ⟨B0, HB0, Hs0⟩ := optRel_some_r (hBl ▸ derefStep_bs HXf b)
    rw [HB] at HB0; cases HB0
    have hrt' := nodeRootIn_step' Hs0 hrt
    rw [(bktStep_fields Hs0).1] at hrt'
    exact Hroot rt hrt'
  | step _ c _ Bb k hBb hk hcd =>
    obtain ⟨B0, HB0, Hs0⟩ := optRel_some_r (hBb ▸ derefStep_bs HXf b)
    rw [HB] at HB0; cases HB0
    rw [(bktStep_fields Hs0).2.2.2.1] at hk
    have hkm : k ∈ keys := (Hkset k).2 (by simp [hk])
    have := Hcov k c (by rw [List.take_of_length_le (by omega)]; exact hkm) hk
    exact this bl Bl rt hcd hBl hrt

end proof

end bbolt
end EtcdGrove
end Perennial
