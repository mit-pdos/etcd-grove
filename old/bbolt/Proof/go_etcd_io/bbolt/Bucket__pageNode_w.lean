module
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.Tx__page_w
public import Proof.go_etcd_io.bbolt.WriteTxLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem uZ_pid_ps' (pgid : w64) (ps : Nat) (hps : ps < 2 ^ 32)
    (h : uint.nat pgid * ps < 281474976710655) :
    uint.Z (pgid * W64 (ps : Int)) = ((uint.nat pgid * ps : Nat) : Int) := by
  have hu : uint.Z (pgid * W64 (ps : Int)) = (uint.Z pgid * uint.Z (W64 (ps : Int))) % 2 ^ 64 := by
    unfold uint.Z; rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]; rfl
  have e1 : uint.Z pgid = ((uint.nat pgid : Nat) : Int) := by unfold uint.nat uint.Z; simp
  have e2 : uint.Z (W64 (ps : Int)) = (ps : Int) := by word
  rw [hu, e1, e2, ← Int.natCast_mul]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem Bucket.pageNode.wp_wproof (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hpage : Tx.page.wspec (GF := GF) (hG := hG)) :
    Bucket.pageNode.wspec (GF := GF) (hG := hG) := by
  intro W bl bv B dqb txl pmap pm dqp id Hbv Htx Hnn Hinl Hfile Hdc Hps
  subst Hbv
  wp_start as ⟨Hb, Hib, Hnm, Hv, Hpf, Hpm, Hdb⟩
  wp_auto
  wp_method_call
  try wp_auto
  wp_apply hRoot $$ [Hib] as Hib
  · iframe
  try wp_auto
  wp_if_destruct
  · have Hid0 := Hinl Hif
    have Hr0 := Hif
    subst Hid0
    try wp_auto
    wp_if_destruct
    · try wp_auto
      iapply HΦ; iframe
      ipureintro
      refine Or.inr ⟨?_, rfl, B.ipg, ?_⟩
      · unfold resolve; rw [if_pos Hr0, if_pos Hif]
      · unfold wpageAt; rw [if_pos Hr0, if_pos rfl]
    · try wp_auto
      iapply HΦ; iframe
      ipureintro
      refine Or.inl ⟨?_, rfl⟩
      unfold resolve; rw [if_pos Hr0, if_neg Hif]
  · ihave %Hnmnn := ownMap_not_nil _ _ _ $$ Hnm
    try wp_auto
    rw [decide_eq_false Hnmnn, Bool.not_false]
    try wp_auto
    wp_apply wp_map_lookup1 $$ Hnm as Hnm
    try wp_auto
    cases hk : B.nm !! id with
    | some l =>
      simp only [Option.getD_some]
      rw [decide_eq_false (Hnn id l hk)]
      try wp_auto
      iapply HΦ; iframe
      ipureintro
      refine Or.inl ⟨?_, rfl⟩
      unfold resolve; rw [if_neg Hif]; exact hk
    | none =>
      have Hres : resolve B id = none := by unfold resolve; rw [if_neg Hif]; exact hk
      obtain ⟨Hpm0, pg, Hpg, Hlen, Hid, Hfl, Hlt⟩ := Hfile Hif Hres
      simp only [Option.getD_none]
      rw [decide_eq_true (show zero_val Loc = null from rfl)]
      try wp_auto
      isimp only [wView] at Hv
      icases Hv with ⟨Hdata, #Hps', #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
      icases viewLoc_acc (GF := GF) W _ pg (inViewLoc_page W _ pg Hpg) $$ Hpv with ⟨Hpg', Hpvback⟩
      have Hu := uZ_pid_ps' id W.ps Hps Hlt
      rw [Htx]
      wp_apply hpage txl pmap pm dqp dqp W.dbl W.data (W64 (W.ps : Int)) (DFrac.own W.q) DFrac.discard id
        (W.data +ₗ ((uint.nat id * W.ps : Nat) : Int)) (DFrac.own W.q) pg
        (Or.inr ⟨Hpm0, by rw [Hu], Hdc, by rw [Hu]; omega⟩) (by simpa [Loc.add] using Hdc) Hlen Hid Hfl
        $$ [Hpf Hpm Hdb Hdata Hpg'] as ⟨Hpf, Hpm, Hdb, Hdata, -, Hpg'⟩
      · iframe
        iframe #
      try wp_auto
      ihave Hpv := Hpvback $$ Hpg'
      iapply HΦ
      iframe
      isplitr
      · ipureintro
        refine Or.inr ⟨Hres, rfl, pg, ?_⟩
        unfold wpageAt; rw [if_neg Hif, Hpg]; rfl
      unfold wView; iframe; iframe #; ipureintro; exact Hlgv

end proof

end bbolt
end EtcdGrove
end Perennial
