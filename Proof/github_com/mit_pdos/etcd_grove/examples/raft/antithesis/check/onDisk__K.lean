/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.K()` (B 314-316, `OnDisk.K`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__K
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L0
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem onDisk.K.wp_proof (wp_fm : onDisk.fm.spec (GF := GF) (hG := hG))
    (wp_L0 : onDisk.L0.spec (GF := GF) (hG := hG)) (wp_At : At.spec (GF := GF) (hG := hG)) :
    onDisk.K.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨-, -, -, -, HB⟩ := Hp
  obtain ⟨b, E, hb, HW⟩ := HB.get
  rw [OnDisk.K_eq] at Hv
  obtain ⟨fm, hfm, Hv⟩ := bind_ok Hv
  obtain ⟨r, hr, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  obtain ⟨hpli, hfl, -, -, -⟩ := OnDisk.fm_within HW hfm
  unfold numBound at hb
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'fm.method_unfold]
  try wp_auto
  wp_apply wp_fm gx x fm $$ [Hx] as %u #Hu
  · iframe Hx; ipureintro; exact hfm
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'L0.method_unfold]
  try wp_auto
  wp_apply wp_L0 gx x $$ [Hx] as %l0 #Hl0
  · iexact Hx
  try wp_auto
  ihave %Hl0l := logRO_len _ _ $$ Hl0
  iunfold appendFactRO at Hu
  icases Hu with ⟨%Hur, #Hes⟩
  obtain ⟨-, -, -, hupli, -, -⟩ := Hur
  ihave #Hes' := Hes
  iunfold logRO at Hes'
  icases Hes' with ⟨%gs, #Hgs, #Hge⟩
  ihave %Hgsl := ownSlice_len $$ Hgs
  ihave %Hgel := BigSepL2.bigSepL2_length $$ Hge
  have hel : (fm.entries.length : Int) = sint.Z u.Entries'.len := by rw [← Hgel, Hgsl.1]; exact sint_nat_cast Hgsl.2
  ihave IH : iprop(∃ (kv : w64),
      "k" ∷ k_ptr ↦ kv ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z kv ∧ sint.Z kv ≤ (fm.entries.length : Int) + 1 ∧
        ((List.range fm.entries.length).drop (sint.nat kv - 1)).foldlM (kStep fm x.L0) none = .ok r⌝)
      $$ [k]
  · have h2 : (1 : Int) ≤ (fm.entries.length : Int) + 1 := by omega
    have h3 : sint.nat (W64 1) - 1 = 0 := rfl
    iexists _
    iframe
    ipureintro
    rw [sint_one, h3]
    exact ⟨Int.le_refl _, h2, by simpa using hr⟩
  wp_for IH
  obtain ⟨hk1, hk2, hkr⟩ := Hk
  have hkn : (sint.nat kv : Int) = sint.Z kv := sint_nat_cast (by omega)
  try wp_auto
  wp_if_destruct
  · have hj : sint.nat kv - 1 < fm.entries.length := by omega
    have hjk : ((sint.nat kv - 1 : Nat) : Int) + 1 = sint.Z kv := by omega
    have hy : sint.Z (u.PrevLogIndex' + kv) = fm.prevLogIndex + sint.Z kv := by
      unfold numOk numBound at hpli
      rw [sint_add (by omega) (by omega), hupli]
    rw [range_drop_cons _ _ hj, List.foldlM_cons] at hkr
    rw [hy, Hl0l]
    by_cases hgt : (x.L0.length : Int) < fm.prevLogIndex + sint.Z kv
    · rw [decide_eq_true hgt]
      have hstep : kStep fm x.L0 none (sint.nat kv - 1) = .ok (some (sint.Z kv)) := by
        simp only [kStep, Option.isSome_none, Bool.false_eq_true, ite_false, hjk, gt_iff_lt, hgt,
          decide_true, pure_ok, orM_ok_true, ok_bind, ite_true]
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ; ipureintro
      rw [hstep, ok_bind, kStep_fold_some] at hkr
      cases hkr
      simp only [Option.getD_some]
    · rw [decide_eq_false hgt]
      have hle : fm.prevLogIndex + sint.Z kv ≤ (x.L0.length : Int) := by omega
      -- the Lean evaluates `At(l0, y)`
      have hfold := hkr
      simp only [kStep, Option.isSome_none, Bool.false_eq_true, ite_false, hjk, gt_iff_lt, hgt,
        decide_false, pure_ok, orM_ok_false] at hfold
      obtain ⟨st, hst, -⟩ := bind_ok hfold
      obtain ⟨c, hc, -⟩ := bind_ok hst
      obtain ⟨e, he, -⟩ := bind_ok hc
      try wp_auto
      wp_apply wp_At l0 x.L0 (u.PrevLogIndex' + kv) e $$ [Hl0] as %ge #Hge0
      · iframe Hl0; ipureintro; rw [hy]; exact he
      iunfold entryRO at Hge0
      icases Hge0 with ⟨%Hge1, #-⟩
      have hes0 : 0 ≤ sint.Z (kv - W64 1) := by rw [sint_sub_one hk1]; omega
      have hkj : (sint.Z (kv - W64 1)).toNat = sint.nat kv - 1 := by rw [sint_sub_one hk1]; omega
      have hgsj : sint.nat kv - 1 < gs.length := by omega
      obtain ⟨gj, Hgj⟩ : ∃ g, gs[sint.nat kv - 1]? = some g := ⟨_, List.getElem?_eq_getElem hgsj⟩
      have Hxj : fm.entries[sint.nat kv - 1]? = some fm.entries[sint.nat kv - 1]! := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      ihave #Hgj := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hgj Hxj $$ Hge
      iunfold entryRO at Hgj
      icases Hgj with ⟨%Hgj1, #-⟩
      icases ownSlice_elem_acc (sint.Z (kv - W64 1)) gj u.Entries' DFrac.discard gs hes0 (by rw [hkj]; exact Hgj) $$ Hgs
        with ⟨Hel, -⟩
      iStructNamed Hel
      have hib : 0 ≤ sint.Z (kv - W64 1) ∧ sint.Z (kv - W64 1) < sint.Z u.Entries'.len := by
        rw [sint_sub_one hk1]; omega
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true hib)]
      try wp_auto
      rw [decide_w64_eq, Hge1.1, Hgj1.1]
      by_cases hne : e.term = (fm.entries[sint.nat kv - 1]!).term
      · rw [decide_eq_true hne]
        have hstep : kStep fm x.L0 none (sint.nat kv - 1) = .ok none := by
          simp only [kStep, Option.isSome_none, Bool.false_eq_true, ite_false, hjk, gt_iff_lt, hgt,
            decide_false, pure_ok, orM_ok_false, he, ok_bind, hne, bne_self_eq_false]
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        have hk' : sint.Z (kv + W64 1) = sint.Z kv + 1 := sint_add_one (by omega)
        have hkn' := sint_nat_cast (k := kv + W64 1) (by omega)
        have hk'' : sint.nat (kv + W64 1) - 1 = sint.nat kv - 1 + 1 := by omega
        rw [hk', hk'']
        have hb1 : 1 ≤ sint.Z kv + 1 := by omega
        have hb2 : sint.Z kv + 1 ≤ (fm.entries.length : Int) + 1 := by omega
        refine ⟨hb1, hb2, ?_⟩
        rw [hstep] at hkr; exact hkr
      · rw [decide_eq_false hne]
        have hstep : kStep fm x.L0 none (sint.nat kv - 1) = .ok (some (sint.Z kv)) := by
          have hne' : (e.term != (fm.entries[sint.nat kv - 1]!).term) = true := by simpa using hne
          simp only [kStep, Option.isSome_none, Bool.false_eq_true, ite_false, hjk, gt_iff_lt, hgt,
            decide_false, pure_ok, orM_ok_false, he, ok_bind, hne', ite_true]
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ; ipureintro
        rw [hstep, ok_bind, kStep_fold_some] at hkr
        cases hkr
        simp only [Option.getD_some]
  · try wp_auto
    have hdone : sint.nat kv - 1 = fm.entries.length := by omega
    rw [hdone, List.drop_eq_nil_of_le (by simp)] at hkr
    cases hkr
    iapply HΦ; ipureintro
    simp only [Option.getD_none]
    have : sint.Z (u.Entries'.len + W64 1) = sint.Z u.Entries'.len + 1 := sint_add_one (by omega)
    rw [this, ← hel]

end proof

end AntCheck
end EtcdGrove
end Perennial
