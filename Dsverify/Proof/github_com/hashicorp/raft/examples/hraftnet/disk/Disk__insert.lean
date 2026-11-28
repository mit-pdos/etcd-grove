/-
(hraft_robust R3) The proof of `disk.(*Disk).insert`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__insert
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.LogLen
public import Perennial.Golang.Theory.IfJoin

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem dk_ins_lt_step (es : List DEnt) (x : w64) (i : Nat) (f : DEnt) (hf : es[i]? = some f)
    (hlt : uint.nat f.idx < uint.nat x) (h : ∀ j < i, ∀ g, es[j]? = some g → uint.nat g.idx < uint.nat x) :
    ∀ j < i + 1, ∀ g, es[j]? = some g → uint.nat g.idx < uint.nat x := by
  intro j hj g hg
  by_cases hji : j = i
  · subst hji; rw [hf] at hg; cases hg; exact hlt
  · exact h j (by omega) g hg

theorem dk_insEnt_set (de : DEnt) (es : List DEnt) (i : Nat) (f : DEnt) (hpos : insPos de.idx es = i)
    (hf : es[i]? = some f) (heq : f.idx = de.idx) : insEnt de es = es.set i de := by
  unfold insEnt; rw [hpos, hf]; simp [heq]

theorem dk_insEnt_mid (de : DEnt) (es : List DEnt) (i : Nat) (hpos : insPos de.idx es = i)
    (hne : ∀ f, es[i]? = some f → f.idx ≠ de.idx) : insEnt de es = es.take i ++ de :: es.drop i := by
  unfold insEnt; rw [hpos]
  cases h : es[i]? with
  | none => simp
  | some f => have := hne f h; simp [this]

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.insert.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.insert.spec (GF := GF) (hG := hG) := by
  intro d I stg lv de
  wp_start as ⟨Hmem, #Hde⟩
  ihave #Hde' := Hde
  iunfold entRep at Hde'
  icases Hde' with ⟨%Hdef, -, -⟩
  iunfold diskMem at Hmem
  icases Hmem with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hentl := BigSepL2.bigSepL2_length $$ Hent
  ihave %Hmax := ownSlice_log_length_lt es lvs $$ Hes
  try wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Hes" ∷ es ↦* lvs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z es.len ∧
        ∀ j < sint.nat i, ∀ g, I.ents[j]? = some g → uint.nat g.idx < uint.nat de.idx⌝ : IProp GF) $$ [i Hes]
  · iexists W64 0; iframe; ipureintro
    exact ⟨by word, Hesl.2, fun j hj => by exfalso; rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for HI
  wp_if_join (fun v => iprop(⌜∃ c : Bool, v = #c ∧ (c = true ↔ (sint.Z i < sint.Z es.len ∧
        ∃ f, I.ents[sint.nat i]? = some f ∧ uint.nat f.idx < uint.nat de.idx))⌝ ∗
      i_ptr ↦ i ∗ d_ptr ↦ d ∗ e_ptr ↦ lv ∗ d.[Disk, go!"ents"] ↦ es ∗ es ↦* lvs)) with [i d e Hents Hes]
  · have hlt := Hif
    have hil : sint.nat i < lvs.length := dk_idx_lt i es.len _ Hesl Hi.1 hlt
    list_elem lvs (sint.nat i) as lv0
    list_elem I.ents (sint.nat i) as e0
    ihave #Her := BigSepL2.bigSepL2_lookup Hlv0_lookup He0_lookup $$ Hent
    iunfold entRep at Her
    icases Her with ⟨%Hef, -, -⟩
    icases ownSlice_elem_acc (sint.Z i) lv0 es (DFrac.own 1) lvs Hi.1
      (by rw [dk_toNat_sint]; exact Hlv0_lookup) $$ Hes with ⟨Hv, Hclose⟩
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
    try wp_auto
    ihave Hes := Hclose $$ Hv
    rw [list_set_lookup_self lvs _ lv0 (by rw [dk_toNat_sint]; exact Hlv0_lookup)]
    iframe
    ipureintro
    refine ⟨_, rfl, ?_⟩
    rw [decide_eq_true_iff]
    constructor
    · intro h; exact ⟨by first | exact hlt | trivial, e0, He0_lookup, by rw [← Hef.1, ← Hdef.1]; word⟩
    · rintro ⟨-, f, hf, hlt'⟩; rw [He0_lookup] at hf; cases hf; rw [Hef.1, Hdef.1]; word
  · iframe
    ipureintro
    refine ⟨false, rfl, ?_⟩
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; exact absurd h Hif
  · iintro %v ⟨%Hc, Hi_, Hd_, He_, Hents, Hes⟩
    obtain ⟨c, Hv, Hc⟩ := Hc
    subst Hv
    have hne : (#false : val) ≠ #true := fun h => Bool.noConfusion (go.intoVal_inj h)
    cases c with
    | true =>
      obtain ⟨hlt, f, hf, hflt⟩ := Hc.1 rfl
      rw [if_pos (decide_eq_true rfl)]
      obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i es.len Hi.1 hlt
      try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨hs2, hs3, ?_⟩
      rw [hs1]
      exact dk_ins_lt_step I.ents de.idx _ f hf hflt Hi.2.2
    | false =>
      rw [if_neg (by simp only [decide_eq_true_eq]; exact hne), if_pos (decide_eq_true rfl)]
      have hpos : insPos de.idx I.ents = sint.nat i := by
        apply insPos_eq
        · rw [← Hentl, Hesl.1]; have := Hi.2.1; word
        · exact Hi.2.2
        · intro f hf hlt'
          have hil : sint.nat i < I.ents.length := (List.getElem?_eq_some_iff.1 hf).1
          have : sint.Z i < sint.Z es.len := by
            have : sint.nat i < sint.nat es.len := by rw [← Hesl.1, Hentl]; exact hil
            word
          exact absurd (Hc.2 ⟨this, f, hf, hlt'⟩) (by simp)
      try wp_auto
      wp_bind (If (Val #(decide (sint.Z i < sint.Z es.len))) _ _)
      wp_if_join (fun v => iprop(⌜∃ c : Bool, v = #c ∧ (c = true ↔ (sint.Z i < sint.Z es.len ∧
            ∃ f, I.ents[sint.nat i]? = some f ∧ f.idx = de.idx))⌝ ∗
          i_ptr ↦ i ∗ d_ptr ↦ d ∗ e_ptr ↦ lv ∗ d.[Disk, go!"ents"] ↦ es ∗ es ↦* lvs)) with [Hi_ Hd_ He_ Hents Hes]
      · have hlt := Hif
        have hil : sint.nat i < lvs.length := dk_idx_lt i es.len _ Hesl Hi.1 hlt
        list_elem lvs (sint.nat i) as lv0
        list_elem I.ents (sint.nat i) as e0
        ihave #Her := BigSepL2.bigSepL2_lookup Hlv0_lookup He0_lookup $$ Hent
        iunfold entRep at Her
        icases Her with ⟨%Hef, -, -⟩
        icases ownSlice_elem_acc (sint.Z i) lv0 es (DFrac.own 1) lvs Hi.1
          (by rw [dk_toNat_sint]; exact Hlv0_lookup) $$ Hes with ⟨Hv, Hclose⟩
        simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
        try wp_auto
        ihave Hes := Hclose $$ Hv
        rw [list_set_lookup_self lvs _ lv0 (by rw [dk_toNat_sint]; exact Hlv0_lookup)]
        iframe
        ipureintro
        refine ⟨_, rfl, ?_⟩
        rw [decide_eq_true_iff]
        constructor
        · intro h; exact ⟨by first | exact hlt | trivial, e0, He0_lookup, by rw [← Hef.1, ← Hdef.1]; exact h⟩
        · rintro ⟨-, f, hf, heq⟩; rw [He0_lookup] at hf; cases hf; rw [Hef.1, Hdef.1]; exact heq
      · iframe
        ipureintro
        refine ⟨false, rfl, ?_⟩
        constructor
        · intro h; cases h
        · rintro ⟨h, -⟩; exact absurd h Hif
      · iintro %v ⟨%Hc2, Hi_, Hd_, He_, Hents, Hes⟩
        obtain ⟨c2, Hv, Hc2⟩ := Hc2
        subst Hv
        cases c2 with
        | true =>
          obtain ⟨hlt, f, hf, hfeq⟩ := Hc2.1 rfl
          have hil : sint.nat i < lvs.length := dk_idx_lt i es.len _ Hesl Hi.1 hlt
          list_elem lvs (sint.nat i) as lv0
          try wp_auto
          simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z es.len from ⟨Hi.1, hlt⟩, _root_.and_self, ↓reduceIte]
          wp_apply (wp_store_slice_index es (sint.Z i) lvs lv) $$ [$Hes] as Hes
          · ipureintro; refine ⟨Hi.1, ?_⟩; have := hil; have := Hesl.1; word
          try wp_auto
          iapply HΦ
          rw [dk_insEnt_set de I.ents _ f hpos hf hfeq]
          iunfold diskMem
          iexists es, ks, vs, iks, ivs, lvs.set (sint.nat i) lv, kss, vss, ikss
          rw [dk_toNat_sint]
          iframe; iframe #
          icases (BigSepL2.bigSepL2_insert_acc Hlv0_lookup hf) $$ Hent with ⟨-, Hset⟩
          iapply Hset; iexact Hde
        | false =>
          have hnf : ∀ f, I.ents[sint.nat i]? = some f → f.idx ≠ de.idx := fun f hf heq => by
            have hil : sint.nat i < I.ents.length := (List.getElem?_eq_some_iff.1 hf).1
            have : sint.Z i < sint.Z es.len := by
              have : sint.nat i < sint.nat es.len := by rw [← Hesl.1, Hentl]; exact hil
              word
            exact absurd (Hc2.2 ⟨this, f, hf, heq⟩) (by simp)
          have hm : maxAddr = 2 ^ 47 := rfl
          have hcapb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (es.len + W64 1) := by
            have := Hesl.1; have := Hesl.2; rw [hm] at Hmax; constructor <;> word
          try wp_auto
          wp_apply (wp_slice_make3 (V := Log) (W64 0) (es.len + W64 1) hcapb) as %ns ⟨Hns, Hnscap, %Hnsc⟩
          try wp_auto
          ihave %Hwf := ownSlice_wf es _ lvs $$ Hes
          simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z i ∧ sint.Z i ≤ sint.Z es.cap from
            ⟨by word, Hi.1, by have := Hi.2.1; omega⟩, ↓reduceIte]
          icases (ownSlice_split_all i es (DFrac.own 1) lvs ⟨Hi.1, Hi.2.1⟩).1 $$ Hes with ⟨Hpre, Hsuf⟩
          rw [show List.replicate 0 (Perennial.zero_val Log) = [] from rfl]
          wp_apply (wp_slice_append (V := Log)) $$ [$Hns $Hnscap $Hpre] as %n1 ⟨Hn, Hncap, -⟩
          try wp_auto
          wp_apply (wp_slice_literal (V := Log))
          isplitr
          · ipureintro; rfl
          iintro %slp ⟨Hlit, -⟩
          wp_apply (wp_slice_append (V := Log)) $$ [$Hn $Hncap $Hlit] as %n2 ⟨Hn, Hncap, -⟩
          try wp_auto
          simp only [show 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z es.len ∧ sint.Z es.len ≤ sint.Z es.cap from
            ⟨Hi.1, Hi.2.1, Hwf.2⟩, ↓reduceIte]
          wp_apply (wp_slice_append (V := Log)) $$ [$Hn $Hncap $Hsuf] as %n3 ⟨Hn, Hncap, -⟩
          try wp_auto
          iapply HΦ
          rw [dk_insEnt_mid de I.ents _ hpos hnf]
          iunfold diskMem
          iexists n3, ks, vs, iks, ivs, lvs.take (sint.nat i) ++ lv :: lvs.drop (sint.nat i), kss, vss, ikss
          simp only [List.nil_append, List.append_assoc, List.singleton_append]
          iframe; iframe #
          have hlt : (lvs.take (sint.nat i)).length = (I.ents.take (sint.nat i)).length := by simp [Hentl]
          iapply (BigSepL2.bigSepL2_append (Or.inl hlt)).1
          rw [List.take_append_drop, List.take_append_drop]
          iexact Hent

end sec

end Perennial
