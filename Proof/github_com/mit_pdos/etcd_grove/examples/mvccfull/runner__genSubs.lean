/- Lean-first (no Rocq counterpart). The proof of `runner.genSubs`: Draft, to come.

The outline: `choose(3)` for the count, then per iteration `choose(3)`: `genKey`, the
checks against the puts and deletes so far (`inRange`), `newVal`, `genLease`; `genKey`, `genEnd`;
`genRange`; `append`s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genSubs
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newVal
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inRange

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section lemmas
variable [GooseExts]

/-- The keys of the puts among `sms`, in order (`genSubs`' `puts`). -/
def putKeys (sms : List SubM) : List GoString :=
  (sms.filter (fun x => decide (x.kind = W64 0))).map (·.key)

/-- The deletes among `sms`, in order (`genSubs`' `dels`). -/
def delsOf (sms : List SubM) : List SubM := sms.filter (fun x => decide (x.kind = W64 1))

theorem putKeys_snoc (sms : List SubM) (b : SubM) :
    putKeys (sms ++ [b]) = putKeys sms ++ (if b.kind = W64 0 then [b.key] else []) := by
  unfold putKeys
  rw [List.filter_append, List.map_append]
  by_cases h : b.kind = W64 0
  · rw [if_pos h, List.filter_cons_of_pos (by simpa using h)]; rfl
  · rw [if_neg h, List.filter_cons_of_neg (by simpa using h)]; rfl

theorem delsOf_snoc (sms : List SubM) (b : SubM) :
    delsOf (sms ++ [b]) = delsOf sms ++ (if b.kind = W64 1 then [b] else []) := by
  unfold delsOf
  rw [List.filter_append]
  by_cases h : b.kind = W64 1
  · rw [if_pos h, List.filter_cons_of_pos (by simpa using h)]; rfl
  · rw [if_neg h, List.filter_cons_of_neg (by simpa using h)]; rfl

theorem mem_putKeys {sms : List SubM} {a : SubM} (ha : a ∈ sms) (hk : a.kind = W64 0) :
    a.key ∈ putKeys sms := by
  unfold putKeys; exact List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, by simp [hk]⟩, rfl⟩

theorem mem_delsOf {sms : List SubM} {a : SubM} (ha : a ∈ sms) (hk : a.kind = W64 1) :
    a ∈ delsOf sms := by
  unfold delsOf; exact List.mem_filter.2 ⟨ha, by simp [hk]⟩

theorem subsOk_nil (ks : List GoString) (L : List w64) : subsOk ks L [] := by
  refine ⟨by simp, fun i j a b _ ha _ => by simp at ha⟩

/-- **Appending a sub-operation that passes `genSubs`' checks.** -/
theorem subsOk_snoc {ks : List GoString} {L : List w64} {sms : List SubM} {b : SubM}
    (h : subsOk ks L sms) (hb : b.kind = W64 0 → b.key ∈ ks ∧ (b.lease = W64 0 ∨ b.lease ∈ L))
    (hput : b.kind = W64 0 → ∀ a ∈ sms, (a.kind = W64 0 → a.key ≠ b.key) ∧
      (a.kind = W64 1 → inRangeM a.endNil a.key a.e b.key = false))
    (hdel : b.kind = W64 1 → ∀ a ∈ sms, a.kind = W64 0 → inRangeM b.endNil b.key b.e a.key = false) :
    subsOk ks L (sms ++ [b]) := by
  refine ⟨fun x hx => ?_, fun i j a c hij ha hc => ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact h.1 x hx
    · simp at hx; subst hx; exact hb
  · have hi : i < sms.length := by
      rcases Nat.lt_or_ge i sms.length with hi | hi
      · exact hi
      · exfalso
        have : (sms ++ [b])[j]? = none := by
          rw [List.getElem?_eq_none]; simp; omega
        rw [this] at hc; exact absurd hc (by simp)
    rw [List.getElem?_append_left hi] at ha
    have ham : a ∈ sms := List.mem_of_getElem? ha
    rcases Nat.lt_or_ge j sms.length with hj | hj
    · rw [List.getElem?_append_left hj] at hc
      exact h.2 i j a c hij ha hc
    · have hj' : j = sms.length := by
        rcases Nat.lt_or_ge j (sms.length + 1) with h' | h'
        · omega
        · exfalso
          have : (sms ++ [b])[j]? = none := by rw [List.getElem?_eq_none]; simp; omega
          rw [this] at hc; exact absurd hc (by simp)
      subst hj'
      rw [List.getElem?_append_right (Nat.le_refl _)] at hc
      simp at hc; subst hc
      refine ⟨fun h0 h1 => (hput h1 a ham).1 h0, fun h0 h1 => (hput h1 a ham).2 h0,
        fun h0 h1 => hdel h1 a ham h0⟩

theorem all_take_succ {α : Type} (l : List α) (i : Nat) (hi : i < l.length) (p : α → Bool) :
    (l.take (i + 1)).all p = ((l.take i).all p && p l[i]) := by
  rw [List.take_succ_eq_append_getElem hi, List.all_append]; simp

theorem zip_fst_snd {α β : Type} (xs : List (α × β)) :
    (xs.map Prod.fst).zip (xs.map Prod.snd) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.genSubs.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_inRange : inRange.spec (GF := GF) (hG := hG))
    (wp_newVal : runner.newVal.spec (GF := GF) (hG := hG))
    (wp_genLease : runner.genLease.spec (GF := GF) (hG := hG))
    (wp_genEnd : runner.genEnd.spec (GF := GF) (hG := hG))
    (wp_genRange : runner.genRange.spec (GF := GF) (hG := hG)) :
    runner.genSubs.spec (GF := GF) (hG := hG) := by
  intro x ks cfg mp rv c sl L nv h0 h1 h2
  wp_start as ⟨Hks, Hmix, Hrv, Hc, Hls, Hsl, Hnv⟩
  iunfold runnerRangeMix at Hmix
  icases Hmix with ⟨#Hcfg, %wrr, #Hwrr⟩
  iunfold runnerKeys at Hks
  icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hne⟩
  wp_auto
  wp_apply wp_choose (W64 3) as %cn %Hcn
  (try wp_auto)
  have hn3 : 1 ≤ sint.Z (W64 1 + cn) ∧ sint.Z (W64 1 + cn) ≤ 3 := by
    have := Hcn.2.1 (by decide)
    have : sint.Z (W64 3) = 3 := by decide
    have := Hcn.1
    constructor <;> word
  ihave HI : (∃ (jj : w64) (ssl psl dsl : GoSlice) (xs ds : List (subOp × SubM)) (nv' : w64),
      "j" ∷ j_ptr ↦ jj ∗ "subs" ∷ subs_ptr ↦ ssl ∗ "Hss" ∷ ssl ↦* xs.map Prod.fst ∗
      "Hssc" ∷ ownSliceCap subOp ssl (DFrac.own 1) ∗
      "puts" ∷ puts_ptr ↦ psl ∗ "Hps" ∷ psl ↦* putKeys (xs.map Prod.snd) ∗
      "Hpsc" ∷ ownSliceCap GoString psl (DFrac.own 1) ∗
      "dels" ∷ dels_ptr ↦ dsl ∗ "Hds" ∷ dsl ↦* ds.map Prod.fst ∗
      "Hdsc" ∷ ownSliceCap subOp dsl (DFrac.own 1) ∗
      "#Hxs" ∷ ([∗list] y ∈ xs, subIs y.1 y.2) ∗ "#Hdi" ∷ ([∗list] y ∈ ds, subIs y.1 y.2) ∗
      "Hnv" ∷ rF go!"vals" x ↦ nv' ∗ "Hrv" ∷ mF go!"rev" mp ↦ rv ∗ "Hc" ∷ mF go!"cmp" mp ↦ c ∗
      "Hls" ∷ mF go!"leases" mp ↦ sl ∗ "Hsl" ∷ sl ↦* L ∗
      "x" ∷ x_ptr ↦ x ∗ "m" ∷ m_ptr ↦ mp ∗ "n" ∷ n_ptr ↦ (W64 1 + cn) ∗
      "res" ∷ «$res0_ptr» ↦ (zero_val GoSlice) ∗
      "HΦ" ∷ (∀ ss : GoSlice, (mF go!"rev" mp ↦ rv ∗ mF go!"cmp" mp ↦ c ∗
        mF go!"leases" mp ↦ sl ∗ sl ↦* L ∗
        ∃ (svs : List subOp) (sms : List SubM) (nv' : w64), ss ↦*□ svs ∗
          ([∗list] y ∈ svs.zip sms, subIs y.1 y.2) ∗ rF go!"vals" x ↦ nv' ∗
          ⌜svs.length = sms.length ∧ 1 ≤ sms.length ∧ sms.length ≤ 3 ∧ subsOk ks L sms ∧
            sint.Z nv ≤ sint.Z nv' ∧ sint.Z nv' ≤ sint.Z nv + 3⌝) -∗ Φ #ss) ∗
      "%Hinv" ∷ ⌜ds.map Prod.snd = delsOf (xs.map Prod.snd) ∧ subsOk ks L (xs.map Prod.snd) ∧
        xs.length ≤ sint.nat jj ∧ (jj ≠ W64 0 → 1 ≤ xs.length) ∧ 0 ≤ sint.Z jj ∧
        sint.Z jj ≤ sint.Z (W64 1 + cn) ∧ sint.Z nv ≤ sint.Z nv' ∧
        sint.Z nv' ≤ sint.Z nv + sint.Z jj⌝ : IProp GF) $$ [-]
  · iexists W64 0, slice.nil, slice.nil, slice.nil, [], [], nv
    iframe
    simp only [List.map_nil, putKeys, delsOf, List.filter_nil]
    isplitl; · iapply ownSlice_nil
    isplitl; · iapply ownSliceCap_nil
    isplitl; · iapply ownSlice_nil
    isplitl; · iapply ownSliceCap_nil
    isplitl; · iapply ownSlice_nil
    isplitl; · iapply ownSliceCap_nil
    isplitr; · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitr; · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro
    have hz : sint.Z (W64 0) = 0 := by decide
    refine ⟨by simp, subsOk_nil ks L, by simp, fun h => absurd rfl h, by omega,
      by omega, Int.le_refl _, by omega⟩
  wp_for HI
  by_cases Hlt : sint.Z jj < sint.Z (W64 1 + cn)
  · simp only [Hlt, decide_True_any, ↓reduceIte]
    obtain ⟨Hds_eq, hok, hlen, hne, hj0, hjn, hv1, hv2⟩ := Hinv
    have hj1 : sint.Z (jj + W64 1) = sint.Z jj + 1 := by word
    have hj1n : sint.nat (jj + W64 1) = sint.nat jj + 1 := by
      have h4 : ∀ w : w64, sint.nat w = (sint.Z w).toNat := fun _ => rfl
      rw [h4, h4, hj1]; omega
    (try wp_auto)
    wp_apply wp_choose (W64 3) as %sw %Hsw
    (try wp_auto)
    wp_if_destruct
    · -- a put
      wp_apply wp_genKey x ks as %ksl ⟨%kk, Hk, %Hkk⟩
      · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
      imod ownSlice_persist $$ Hk with #Hk
      (try wp_auto)
      ihave %Hpsn := ownSlice_len $$ Hps
      ihave HI2 : (∃ (ii : w64) (pv : GoString), "i" ∷ i_ptr ↦ ii ∗ "p" ∷ p_ptr ↦ pv ∗
          "ok" ∷ ok_ptr ↦ (((putKeys (xs.map Prod.snd)).take (sint.nat ii)).all
            fun q => decide (q ≠ kk)) ∗
          "%Hii" ∷ ⌜0 ≤ sint.Z ii⌝ : IProp GF) $$ [i p ok]
      · iexists W64 0, _; iframe; ipureintro; decide
      wp_for HI2
      by_cases Hlt2 : sint.Z ii < sint.Z psl.len
      · rw [decide_eq_true Hlt2]; simp only [↓reduceIte]
        have hil : (sint.Z ii).toNat < (putKeys (xs.map Prod.snd)).length := by
          have h4 : sint.nat psl.len = (sint.Z psl.len).toNat := rfl
          have := Hpsn.1; omega
        have hb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z psl.len := ⟨Hii, Hlt2⟩
        (try wp_auto)
        (try simp only [hb, _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index psl (sint.Z ii) (putKeys (xs.map Prod.snd)) (DFrac.own 1)
          ((putKeys (xs.map Prod.snd))[(sint.Z ii).toNat]'hil) Hii $$ [Hps] as Hps
        · iframe; ipureintro; exact List.getElem?_eq_getElem hil
        (try wp_auto)
        wp_apply (wp_bytes_to_string ksl kk DFrac.discard) $$ [Hk] as -
        · iexact Hk
        (try wp_auto)
        have hstep := all_take_succ (putKeys (xs.map Prod.snd)) (sint.nat ii) hil
          (fun q => decide (q ≠ kk))
        have hi1 : sint.nat (ii + W64 1) = sint.nat ii + 1 := by
          have := Hpsn.2; word
        have hii : sint.nat ii = (sint.Z ii).toNat := rfl
        wp_if_destruct
        · (try wp_auto)
          wp_for_post
          iframe
          iexists ii + W64 1, _
          iframe
          rw [hi1, hstep]
          simp only [← hii, ne_eq, not_true_eq_false, decide_false, Bool.and_false]
          iframe
          ipureintro; word
        · (try wp_auto)
          wp_for_post
          iframe
          iexists ii + W64 1, _
          iframe
          rw [hi1, hstep]
          simp only [Hif, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
          iframe
          ipureintro; word
      · rw [decide_eq_false Hlt2]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hall : (putKeys (xs.map Prod.snd)).take (sint.nat ii) = putKeys (xs.map Prod.snd) := by
          apply List.take_of_length_le
          have h4 : sint.nat psl.len = (sint.Z psl.len).toNat := rfl
          have hii : sint.nat ii = (sint.Z ii).toNat := rfl
          omega
        rw [hall]
        (try wp_auto)
        ihave %Hdsn := ownSlice_len $$ Hds
        ihave HI3 : (∃ (ii : w64) (dv : subOp), "i" ∷ i_ptr ↦ ii ∗ "d" ∷ d_ptr ↦ dv ∗
            "ok" ∷ ok_ptr ↦ (((putKeys (xs.map Prod.snd)).all fun q => decide (q ≠ kk)) &&
              (((ds.map Prod.snd).take (sint.nat ii)).all
                fun d => !inRangeM d.endNil d.key d.e kk)) ∗
            "%Hii" ∷ ⌜0 ≤ sint.Z ii⌝ : IProp GF) $$ [i d ok]
        · iexists W64 0, _
          have h0' : sint.nat (W64 0) = 0 := rfl
          simp only [h0', List.take_zero, List.all_nil, Bool.and_true]
          iframe; ipureintro; decide
        wp_for HI3
        by_cases Hlt3 : sint.Z ii < sint.Z dsl.len
        · simp only [Hlt3, decide_True_any, decide_eq_self_any, ↓reduceIte]
          have hi1 : sint.nat (ii + W64 1) = sint.nat ii + 1 := by
            have := Hdsn.2; word
          have hil : (sint.Z ii).toNat < ds.length := by
            have h4 : sint.nat dsl.len = (sint.Z dsl.len).toNat := rfl
            have := Hdsn.1; simp only [List.length_map] at this; omega
          have hb : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z dsl.len := ⟨Hii, Hlt3⟩
          (try wp_auto)
          (try simp only [hb, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index dsl (sint.Z ii) (ds.map Prod.fst) (DFrac.own 1)
            (ds[(sint.Z ii).toNat]'hil).1 Hii $$ [Hds] as Hds
          · iframe; ipureintro; rw [List.getElem?_map, List.getElem?_eq_getElem hil]; rfl
          ihave #Hd := BigSepL.bigSepL_lookup (Φ := fun _ y => subIs (GF := GF) y.1 y.2)
            (List.getElem?_eq_getElem hil) $$ Hdi
          iunfold subIs at Hd
          icases Hd with ⟨#Hdk, #Hde, -, %Hdp⟩
          (try wp_auto)
          wp_apply (wp_bytes_to_string ksl kk DFrac.discard) $$ [Hk] as -
          · iexact Hk
          (try wp_auto)
          wp_apply wp_inRange _ _ (ds[(sint.Z ii).toNat]'hil).2.key (ds[(sint.Z ii).toNat]'hil).2.e kk
            DFrac.discard DFrac.discard $$ [Hdk Hde] as -
          · iframe #
          rw [← Hdp.2.1]
          have hil' : sint.nat ii < (ds.map Prod.snd).length := by rw [List.length_map]; exact hil
          have hstep := all_take_succ (ds.map Prod.snd) (sint.nat ii) hil'
            (fun d => !inRangeM d.endNil d.key d.e kk)
          have hii : sint.nat ii = (sint.Z ii).toNat := rfl
          rw [List.getElem_map] at hstep
          generalize hin : inRangeM (ds[(sint.Z ii).toNat]'hil).2.endNil (ds[(sint.Z ii).toNat]'hil).2.key
            (ds[(sint.Z ii).toNat]'hil).2.e kk = bb
          cases bb
          · (try wp_auto)
            wp_for_post
            iframe
            iexists ii + W64 1, _
            iframe
            rw [hi1, hstep]
            simp only [hii, hin, Bool.not_false, Bool.and_true]
            iframe
            ipureintro; word
          · (try wp_auto)
            wp_for_post
            iframe
            iexists ii + W64 1, _
            iframe
            rw [hi1, hstep]
            simp only [hii, hin, Bool.not_true, Bool.and_false]
            iframe
            ipureintro; word
        · simp only [Hlt3, decide_False_any, intoVal_eq_iff, decide_eq_self_any, Bool.false_eq_true,
            decide_false, ↓reduceIte]
          have hall : (ds.map Prod.snd).take (sint.nat ii) = ds.map Prod.snd := by
            apply List.take_of_length_le
            have h4 : sint.nat dsl.len = (sint.Z dsl.len).toNat := rfl
            have hii : sint.nat ii = (sint.Z ii).toNat := rfl
            have := Hdsn.1; simp only [List.length_map] at this ⊢; omega
          rw [hall]
          (try wp_auto)
          generalize hokb : (((putKeys (xs.map Prod.snd)).all fun q => !decide (q = kk)) &&
            (ds.map Prod.snd).all fun d => !inRangeM d.endNil d.key d.e kk) = okb
          cases okb
          · (try wp_auto)
            wp_for_post
            iframe
            iexists jj + W64 1, ssl, psl, dsl, xs, ds, nv'
            iframe; iframe #
            ipureintro
            refine ⟨Hds_eq, hok, by omega, fun _ => ?_, by word, by word, hv1, by word⟩
            by_cases hjz : jj = W64 0
            · exfalso
              have hx0 : xs = [] := by
                subst hjz; exact List.eq_nil_of_length_eq_zero (by have : sint.nat (W64 0) = 0 := rfl; omega)
              subst hx0
              have hd0 : ds = [] := by
                have : ds.map Prod.snd = [] := by rw [Hds_eq]; rfl
                exact List.map_eq_nil_iff.1 this
              subst hd0
              simp [putKeys] at hokb
            · have := hne hjz; omega
          · (try wp_auto)
            wp_apply (wp_bytes_to_string ksl kk DFrac.discard) $$ [Hk] as -
            · iexact Hk
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %psl1 ⟨Hpsl1, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hps $Hpsc $Hpsl1] as %psl' ⟨Hps, Hpsc, -⟩
            (try wp_auto)
            have hnv0 : 0 ≤ sint.Z nv' := by omega
            have hnv1 : sint.Z nv' + 1 < 2 ^ 63 := by
              have : sint.Z jj < 3 := by omega
              omega
            wp_apply wp_newVal x cfg nv' hnv0 hnv1 $$ [Hnv] as %vl Hnv
            · iframe; iexact Hcfg
            (try wp_auto)
            wp_apply wp_genLease x mp sl L $$ [Hls Hsl] as %l ⟨Hls, Hsl, %Hl⟩
            · iframe
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %ssl1 ⟨Hssl1, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hss $Hssc $Hssl1] as %ssl' ⟨Hss, Hssc, -⟩
            (try wp_auto)
            wp_for_post
            let b : SubM := ⟨W64 0, kk, [], true, vl, l, ⟨[], [], true, zeroValDef⟩⟩
            have hb0 : b.kind = W64 0 := rfl
            have hb1 : ¬ b.kind = W64 1 := by show ¬ (W64 0 : w64) = W64 1; decide
            ihave #Hnew : subIs (GF := GF)
                (subOp.mk (W64 0) ksl slice.nil vl l zeroValDef) b $$ []
            · iunfold subIs
              iframe #
              isplitr; · iapply ownSlice_nil
              isplitr
              · iunfold rangeIs
                isplitr; · iapply ownSlice_nil
                isplitr; · iapply ownSlice_nil
                ipureintro; exact ⟨rfl, rfl⟩
              ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
            iframe
            iexists jj + W64 1, ssl', psl', dsl, xs ++ [(_, b)], ds, nv' + W64 1
            simp only [List.map_append, List.map_cons, List.map_nil, putKeys_snoc, delsOf_snoc,
              hb0, hb1, ↓reduceIte, List.append_nil]
            iframe
            isplitr
            · iapply BigSepL.bigSepL_snoc.2; iframe #
            iframe #
            ipureintro
            simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hokb
            have h01 : ¬ (W64 0 : w64) = W64 1 := by decide
            refine ⟨by rw [if_neg h01, List.append_nil]; exact Hds_eq, ?_,
              by simp only [List.length_append, List.length_singleton]; rw [hj1n]; omega,
              fun _ => by simp, by word, by word, by word, by word⟩
            refine subsOk_snoc hok (fun _ => ⟨Hkk, Hl⟩) (fun _ a ha => ⟨fun h0 => ?_, fun h1 => ?_⟩)
              (fun h => absurd h hb1)
            · exact hokb.1 _ (mem_putKeys ha h0)
            · exact hokb.2 _ (by rw [Hds_eq]; exact mem_delsOf ha h1)
    · sorry
  · simp only [Hlt, decide_False_any, decide_True_any, intoVal_eq_iff, decide_eq_self_any, Bool.false_eq_true,
      decide_false, ↓reduceIte]
    imod ownSlice_persist $$ Hss with #Hss
    (try wp_auto)
    iapply HΦ
    iframe
    iexists xs.map Prod.fst, xs.map Prod.snd
    rw [zip_fst_snd]
    iframe #
    ipureintro
    obtain ⟨_, hok, hlen, hne, hj0, hjn, hv1, hv2⟩ := Hinv
    have hjj : jj ≠ W64 0 := by
      intro h; subst h; have : sint.Z (W64 0) = 0 := (by decide)
      omega
    have h4 : sint.nat jj = (sint.Z jj).toNat := rfl
    refine ⟨by simp, by simpa using hne hjj, by simp; omega, hok, hv1, by omega⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
