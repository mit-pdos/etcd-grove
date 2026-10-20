/-
Lean-first (no Rocq counterpart).

The proof of `txnRes`: the loop appends each response's result (`tresOf`, by its operation's
kind); its invariant, the results so far; at the end the model's (`tresOf_zip`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.txnRes
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseDeleteRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrOf
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- A transaction operation's kind, read-only. -/
theorem TOp_kind_disc (l : Loc) (v : TOp) :
    (l ↦□ v : IProp GF) ⊢ l.[TOp, go!"Kind"] ↦□ v.Kind' := by
  iintro #H
  icases (AccessStrict.access_strict (A := l.[TOp, go!"Kind"] ↦□ v.Kind')
      (A' := l.[TOp, go!"Kind"] ↦□ v.Kind') (P := l ↦□ v)) $$ H with ⟨H1, -⟩
  iexact H1

theorem zipWith_take_succ {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) (j : Nat)
    (a : α) (b : β) (h1 : l1[j]? = some a) (h2 : l2[j]? = some b) :
    List.zipWith f (l1.take (j + 1)) (l2.take (j + 1)) =
      List.zipWith f (l1.take j) (l2.take j) ++ [f a b] := by
  rw [List.take_add_one, List.take_add_one, h1, h2]
  simp only [Option.toList_some]
  rw [List.zipWith_append]
  · simp
  · have := (List.getElem?_eq_some_iff.1 h1).1
    have := (List.getElem?_eq_some_iff.1 h2).1
    simp only [List.length_take]; omega

theorem txnRes.wp_proof (wp_vrOf : vrOf.spec (GF := GF) (hG := hG))
    (wp_GRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (wp_GRD : EtcdGrove.ResponseOp.GetResponseDeleteRange.spec (GF := GF) (hG := hG)) :
    txnRes.spec (GF := GF) (hG := hG) := by
  intro osl ops mops rsl ps rs ms hops hrel
  wp_start as ⟨#Hops, #Hps, #Hms⟩
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave ⟨%Hpl, #Hmall⟩ := opRespsMsg_getElem ps ms $$ Hms
  obtain ⟨hml, hrel_el⟩ := opRespsRel_getElem false _ rs ms hrel
  rw [List.length_map] at hml
  have hol : mops.length = ops.length := decAll_length _ _ _ hops
  ihave %Hol := ownSlice_len $$ Hops
  ihave %Hrl := ownSlice_len $$ Hps
  wp_auto
  wp_apply wp_slice_make3 (V := TRes) (W64 0) rsl.len ⟨by word, by word⟩ as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  rename_i iv_ptr
  irename : (iv_ptr ↦ zero_val w64 : IProp GF) => Hiv
  ihave HI : (∃ (j : w64) (r1 : Loc) (os : GoSlice) (iv : w64),
      "i" ∷ i_ptr ↦ j ∗ "r" ∷ r_ptr ↦ r1 ∗ "res" ∷ res_ptr ↦ os ∗ "Hiv" ∷ iv_ptr ↦ iv ∗
      "Hos" ∷ os ↦* List.zipWith tresOf (ops.take (sint.nat j)) (ms.take (sint.nat j)) ∗
      "Hoscap" ∷ ownSliceCap TRes os (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rsl.len⌝ : IProp GF)
    $$ [i r res Ho Hocap Hiv]
  · iexists W64 0, _, o0, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.take_zero]
    iframe
    ipureintro; word
  wp_for HI
  by_cases Hif : sint.Z j < sint.Z rsl.len
  · (try simp only [decide_eq_true Hif]); wp_pures; cleanup_bool_decide
    (try wp_auto); cleanup_bool_decide
    list_elem ps (sint.nat j) as p
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rsl.len from ⟨Hj.1, Hif⟩)]
    wp_apply wp_load_slice_index rsl (sint.Z j) ps DFrac.discard p Hj.1 $$ [Hps] as -
    · iframe Hps; ipureintro; exact Hp_lookup
    have hjo : sint.nat j < ops.length := by
      rw [← hol, hml, ← Hpl, Hrl.1]; word
    obtain ⟨m, Hm⟩ : ∃ m, ms[sint.nat j]? = some m := by
      have : sint.nat j < ms.length := by rw [← Hpl, Hrl.1]; word
      exact ⟨ms[sint.nat j], List.getElem?_eq_getElem this⟩
    obtain ⟨op, Hop⟩ : ∃ op, ops[sint.nat j]? = some op :=
      ⟨ops[sint.nat j], List.getElem?_eq_getElem hjo⟩
    obtain ⟨mop, hmop, hmopj⟩ := decAll_getElem decTOp ops mops hops (sint.nat j) op Hop
    obtain ⟨r, -, hr⟩ := hrel_el (sint.nat j) (linkv.tOpOf mop) m
      (by rw [List.getElem?_map, hmopj]; rfl) Hm
    ihave Hw := (ownSlice_elem_acc (sint.Z j) op osl DFrac.discard ops Hj.1 Hop) $$ Hops
    icases Hw with ⟨#Hw, -⟩
    ihave #Hk := TOp_kind_disc _ op $$ Hw
    have Htk := zipWith_take_succ tresOf ops ms (sint.nat j) op m Hop Hm
    have Hlt : sint.Z j < sint.Z osl.len := by have := Hol.1; word
    -- the step: the result appended, the invariant at `j + 1`
    have Hpost : ∀ (t : TRes), t = tresOf op m →
        ∀ os', (os' ↦* (List.zipWith tresOf (ops.take (sint.nat j)) (ms.take (sint.nat j)) ++ [t]) :
          IProp GF) ⊢ os' ↦* List.zipWith tresOf (ops.take (sint.nat (j + W64 1)))
            (ms.take (sint.nat (j + W64 1))) := by
      intro t ht os'
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, Htk, ht]
    -- the response's shape, by the operation's kind
    unfold decTOp at hmop
    have Hshape : (op.Kind' = W64 0 ∧ ∃ rev kvs more count, m = .range rev kvs more count) ∨
        (op.Kind' ≠ W64 0 ∧ op.Kind' = W64 1) ∨
        (op.Kind' ≠ W64 0 ∧ op.Kind' ≠ W64 1 ∧ ∃ rev n prevs, m = .delete rev n prevs) := by
      by_cases hk0 : op.Kind' = W64 0
      · rw [if_pos hk0] at hmop
        cases hmop
        left
        refine ⟨hk0, ?_⟩
        cases m with
        | range a b c d => exact ⟨a, b, c, d, rfl⟩
        | _ => simp [linkv.tOpOf, client.opRespRel] at hr
      · rw [if_neg hk0] at hmop
        by_cases hk1 : op.Kind' = W64 1
        · exact Or.inr (Or.inl ⟨hk0, hk1⟩)
        · rw [if_neg hk1] at hmop
          have hk2 : op.Kind' = W64 2 := by
            by_cases e : op.Kind' = W64 2
            · exact e
            · rw [if_neg e] at hmop; cases hmop
          rw [if_pos hk2] at hmop
          cases hmop
          right; right
          refine ⟨hk0, hk1, ?_⟩
          cases m with
          | delete a b c => exact ⟨a, b, c, rfl⟩
          | _ => simp [linkv.tOpOf, client.opRespRel] at hr
    (try wp_auto)
    simp only [decide_eq_true Hlt]
    wp_pures
    have Hb'' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    simp only [Hb'', _root_.and_self, ↓reduceIte]
    wp_auto
    rcases Hshape with ⟨hk0, rev, kvs, more, count, rfl⟩ | ⟨hk0, hk1⟩ |
      ⟨hk0, hk1, rev, n, prevs, rfl⟩
    · -- a get: its response is a range's
      ihave #HmM := Hmall $$ %(sint.nat j) %p %(.range rev kvs more count) %Hp_lookup %Hm
      iunfold opRespMsg at HmM
      icases HmM with ⟨%Hpn, %w, %rr, #Hresp, #Hrr, #Hrri⟩
      iunfold txn.rangeResponseIs at Hrri
      icases Hrri with ⟨%Hrrn, %h, %sl, %ps', #Hh, %Hhn, #Hrev, #Hkvsf, #Hsl, #Hkvsi, #Hmore, #Hcount⟩
      iunfold txn.kvsIs at Hkvsi
      icases Hkvsi with ⟨%Hlen', #Hall'⟩
      ihave %Hsll := ownSlice_len $$ Hsl
      wp_if_destruct
      · wp_apply wp_GRR p w rr $$ []
        · iframe #; ipureintro; exact Hpn
        (try wp_auto)
        simp only [show decide (rr = null) = false from decide_eq_false Hrrn, Bool.not_false]
        wp_pures
        (try wp_auto)
        by_cases Hne : sint.Z (W64 0) < sint.Z sl.len
        · -- a key-value: found
          simp only [decide_eq_true Hne]
          wp_pures
          (try wp_auto)
          obtain ⟨p0, Hp0⟩ : ∃ p0, ps'[0]? = some p0 := by
            have : 0 < ps'.length := by have := Hsll.1; word
            exact ⟨ps'[0], List.getElem?_eq_getElem this⟩
          obtain ⟨kv0, Hkv0⟩ : ∃ kv0, kvs[0]? = some kv0 := by
            have : 0 < kvs.length := by
              rw [← Hlen']; exact List.length_pos_of_mem (List.mem_of_getElem? Hp0)
            exact ⟨kvs[0], List.getElem?_eq_getElem this⟩
          ihave #Hkv := Hall' $$ %0 %p0 %kv0 %Hp0 %Hkv0
          iunfold txn.kvIs at Hkv
          icases Hkv with ⟨%kSl, %vSl, -, -, -, #HmF, #HvF, #HvalF, #HvS, -⟩
          have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
            have := Hsll.1
            constructor <;> word
          simp only [Hbnd0, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
          · iframe Hsl; ipureintro; exact Hp0
          (try wp_auto)
          wp_apply wp_vrOf vSl kv0.value DFrac.discard kv0.modRev kv0.version $$ [HvS] as -
          · iframe #
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hl1, _⟩
          wp_apply wp_slice_append $$ [$Hos $Hoscap $Hl1] as %os' ⟨Hos, Hoscap, -⟩
          have ht : tresOf op (.range rev kvs more count) = getRes (kvVR kv0, true) := by
            obtain ⟨tl, rfl⟩ : ∃ tl, kvs = kv0 :: tl := by
              cases kvs with
              | nil => simp at Hkv0
              | cons a l => simp only [List.getElem?_cons_zero, Option.some.injEq] at Hkv0; exact ⟨l, by rw [Hkv0]⟩
            simp only [tresOf, if_pos hk0]
          ihave Hos := Hpost _ (by rw [ht]; rfl) os' $$ Hos
          wp_for_post
          iframe
          iexists j + W64 1, _, os', _
          iframe
          ipureintro; word
        · -- none
          simp only [decide_eq_false Hne]
          wp_pures
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hl1, _⟩
          wp_apply wp_slice_append $$ [$Hos $Hoscap $Hl1] as %os' ⟨Hos, Hoscap, -⟩
          have hnil : kvs = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [← Hlen', Hsll.1]; word
          have ht : tresOf op (.range rev kvs more count) = getRes (zVR, false) := by
            rw [hnil]; simp only [tresOf, if_pos hk0]
          ihave Hos := Hpost _ (by rw [ht]; rfl) os' $$ Hos
          wp_for_post
          iframe
          iexists j + W64 1, _, os', _
          iframe
          ipureintro; word
      · exfalso; exact Hif hk0
    · -- a put
      wp_if_destruct
      · exfalso; exact hk0 Hif
      wp_if_destruct
      · (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Hos $Hoscap $Hl1] as %os' ⟨Hos, Hoscap, -⟩
        ihave Hos := Hpost _ (by simp only [tresOf, if_neg hk0, if_pos hk1]; rfl) os' $$ Hos
        wp_for_post
        iframe
        iexists j + W64 1, _, os', _
        iframe
        ipureintro; word
      · exfalso; exact Hif hk1
    · -- a delete: its response is a delete's
      ihave #HmM := Hmall $$ %(sint.nat j) %p %(.delete rev n prevs) %Hp_lookup %Hm
      iunfold opRespMsg at HmM
      icases HmM with ⟨%Hpn, %w, %dr, #Hresp, #Hdr, %Hdrn, %h, %sl, %ps', #Hh, %Hhn, #Hrev, #Hdel, -⟩
      wp_if_destruct
      · exfalso; exact hk0 Hif
      wp_if_destruct
      · exfalso; exact hk1 Hif
      (try wp_auto)
      wp_apply wp_GRD p w dr $$ []
      · iframe #; ipureintro; exact Hpn
      (try wp_auto)
      simp only [show decide (dr = null) = false from decide_eq_false Hdrn, Bool.not_false]
      wp_pures
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_apply wp_slice_append $$ [$Hos $Hoscap $Hl1] as %os' ⟨Hos, Hoscap, -⟩
      ihave Hos := Hpost _ (by simp only [tresOf, if_neg hk0, if_neg hk1]; rfl) os' $$ Hos
      wp_for_post
      iframe
      iexists j + W64 1, _, os', _
      iframe
      ipureintro; word
  · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
    cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
    have hj : sint.nat j = ms.length := by rw [← Hpl, Hrl.1]; word
    have h1 : ops.take (sint.nat j) = ops := List.take_of_length_le (by omega)
    have h2 : ms.take (sint.nat j) = ms := List.take_of_length_le (by omega)
    rw [h1, h2, tresOf_zip ops mops hops rs ms hrel]
    iapply HΦ
    iframe
end proof

end linkvtxn
end EtcdGrove
end Perennial
