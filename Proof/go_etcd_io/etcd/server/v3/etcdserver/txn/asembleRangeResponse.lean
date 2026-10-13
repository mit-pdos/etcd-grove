/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.asembleRangeResponse

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.kvsAt_take' (l : List (Loc × EtcdKv)) (n : Nat) :
    txn.kvsAt (GF := GF) l ⊢ txn.kvsAt (l.take n) := by
  unfold txn.kvsAt
  refine (BigSepL.bigSepL_take_drop (n := n)).1.trans ?_
  iintro ⟨H, -⟩
  iexact H

theorem txn.kvsAt_append' (A B : List (Loc × EtcdKv)) :
    txn.kvsAt (GF := GF) (A ++ B) ⊣⊢ txn.kvsAt A ∗ txn.kvsAt B := by
  unfold txn.kvsAt; exact BigSepL.bigSepL_append

/-- An owned key-value, made read-only. -/
theorem txn.kvAt_persist' (p : Loc) (v : EtcdKv) :
    txn.kvAt (GF := GF) p v ⊢ |==> txn.kvIs p v := by
  simp only [txn.kvAt, mvcc.kvPtrIs, ↓reduceIte]
  iintro ⟨%ks, %st, %uf, %sc, #Hk, %vsl, #Hv, Hp⟩
  iStructNamed Hp
  ipersist Key
  ipersist CreateRevision
  ipersist ModRevision
  ipersist Version
  ipersist Value
  ipersist Lease
  imodintro
  unfold txn.kvIs
  iexists ks, vsl
  iframe #

theorem txn.kvsIs_cons' (p : Loc) (ps : List Loc) (v : EtcdKv) (vs : List EtcdKv) :
    txn.kvIs (GF := GF) p v ∗ txn.kvsIs ps vs ⊢ txn.kvsIs (p :: ps) (v :: vs) := by
  unfold txn.kvsIs
  iintro ⟨#H1, %Hl, #H2⟩
  isplitl []
  · ipureintro; simp [Hl]
  imodintro
  iintro %i %q %w %hq %hw
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hq hw
    subst hq; subst hw; iexact H1
  | succ i =>
    simp only [List.getElem?_cons_succ] at hq hw
    iapply H2 $$ %i %q %w %hq %hw

/-- Owned key-values, made read-only. -/
theorem txn.kvsAt_persist' (l : List (Loc × EtcdKv)) :
    txn.kvsAt (GF := GF) l ⊢ |==> txn.kvsIs (l.map Prod.fst) (l.map Prod.snd) := by
  induction l with
  | nil =>
    iintro -
    imodintro
    unfold txn.kvsIs
    isplitl []
    · ipureintro; rfl
    imodintro
    iintro %i %q %w %hq
    simp at hq
  | cons x l ih =>
    iintro H
    icases (txn.kvsAt_cons _ _).1 $$ H with ⟨Hx, H⟩
    imod txn.kvAt_persist' _ _ $$ Hx with #Hx
    imod ih $$ H with #H
    imodintro
    simp only [List.map_cons]
    iapply txn.kvsIs_cons'
    iframe #

theorem txn.asembleRangeResponse.wp_proof : txn.asembleRangeResponse.spec (GF := GF) (hG := hG) := by
  intro rr r o rev count vs
  wp_start as ⟨Hrr, #Hr⟩
  iunfold txn.rangeRequestIs at Hr
  icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %rv, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho⟩
  iunfold txn.rangeResultIs at Hrr
  icases Hrr with ⟨%sl, %l, %Hl, Hrr, Hown⟩
  iunfold txn.kvsOwnAt at Hown
  icases Hown with ⟨Hsl, Hkvs⟩
  wp_auto
  have hlim : o.base.limit = limit := by subst Ho; rfl
  have hko : o.keysOnly = ko := by subst Ho; rfl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hlen
  have hvl : vs.length = l.length := by rw [← Hl]; simp
  ihave %HrespNN := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  wp_join iprop(∃ (sl' : GoSlice) (l' : List (Loc × EtcdKv)),
      rr ↦ ({ KVs' := sl', Rev' := rev, Count' := count } : go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult) ∗
      sl' ↦* l'.map Prod.fst ∗ txn.kvsAt l' ∗
      «$r0_ptr».[etcdserverpb.RangeResponse, go!"More"] ↦ txn.srvMore o vs ∗
      rr_ptr ↦ rr ∗ r_ptr ↦ r ∗ resp_ptr ↦ «$r0_ptr» ∗
      ⌜l'.map Prod.snd = txn.srvTrunc o vs⌝) with [Hrr Hsl Hkvs More rr r resp] as
      ⟨%sl', %l', Hrr, Hsl, Hkvs, More, rr, r, resp, %Hl'⟩
  · wp_if_destruct
    · ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z limit ∧ sint.Z limit ≤ sint.Z sl.cap := by
        refine ⟨by decide, by omega, by omega⟩
      simp only [hb, _root_.and_self, ite_true]
      icases (ownSlice_slice (W64 0) limit sl (DFrac.own 1) _ ⟨by decide, by omega, by omega⟩).1 $$ Hsl
        with ⟨-, Hsl, -⟩
      ihave Hkvs := txn.kvsAt_take' l (sint.nat limit) $$ Hkvs
      wp_auto
      have hm : txn.srvMore o vs = true := by
        unfold txn.srvMore; rw [hlim, hvl]
        have h0 : sint.Z (W64 0) = 0 := rfl
        have := Hlen.1; simp only [decide_eq_true_eq]; constructor <;> word
      have ht : txn.srvTrunc o vs = vs.take (sint.nat limit) := by
        unfold txn.srvTrunc; rw [hm, hlim]; rfl
      rw [hm, show sint.nat (W64 0) = 0 from rfl, subslice_from_start, ← List.map_take]
      simp only
      isplitl []
      · itrivial
      iexists slice.slice sl Loc (W64 0) limit, l.take (sint.nat limit)
      iframe
      ipureintro
      rw [ht, List.map_take, Hl]
    · have hm : txn.srvMore o vs = false := by
        unfold txn.srvMore; rw [hlim, hvl]
        have := Hlen.1; simp only [decide_eq_false_iff_not, not_and]
        intro _; word
      have ht : txn.srvTrunc o vs = vs := by unfold txn.srvTrunc; rw [hm]; rfl
      rw [hm]
      isplitl []
      · itrivial
      iexists sl, l
      iframe
      ipureintro; rw [ht, Hl]
  · have hm : txn.srvMore o vs = false := by
      unfold txn.srvMore; rw [hlim]; simp only [decide_eq_false_iff_not, not_and]
      intro h; exfalso; apply Hif; simpa using h
    have ht : txn.srvTrunc o vs = vs := by unfold txn.srvTrunc; rw [hm]; rfl
    rw [hm]
    iexists sl, l
    iframe
    ipureintro; rw [ht, Hl]
  ihave %Hlen' := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hlen'
  wp_apply wp_slice_make2 (V := Loc) sl'.len as %ks ⟨Hks, Hkscap⟩
  · ipureintro; exact Hlen'.2
  rename_i gi_ptr
  irename i => Hcnt
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  have hN : sint.nat sl'.len = l'.length := Hlen'.1.symm
  rw [hN]
  ihave HI : (∃ (n : Nat) (iv : w64),
      "Hcnt" ∷ i_ptr ↦ W64 (n : Int) ∗ "Hgi" ∷ gi_ptr ↦ iv ∗ "%Hn" ∷ ⌜n ≤ l'.length⌝ ∗
      "Hks" ∷ ks ↦* ((l'.take n).map Prod.fst ++
        List.replicate (l'.length - n) (zero_val Loc)) ∗
      "Hdone" ∷ txn.kvsAt ((l'.take n).map (fun x => (x.1, txn.respKv o x.2))) ∗
      "Hrest" ∷ txn.kvsAt (l'.drop n)) $$ [Hcnt Hgi Hks Hkvs]
  · iexists 0, zero_val w64
    simp only [named, List.take_zero, List.map_nil, List.nil_append, Nat.sub_zero, List.drop_zero]
    iframe Hcnt Hgi Hks Hkvs
    isplitl []
    · ipureintro; omega
    iapply txn.kvsAt_nil
  irename : (iprop("_" ∷ True) : IProp GF) => Hjunk
  iclear Hjunk
  wp_for HI
  have hNlt : l'.length < 2 ^ 63 := by rw [← hN]; unfold sint.nat; have := BitVec.toInt_lt (x := sl'.len); omega
  have hnZ : sint.Z (W64 (n : Int)) = n := by word
  by_cases Hif : sint.Z (W64 (n : Int)) < sint.Z sl'.len
  · rw [decide_eq_true Hif]
    simp only [↓reduceIte]
    (try wp_auto)
    have hlt : n < l'.length := by
      have h := Hif; rw [hnZ] at h; rw [← hN]; unfold sint.nat; unfold sint.Z at h; omega
    obtain ⟨x, hx⟩ : ∃ x, l'[n]? = some x := ⟨_, List.getElem?_eq_getElem hlt⟩
    have Hb : 0 ≤ sint.Z (W64 (n : Int)) ∧ sint.Z (W64 (n : Int)) < sint.Z sl'.len := by
      rw [hnZ]; constructor; · omega
      exact (hnZ ▸ Hif)
    have hnN : (sint.Z (W64 (n : Int))).toNat = n := by rw [hnZ]; rfl
    simp only [Hb, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl' (sint.Z (W64 (n : Int))) _ (DFrac.own 1) x.1 (by omega) $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [hnN, List.getElem?_map, hx]; rfl
    rw [List.drop_eq_getElem_cons hlt, show l'[n] = x from (List.getElem?_eq_some_iff.1 hx).2]
    icases (txn.kvsAt_cons _ _).1 $$ Hrest with ⟨Hx, Hrest⟩
    wp_join iprop(txn.kvAt x.1 (txn.respKv o x.2) ∗
        sl' ↦* List.map Prod.fst l' ∗ rr_ptr ↦ rr ∗
        rr ↦ ({ KVs' := sl', Rev' := rev, Count' := count } : go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult) ∗
        gi_ptr ↦ W64 (n : Int)) with [Hx Hsl rr Hrr Hgi] as ⟨Hx, Hsl, rr, Hrr, Hgi⟩
    · rw [show txn.respKv o x.2 = x.2 by simp [txn.respKv, hko]]
      iframe
    · simp only [Hb, _root_.and_self, ite_true]
      wp_apply wp_load_slice_index sl' (sint.Z (W64 (n : Int))) _ (DFrac.own 1) x.1 (by omega) $$ [Hsl] as Hsl
      · iframe; ipureintro; rw [hnN, List.getElem?_map, hx]; rfl
      simp only [txn.kvAt, mvcc.kvPtrIs, ↓reduceIte]
      icases Hx with ⟨%ksx, %stx, %ufx, %scx, #Hkx, %vsx, #Hvx, Hpx⟩
      wp_auto
      rw [show txn.respKv o x.2 = { x.2 with value := [] } by simp [txn.respKv, hko]]
      isplitl []
      · ipureintro; rfl
      ihave #Hnil := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      iframe Hsl rr Hrr Hgi
      iexists ksx, stx, ufx, scx
      iframe Hkx
      iexists slice.nil
      iframe Hnil
      iexact Hpx
    simp only [Hb, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl' (sint.Z (W64 (n : Int))) _ (DFrac.own 1) x.1 (by omega) $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [hnN, List.getElem?_map, hx]; rfl
    ihave %Hkslen := ownSlice_len _ _ _ $$ Hks
    have hkslen : ((l'.take n).map Prod.fst ++ List.replicate (l'.length - n) (zero_val Loc)).length =
        l'.length := by simp; omega
    rw [hkslen] at Hkslen
    have Hbk : 0 ≤ sint.Z (W64 (n : Int)) ∧ sint.Z (W64 (n : Int)) < sint.Z ks.len := by
      rw [hnZ]; constructor; · omega
      have := Hkslen.1; word
    simp only [Hbk, _root_.and_self, ite_true]
    wp_apply wp_store_slice_index (V := Loc) ks _ _ x.1 $$ [$Hks] as Hks
    · ipureintro; rw [hnZ, hkslen]; omega
    wp_for_post
    iframe
    iexists (n + 1), (W64 (n : Int))
    have hsucc : (W64 ((n + 1 : Nat) : Int)) = W64 (n : Int) + W64 1 := by word
    rw [hsucc, hnN, mvcc.set_filled (by simp; omega) hlt]
    iframe Hcnt Hgi
    isplitl []
    · ipureintro; omega
    have htk : l'.take (n + 1) = l'.take n ++ [x] := by
      rw [List.take_add_one, hx]; rfl
    rw [htk, List.map_append, List.map_append]
    simp only [List.map_cons, List.map_nil]
    iframe Hks
    isplitr [Hrest]
    · iapply (txn.kvsAt_append' _ _).2
      iframe Hdone
      iapply (txn.kvsAt_cons _ _).2
      iframe Hx
      iapply txn.kvsAt_nil
    iexact Hrest
  · rw [decide_eq_false Hif]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hnL : n = l'.length := by
      have h := Hif; rw [hnZ] at h
      have h2 : ((l'.length : Nat) : Int) = sint.Z sl'.len := by
        rw [← hN]; exact Int.toNat_of_nonneg Hlen'.2
      omega
    rw [hnL, Nat.sub_self, List.replicate_zero, List.append_nil, List.take_length, List.drop_length]
    ihave %Hv0nn := typedPointsto_not_null _ _ _ $$ «$v0»
    iStructNamedSuffix «$v0» "H"
    ipersist RevisionH
    ipersist Header
    ipersist Kvs
    ipersist More
    ipersist Count
    ipersist Hks
    iclear Hrest
    imod txn.kvsAt_persist' _ $$ Hdone with #Hdone
    wp_auto
    iapply HΦ
    have e1 : (l'.map (fun x => (x.1, txn.respKv o x.2))).map Prod.fst = l'.map Prod.fst := by
      simp [List.map_map, Function.comp_def]
    have e2 : (l'.map (fun x => (x.1, txn.respKv o x.2))).map Prod.snd =
        (txn.srvTrunc o vs).map (txn.respKv o) := by
      rw [← Hl']; simp [List.map_map, Function.comp_def]
    rw [e1, e2]
    isplitl []
    · unfold txn.rangeResponseIs
      isplitl []
      · ipureintro; exact HrespNN
      iexists «$v0_ptr», ks, l'.map Prod.fst
      iframe #
      ipureintro; exact Hv0nn
    unfold txn.respHdrOwn
    iexists «$v0_ptr»
    iframe Header
    isplitl []
    · ipureintro; exact Hv0nn
    iexists _, _, _, _
    iframe

end proof

end EtcdGrove
end Perennial
