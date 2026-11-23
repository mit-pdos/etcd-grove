/-
The proofs of the swiftpaxos kit's model, codec and generator (kit.go; notes/dsv-swiftpaxos.md, "The
kit over remote"; as dsv-paxos's `ModelProof.lean`/`KitProof.lean` and dsv-rabia's `ModelProof.lean`):

* `Model.wp_proof : Model.spec` (porcupine's `isModel swS`, what remote's `Check` consumes):
  `Model()`'s `Init` and `Step` closures meet `initSpec`/`stepSpec` against `swS` (the pending-writes
  model `pSeq swB`, remote's `PendDec`), from the state's helpers `has`, `push`, `erase`, `setCur`,
  `setPend`, `step`, `initState` over read-only slices and the pure `stepG_sim` (`ModelSet.lean`);
  its `Equal` is always `false` (kit.go, since `dff42254a2`), so `equalSpec` holds vacuously. A
  model value only simulates its set, and two histories reach equal values with different sets
  (`ModelSet.equal_unsound`), so no `Equal` comparing values could meet `equalSpec` (as dsv-epaxos's
  model, `notes/dsv-epaxos.md`, "Equal is always false"); `false` only costs porcupine's caching.
* `Codec.wp_proof : Codec.spec`: `Codec()`'s seven functions meet remote's `codecOk (swR sys E)`.
* `Gen.wp_proof` (premise: primitive's `RandomUint64` spec): `Gen`'s inputs are `KIn`s.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ModelLemmas
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof

attribute [local instance] Dsv.netShaExts Dsv.netShaExtsSemantics Dsv.netShaExtsInterp
  Dsv.netShaExts_has

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [SwiftNetPkgState GF]
variable [package_sem' : github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

set_option goose.wp.extras true

theorem wp_push (p : GoSlice) (P : List GoString) (v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.push)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [v]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ v $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq

theorem wp_has (p : GoSlice) (P : List GoString) (v : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.has)) (Val #p)) (Val #v))
    {{ RET #(decide (v ∈ P)); True }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ v ∉ P.take (sint.nat i)⌝ : IProp GF)
      $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, ?_⟩
    rw [h0]; simp
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as x
    rw [ite_eq_left ⟨Hi.1, hlt⟩]
    wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi.1 $$ [Hp] as -
    · iframe Hp; ipureintro; exact Hx_lookup
    wp_if_destruct
    · wp_for_post
      have : v ∈ P := Hif ▸ List.mem_of_getElem? Hx_lookup
      rw [show decide (v ∈ P) = true from decide_eq_true this]
      iapply HΦ
      itrivial
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hs, List.take_add_one, Hx_lookup]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hi.2.2, fun h => Hif h.symm⟩
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hv : v ∉ P := by
      have := Hi.2.2
      rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
        List.take_length] at this
    rw [show decide (v ∈ P) = false from decide_eq_false hv]
    iapply HΦ
    itrivial

theorem erase_take_succ (P : List GoString) (v x : GoString) (n : Nat) (hx : P[n]? = some x)
    (f : Bool) (hf : f = false → v ∉ P.take n) (hf2 : f = true → v ∈ P.take n) :
    (if (!f && decide (x = v)) then P.take n else
      (if f then (P.take n).erase v else P.take n) ++ [x]) =
    (if (f || decide (x = v)) then (P.take (n + 1)).erase v else P.take (n + 1)) := by
  rw [List.take_add_one, hx, Option.toList_some]
  cases f
  · have hv := hf rfl
    by_cases h : x = v
    · subst h
      simp [List.erase_append_right _ hv]
    · have hv' : v ∉ P.take n ++ [x] := by simp [hv, Ne.symm h]
      simp [h]
  · have hv := hf2 rfl
    simp [List.erase_append_left _ hv]

theorem wp_erase (p : GoSlice) (P : List GoString) (v : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.erase)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* P.erase v }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) p.len (by word)) as %q0 ⟨Hq, Hcap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (i : w64) (f : Bool) (q : GoSlice), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ f ∗
      "q" ∷ q_ptr ↦ q ∗
      "Hq" ∷ q ↦* (if f then (P.take (sint.nat i)).erase v else P.take (sint.nat i)) ∗
      "Hcap" ∷ ownSliceCap GoString q (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ (f = false → v ∉ P.take (sint.nat i)) ∧
        (f = true → v ∈ P.take (sint.nat i))⌝ : IProp GF) $$ [i found q Hq Hcap]
  · iexists W64 0, false, q0
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    simp only [Bool.false_eq_true, ↓reduceIte, List.take_zero]
    iframe
    ipureintro
    refine ⟨by word, by word, fun _ => by simp, fun h => by cases h⟩
  wp_for HI
  obtain ⟨Hi0, Hil, hf1, hf2⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as x
    have e := erase_take_succ P v x (sint.nat i) Hx_lookup f hf1 hf2
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    cases f
    · wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
      · iframe Hp; ipureintro; exact Hx_lookup
      by_cases hxv : x = v
      · subst hxv
        simp only [Bool.not_false, decide_true, Bool.and_self, ↓reduceIte, Bool.or_true] at e
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, true, q
        rw [hs, ← e]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro
        refine ⟨by word, by word, ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
        rw [List.take_add_one, Hx_lookup]; simp
      · simp only [Bool.not_false, hxv, decide_false, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Bool.or_false] at e
        rw [decide_eq_false hxv]
        wp_auto
        rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
        wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
        · iframe Hp; ipureintro; exact Hx_lookup
        wp_apply wp_slice_literal (V := GoString) [x]
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_auto
        wp_apply wp_slice_append (V := GoString) $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
        wp_for_post
        iframe
        iexists i + W64 1, false, q'
        rw [hs, ← e]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro
        refine ⟨by word, by word, ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hf1 rfl, Ne.symm hxv⟩
    · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Bool.true_or] at e
      wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
      · iframe Hp; ipureintro; exact Hx_lookup
      wp_apply wp_slice_literal (V := GoString) [x]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := GoString) $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists i + W64 1, true, q'
      rw [hs, ← e]
      simp only [↓reduceIte]
      iframe
      ipureintro
      refine ⟨by word, by word, ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
      rw [List.take_add_one, Hx_lookup]
      simp [hf2 rfl]
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hn : sint.nat i = P.length := by
      rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_length]
    iapply HΦ
    cases f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hv : v ∉ P := by
        have := hf1 rfl
        rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
          List.take_length] at this
      rw [List.erase_of_not_mem hv]
      iexact Hq
    · simp only [↓reduceIte]
      iexact Hq

theorem wp_setCur (c : GoSlice) (C : List GoString) (k : w64) (v : GoString)
    (hk : uint.nat k < C.length) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ c ↦*□ C }}
      (App (App (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.setCur))
        (Val #c)) (Val #k)) (Val #v))
    {{ (d : GoSlice), RET #d; d ↦* C.set (uint.nat k) v }} := by
  wp_start as #Hc
  ihave %Hl := ownSlice_len _ _ _ $$ Hc
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %d ⟨Hd, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hd $Hc] as %n ⟨-, Hd, -⟩
  have hn : sint.nat c.len = C.length := Hl.1.symm
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  ihave %Hdl := ownSlice_len _ _ _ $$ Hd
  have hkz : (uint.nat k : Int) = uint.Z k := by word
  have hd : (uint.nat k : Int) < sint.Z d.len := by
    have h1 : ((sint.nat d.len : Nat) : Int) = sint.Z d.len := Int.toNat_of_nonneg Hdl.2
    omega
  have hks : sint.Z k = uint.Z k := by
    have : sint.Z d.len < 2 ^ 63 := by word
    have : uint.Z k < 2 ^ 63 := by
      have : (uint.nat k : Int) = uint.Z k := by word
      omega
    word
  have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z d.len := by
    have : (uint.nat k : Int) = uint.Z k := by word
    omega
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index d (sint.Z k) _ v $$ [Hd] as Hd
  · iframe Hd; ipureintro; omega
  rw [show (sint.Z k).toNat = uint.nat k by rw [hks]; rfl]
  wp_auto
  iapply HΦ
  iexact Hd

theorem wp_setPend (c : GoSlice) (C : List GoSlice) (k : w64) (v : GoSlice)
    (hk : uint.nat k < C.length) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ c ↦*□ C }}
      (App (App (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.setPend))
        (Val #c)) (Val #k)) (Val #v))
    {{ (d : GoSlice), RET #d; d ↦* C.set (uint.nat k) v }} := by
  wp_start as #Hc
  ihave %Hl := ownSlice_len _ _ _ $$ Hc
  wp_auto
  wp_apply wp_slice_make2 (V := GoSlice) $$ [] as %d ⟨Hd, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hd $Hc] as %n ⟨-, Hd, -⟩
  have hn : sint.nat c.len = C.length := Hl.1.symm
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  ihave %Hdl := ownSlice_len _ _ _ $$ Hd
  have hkz : (uint.nat k : Int) = uint.Z k := by word
  have hd : (uint.nat k : Int) < sint.Z d.len := by
    have h1 : ((sint.nat d.len : Nat) : Int) = sint.Z d.len := Int.toNat_of_nonneg Hdl.2
    omega
  have hks : sint.Z k = uint.Z k := by
    have : sint.Z d.len < 2 ^ 63 := by word
    have : uint.Z k < 2 ^ 63 := by
      have : (uint.nat k : Int) = uint.Z k := by word
      omega
    word
  have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z d.len := by
    have : (uint.nat k : Int) = uint.Z k := by word
    omega
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index d (sint.Z k) _ v $$ [Hd] as Hd
  · iframe Hd; ipureintro; omega
  rw [show (sint.Z k).toNat = uint.nat k by rw [hks]; rfl]
  wp_auto
  iapply HΦ
  iexact Hd


theorem pendOwn_set (psl : List GoSlice) (pend : List (List GoString)) (k : Nat) (q : GoSlice)
    (Q : List GoString) (hk : k < pend.length) :
    (□ ∀ (i : Nat) (sl : GoSlice), ⌜psl[i]? = some sl⌝ → sl ↦*□ pend.getD i []) ∗ q ↦*□ Q ⊢
      (□ ∀ (i : Nat) (sl : GoSlice), ⌜(psl.set k q)[i]? = some sl⌝ →
        sl ↦*□ (pend.set k Q).getD i [] : IProp GF) := by
  iintro ⟨#H, #Hq⟩ !> %i %sl %Hi
  by_cases h : k = i
  · subst h
    rw [List.getElem?_set_self'] at Hi
    have e : sl = q := by
      cases h' : psl[k]? <;> simp [h'] at Hi
      exact Hi.symm
    subst e
    rw [getD_set_eq _ _ _ _ hk]
    iexact Hq
  · rw [List.getElem?_set_ne h] at Hi
    rw [getD_set_ne _ _ _ h]
    iapply H
    ipureintro; exact Hi

theorem wp_stepGo (cs ps : GoSlice) (cur : List GoString) (pend : List (List GoString))
    (hc : cur.length = 2) (hp : pend.length = 2) (hpb : ∀ k, (pend.getD k []).length < 2 ^ 60)
    (i : KIn) (u : Bool) (w : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ stateOwn cs ps cur pend }}
      (App (App (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.step))
        (Val #(State.mk cs ps))) (Val #(inVal i))) (Val #(Out.mk u w)))
    {{ (ok : Bool) (s' : State), RET (PairV #ok #s');
        ⌜ok = (stepG cur pend i u w).1⌝ ∗
        stateOwn s'.Cur' s'.Pend' (stepG cur pend i u w).2.1 (stepG cur pend i u w).2.2 }} := by
  unfold stateOwn
  wp_start as ⟨#Hc, %psl, %Hpl, #Hp, #He⟩
  ihave %HC := ownSlice_len _ _ _ $$ Hc
  ihave %HP := ownSlice_len _ _ _ $$ Hp
  have hk := i.key_lt
  have hkn : uint.nat (W64 (i.key : Int)) = i.key := by word
  have hks : sint.Z (W64 (i.key : Int)) = i.key := by word
  have hpl : psl.length = 2 := Hpl.trans hp
  have hbk : 0 ≤ sint.Z (W64 (i.key : Int)) ∧ sint.Z (W64 (i.key : Int)) < sint.Z ps.len := by
    have : ((sint.nat ps.len : Nat) : Int) = sint.Z ps.len := Int.toNat_of_nonneg HP.2
    omega
  list_elem psl i.key as x
  ihave #Hx := He $$ %i.key %x %Hx_lookup
  have hbc : 0 ≤ sint.Z (W64 (i.key : Int)) ∧ sint.Z (W64 (i.key : Int)) < sint.Z cs.len := by
    have : ((sint.nat cs.len : Nat) : Int) = sint.Z cs.len := Int.toNat_of_nonneg HC.2
    omega
  cases u
  · wp_auto
    cases hput : i.put
    · wp_auto
      list_elem cur i.key as y
      rw [ite_eq_left hbc]
      wp_apply wp_load_slice_index cs _ cur _ y hbc.1 $$ [Hc] as -
      · iframe Hc; ipureintro; rw [hks]; exact Hy_lookup
      have hy : cur.getD i.key [] = y := by simp [List.getD, Hy_lookup]
      wp_if_destruct
      · iapply HΦ
        simp only [stepG, hput, Bool.false_eq_true, ↓reduceIte, hy, Hif]
        iframe Hc Hp
        isplitr
        · ipureintro; exact Hpl
        iexact He
      have hw : ¬ w = cur.getD i.key [] := by rw [hy]; exact Hif
      clear Hif
      rw [ite_eq_left hbk]
      wp_apply wp_load_slice_index ps _ psl _ x hbk.1 $$ [Hp] as -
      · iframe Hp; ipureintro; rw [hks]; exact Hx_lookup
      wp_apply wp_has x _ w $$ [$Hx]
      wp_if_destruct
      · wp_apply +noauto wp_setCur cs cur (W64 (i.key : Int)) w (by rw [hkn]; omega) $$ [$Hc]
          as %d Hd
        iapply fupd_wp
        imod ownSlice_persist _ _ _ $$ Hd with #Hd
        imodintro
        wp_auto
        rw [ite_eq_left hbk]
        wp_apply wp_load_slice_index ps _ psl _ x hbk.1 $$ [Hp] as -
        · iframe Hp; ipureintro; rw [hks]; exact Hx_lookup
        wp_apply +noauto wp_erase x _ w $$ [$Hx] as %q Hq
        iapply fupd_wp
        imod ownSlice_persist _ _ _ $$ Hq with #Hq
        imodintro
        wp_auto
        wp_apply +noauto wp_setPend ps psl (W64 (i.key : Int)) q (by rw [hkn]; omega) $$ [$Hp]
          as %d' Hd'
        iapply fupd_wp
        imod ownSlice_persist _ _ _ $$ Hd' with #Hd'
        imodintro
        wp_auto
        iapply HΦ
        have hm : w ∈ pend.getD i.key [] := Hif
        simp only [stepG, hput, Bool.false_eq_true, ↓reduceIte, hw, hm]
        rw [hkn]
        iframe Hd Hd'
        isplitr
        · ipureintro; simp [Hpl]
        iapply pendOwn_set psl pend i.key q _ (by omega)
        iframe He Hq
      · iapply HΦ
        have hm : w ∉ pend.getD i.key [] := Hif
        simp only [stepG, hput, Bool.false_eq_true, ↓reduceIte, hw, hm]
        iframe Hc Hp
        isplitr
        · ipureintro; exact Hpl
        iexact He
    · wp_auto
      wp_apply +noauto wp_setCur cs cur (W64 (i.key : Int)) i.val (by rw [hkn]; omega) $$ [$Hc]
        as %d Hd
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hd with #Hd
      imodintro
      wp_auto
      iapply HΦ
      simp only [stepG, hput, Bool.false_eq_true, ↓reduceIte]
      rw [hkn]
      iframe Hd Hp
      isplitr
      · ipureintro; exact Hpl
      iexact He
  · wp_auto
    cases hput : i.put
    · wp_auto
      iapply HΦ
      simp only [stepG, hput, Bool.false_eq_true, ↓reduceIte]
      iframe Hc Hp
      isplitr
      · ipureintro; exact Hpl
      iexact He
    · wp_auto
      rw [ite_eq_left hbk]
      wp_apply wp_load_slice_index ps _ psl _ x hbk.1 $$ [Hp] as -
      · iframe Hp; ipureintro; rw [hks]; exact Hx_lookup
      wp_apply +noauto wp_push x _ i.val (hpb _) $$ [$Hx] as %q Hq
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hq with #Hq
      imodintro
      wp_auto
      wp_apply +noauto wp_setPend ps psl (W64 (i.key : Int)) q (by rw [hkn]; omega) $$ [$Hp]
        as %d Hd
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hd with #Hd
      imodintro
      wp_auto
      iapply HΦ
      simp only [stepG, hput, ↓reduceIte]
      rw [hkn]
      iframe Hc Hd
      isplitr
      · ipureintro; simp [Hpl]
      iapply pendOwn_set psl pend i.key q _ (by omega)
      iframe He Hq


theorem wp_initState :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.initState)) (Val #()))
    {{ (s : State), RET #s; stateOwn s.Cur' s.Pend' [[], []] [[], []] }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %c ⟨Hc, -⟩
  · ipureintro; word
  wp_apply +noauto wp_slice_make2 (V := GoSlice) $$ [] as %p ⟨Hp, -⟩
  · ipureintro; word
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hc with #Hc
  imod ownSlice_persist _ _ _ $$ Hp with #Hp
  imodintro
  wp_auto
  iapply HΦ
  unfold stateOwn
  simp only
  have e1 : List.replicate 2 (zero_val GoString) = [[], []] := rfl
  rw [e1] at *
  iframe Hc
  iexists List.replicate 2 (zero_val GoSlice)
  iframe Hp
  isplitr
  · ipureintro; rfl
  iintro !> %i %sl %Hi
  have hsl : sl = zero_val GoSlice := by
    rcases i with _ | _ | i <;> simp_all
  have hg : ([[], []] : List (List GoString)).getD i [] = [] := by
    rcases i with _ | _ | i <;> rfl
  rw [hsl, hg]
  iapply ownSlice_nil

theorem Model.wp_proof : Model.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    wp_apply wp_initState as %s0 Hs0
    iapply HΦ'
    simp only [swS, swRep]
    iexists s0.Cur', s0.Pend', [[], []], [[], []]
    iframe Hs0
    ipureintro
    refine ⟨rfl, rfl, rfl, fun k => by rcases k with _ | _ | k <;> simp [List.getD], sim_init⟩
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [swS, swS0]
    icases Hpre with ⟨%Hk, Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, a, rfl⟩ := Hio
    unfold swRep
    icases Hrep with ⟨%cs, %ps, %cur, %pend, %Hr, #Hst⟩
    obtain ⟨rfl, hc, hp, hpb, hsim⟩ := Hr
    have hdec : ∃ (u : Bool) (w : BStr), (u = true → w.1 = []) ∧ a = ansOf u w ∧
        ansV a = outV u w.1 := by
      cases a with
      | ok w => exact ⟨false, w, nofun, rfl, rfl⟩
      | err => exact ⟨true, bnil, fun _ => rfl, rfl, rfl⟩
    obtain ⟨u, w, hu, rfl, hav⟩ := hdec
    have hM : (pM swB swDec).step s (inV x, ansV (ansOf u w)) =
        (pSeq swB).step s (x, ansOf u w) := pM_step swB swDec s _ x _ (swDec_box x _)
    rw [hav] at hM ⊢
    obtain ⟨H1, H2⟩ := stepG_sim hc hp hsim x u w hu
    obtain ⟨hl1, hl2, hl3⟩ := stepG_lens cur pend x u w.1
    wp_auto
    wp_apply wp_stepGo cs ps cur pend hc hp (fun k => by have := hpb k; omega) x u w.1 $$ [$Hst]
      as %ok %s' ⟨%Hok, #Hs'⟩
    iapply HΦ'
    isplitr
    · iexists cs, ps, cur, pend
      iframe Hst
      ipureintro; exact ⟨rfl, hc, hp, hpb, hsim⟩
    isplitr
    · ipureintro; rw [Hok, hM, H1]
    unfold stepPost
    simp only [hM]
    cases hs : (pSeq swB).step s (x, ansOf u w) with
    | none => itrivial
    | some S' =>
      simp only
      iexists s'.Cur', s'.Pend', (stepG cur pend x u w.1).2.1, (stepG cur pend x u w.1).2.2
      iframe Hs'
      ipureintro
      refine ⟨rfl, by rw [hl1, hc], by rw [hl2, hp], fun k' => ?_, H2 S' hs⟩
      have := hl3 k'
      have := hpb k'
      omega
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal: always false
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    icases Hpre with ⟨Ha, Hb⟩
    wp_auto
    iapply HΦ'
    iframe Ha Hb
    ipureintro; nofun
  ileft
  ipureintro; trivial

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro sys E
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk swR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    have hv : i.val.length < 2 ^ 48 := i.2.2
    have hk := i.key_lt
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
    wp_apply (wp_slice_make3 (V := w8) (W64 2) (W64 2 + W64 i.val.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have hbl : sint.Z b.len = 2 := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by rw [hbl]; word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by rw [hbl]; word
    have hkb : W8 (uint.Z (W64 (i.key : Int))) = W8 (i.key : Int) := by
      rw [show uint.Z (W64 (i.key : Int)) = (i.key : Int) by word]
    cases hput : i.put
    · wp_auto
      rw [ite_eq_left h1]
      wp_apply wp_store_slice_index b (sint.Z (W64 1)) _ _ $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encInB, hput, Bool.false_eq_true, ↓reduceIte]
      rw [← hkb, show W8 0 :: W8 (uint.Z (W64 (i.key : Int))) :: i.val =
        (List.replicate 2 (zero_val w8)).set 1 (W8 (uint.Z (W64 (i.key : Int)))) ++ i.val from rfl]
      iexact Hb'
    · wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      rw [ite_eq_left h1]
      wp_apply wp_store_slice_index b (sint.Z (W64 1)) _ _ $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encInB, hput, ↓reduceIte]
      rw [← hkb, show W8 1 :: W8 (uint.Z (W64 (i.key : Int))) :: i.val =
        ((List.replicate 2 (zero_val w8)).set 0 (W8 1)).set 1 (W8 (uint.Z (W64 (i.key : Int)))) ++
          i.val from rfl]
      iexact Hb'
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    have hk := i.key_lt
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hb2 : 2 ≤ sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [encInB, List.length_cons] at h1
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg h2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      constructor <;> word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by
      constructor <;> word
    wp_auto
    wp_if_destruct
    · exfalso; word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if i.put then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    have hkz : uint.Z (W8 (i.key : Int)) = i.key := by word
    wp_if_destruct
    · exfalso
      have hb0 : uint.Z (if i.put = true then W8 1 else W8 0) ≤ 1 := by
        cases i.put <;> decide
      have h11 : uint.Z (W8 1) = 1 := by decide
      rw [h11] at Hif
      exact Int.not_lt.2 hb0 Hif
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (W8 (i.key : Int)) (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; rw [hkz] at Hif; word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if i.put then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [ite_eq_left h1]
    wp_apply wp_load_slice_index b (sint.Z (W64 1)) _ dq (W8 (i.key : Int)) (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by word, by word, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 2) b dq _ ⟨by word, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 2) = 2 from rfl]
    simp only [encInB, List.drop_succ_cons, List.drop_zero]
    wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
    · iexact Hb2
    iapply HΦ'
    ipureintro
    intro _
    have e : decide ((if i.put = true then W8 1 else W8 0) = W8 1) = i.put := by
      cases i.put <;> decide
    rw [hkz, e]
    rfl
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨u, w, rfl⟩ : ∃ (u : Bool) (w : BStr), v = outV u w.1 := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, h⟩
      · exact ⟨_, bnil, h⟩
    iintro !> %Φ' - HΦ'
    rw [encOutV_outV]
    have hw := w.2
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
    wp_apply (wp_slice_make3 (V := w8) (W64 1) (W64 1 + W64 w.1.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    cases u
    · wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encOutB, Bool.false_eq_true, ↓reduceIte]
      rw [show List.replicate 1 (zero_val w8) ++ w.val = W8 0 :: w.val from rfl]
      iexact Hb'
    · wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encOutB, ↓reduceIte]
      rw [show (List.replicate 1 (zero_val w8)).set 0 (W8 1) ++ w.val = W8 1 :: w.val from rfl]
      iexact Hb'
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨u, w, rfl⟩ : ∃ (u : Bool) (w : BStr), v = outV u w.1 := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, h⟩
      · exact ⟨_, bnil, h⟩
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_outV]
    simp only [encOutB]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hw := w.2
    have hb1 : 1 ≤ sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_cons] at h1
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg h2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      constructor <;> word
    wp_auto
    wp_if_destruct
    · exfalso; word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hif <;> word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if u then W8 1 else W8 0) (by word)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by word, by word, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 1) b dq _ ⟨by word, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 1) = 1 from rfl, List.drop_one, List.tail_cons]
    wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
    · iexact Hb2
    iapply HΦ'
    ipureintro
    intro _
    cases u <;> rfl
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    rw [show (!swB.isWrite i) = !i.put from rfl]
    iapply HΦ'
    itrivial
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial


/-- `digits(n)`: a decimal string of at most `k` characters when `n < 10^k` (one digit character
for `n < 10`). As the lab's (`examples/swiftnet/OrchGen.lean`). -/
theorem wp_digits (n : w64) (k : Nat) (hk : uint.nat n < 10 ^ k) (hk1 : 1 ≤ k) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.imdea_software.swiftpaxos.examples.swiftnet.digits)) (Val #n))
    {{ (s : GoString), RET #s; ⌜s ≠ [] ∧ s.length ≤ k ∧
        (uint.nat n < 10 → s = [W8 (48 + uint.Z n)])⌝ }} := by
  induction h : uint.nat n using Nat.strongRecOn generalizing n k with
  | _ m IH =>
  wp_start as -
  wp_auto
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (W64 48 + n))]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z (W64 48 + n))))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %c_sl ⟨Hc_sl, -⟩
    wp_apply wp_bytes_to_string $$ Hc_sl as -
    iapply HΦ
    ipureintro
    have hn : uint.Z n < 10 := by word
    refine ⟨by simp, by simp; omega, fun _ => ?_⟩
    congr 1
    word
  · have hn10 : 10 ≤ uint.nat n := by word
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · simp at hk; omega
      · omega
    wp_apply IH (uint.nat (n / W64 10)) (by word) (n / W64 10) (k - 1) ?_ (by omega) rfl
      as %s1 %Hs1
    · rw [show uint.nat (n / W64 10) = uint.nat n / 10 by word]
      have h10 : 10 ^ k = 10 ^ (k - 1) * 10 := by
        rw [← Nat.pow_succ]; congr 1; omega
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← h10]; exact hk)
    wp_apply IH (uint.nat (n % W64 10)) (by word) (n % W64 10) 1 (by word) (Nat.le_refl _) rfl
      as %s2 %Hs2
    iapply HΦ
    ipureintro
    have hs2 : s2.length = 1 := by
      rw [Hs2.2.2 (by word)]; rfl
    refine ⟨by simp [Hs1.1], ?_, fun h' => by omega⟩
    simp only [List.length_append, hs2]
    have := Hs1.2.1
    omega

theorem Gen.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply wp_RandomUint64 as %n -
  have hk : uint.nat (n % W64 2) < 2 := by word
  have hkw : W64 ((uint.nat (n % W64 2) : Nat) : Int) = n % W64 2 := by word
  wp_if_destruct
  · wp_apply wp_digits _ 3 (by word) (by omega) as %d %Hd
    iapply HΦ
    imodintro
    ipureintro
    refine ⟨⟨(true, uint.nat (n % W64 2), [118#8] ++ d), hk, ?_⟩, ?_⟩
    · show ([118#8] ++ d).length < 2 ^ 48
      simp only [List.length_append, List.length_singleton]
      have := Hd.2.1
      omega
    · simp only [inV, inVal, KIn.put, KIn.key, KIn.val]
      rw [hkw]
  · iapply HΦ
    imodintro
    ipureintro
    refine ⟨⟨(false, uint.nat (n % W64 2), []), hk, by simp⟩, ?_⟩
    simp only [inV, inVal, KIn.put, KIn.key, KIn.val]
    rw [hkw]

end proof

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial
