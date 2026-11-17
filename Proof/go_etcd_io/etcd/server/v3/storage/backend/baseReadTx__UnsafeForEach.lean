/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/baseReadTx__UnsafeForEach.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.baseReadTx__UnsafeForEach
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__ForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeForEach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

/-! The walk's counting: the user's index after `j` of bbolt's entries is the number of them the
filter keeps. -/

private theorem cnt_step {es : List Ent} {p : Ent → Bool} {j : Nat} {e : Ent} (h : es[j]? = some e) :
    ((es.take (j + 1)).filter p).length = ((es.take j).filter p).length + (if p e then 1 else 0) := by
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split <;> simp

private theorem cnt_get {es : List Ent} {p : Ent → Bool} {j : Nat} {e : Ent} (h : es[j]? = some e)
    (hp : p e = true) (bf : List Ent) :
    (es.filter p ++ bf)[((es.take j).filter p).length]? = some e := by
  obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.1 h
  have hes : es = es.take j ++ (e :: es.drop (j + 1)) := by
    have := List.take_append_drop j es
    rw [List.drop_eq_getElem_cons hj, hje] at this
    exact this.symm
  have hf : es.filter p = (es.take j).filter p ++ (e :: (es.drop (j + 1)).filter p) := by
    conv => lhs; rw [hes]
    rw [List.filter_append, List.filter_cons_of_pos hp]
  rw [hf, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem cnt_lt {es : List Ent} {p : Ent → Bool} {j : Nat} {e : Ent} (h : es[j]? = some e)
    (hp : p e = true) (bf : List Ent) :
    ((es.take j).filter p).length < (es.filter p ++ bf).length := by
  have := cnt_get h hp bf
  exact (List.getElem?_eq_some_iff.1 this).1

private theorem cnt_all (es : List Ent) (p : Ent → Bool) :
    ((es.take es.length).filter p).length = (es.filter p).length := by
  rw [List.take_length]

private theorem buf_get {fs bf : List Ent} {i : Nat} {e : Ent} (h : bf[i]? = some e) :
    (fs ++ bf)[fs.length + i]? = some e := by
  rw [List.getElem?_append_right (by omega)]; simpa using h

private theorem keys_take_succ {bf : List Ent} {i : Nat} {e : Ent} (h : bf[i]? = some e)
    (M : GMap GoString Unit) (hM : ∀ k, (M !! k).isSome ↔ k ∈ (bf.take i).map Prod.fst) (k : GoString) :
    ((<[e.1 := ()]> M) !! k).isSome ↔ k ∈ (bf.take (i + 1)).map Prod.fst := by
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_singleton]
  by_cases hk : e.1 = k
  · subst hk; simp
  · rw [GMap.lookup_insert_ne _ _ hk, hM k]; simp [Ne.symm hk]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.baseReadTx.UnsafeForEach.wp_proof
    (hFE : backend.txReadBuffer.ForEach.spec (GF := GF) (hG := hG))
    (hfe : backend.unsafeForEach.spec (GF := GF) (hG := hG)) :
    backend.baseReadTx.UnsafeForEach.spec (GF := GF) (hG := hG) := by
  intro γ P base dq rtx rv q bk bi fn I E
  wp_start as ⟨Hrd, #Hbk, HI, #Hf⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold baseRd
  icases Hrd with ⟨%m, %Pb, %cm, %tm, Hrb, Hrtx, Hcm, #Htm, Hown, #Hg, Hlive, #Hsnap, #Hintv,
    %Hwf⟩
  generalize hbf : bkOf rv.2.bks bi.id = bf
  generalize hes : bktEnts (bktOf rv.1 bi.name) = es
  have hrt : rtForEach rv bi = es.filter (fun e => !decide (e.1 ∈ bf.map Prod.fst)) ++ bf := by
    rw [← hbf, ← hes]; unfold rtForEach; simp only [decide_not]
  rw [hrt] at *
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Unit) go.string (go.GoType.StructType []))
    as %dm Hdm
  -- the buffer's keys
  wp_apply (hFE (rbufOf base) dq m Pb rv.2 bk bi _
      (fun i => iprop(dups_ptr ↦ dm ∗ ∃ M : GMap GoString Unit, dm ↦$ M ∗
        ⌜∀ k, (M !! k).isSome ↔ k ∈ (bf.take i).map Prod.fst⌝))
      (fun _ => iprop(False))) $$ [$Hrb dups Hdm] as %err ⟨Hrb, Hres⟩
  · rw [hbf]
    iframe #
    isplitr
    · iunfold visitorSpec
      imodintro
      iintro %i %e %ks %vs %He
      wp_start as ⟨⟨dups, %M, HM, %HMk⟩, #Hks, #Hvs⟩
      wp_auto
      wp_apply wp_bytes_to_string $$ Hks as -
      wp_apply wp_mapInsert $$ HM as HM
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      dsimp only
      iframe
      ipureintro
      exact keys_take_succ He M HMk
    · iframe
      ipureintro
      intro k; simp
  icases Hres with (⟨%Hnil, dups, %M, HM, %HMk⟩ | ⟨-, %hF⟩)
  rotate_left
  · exact hF.elim
  subst Hnil
  rw [hbf, List.take_length] at HMk
  wp_auto
  -- bbolt's entries not in the buffer, under `txMu`
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hwl, HP⟩
  unfold tmTok
  icases HP with ⟨Hta, Htb⟩
  imod stats_take γ P rtx cm rv.1 ⊤ (by solve_ndisj) $$ [$Hintv $Htb] with Hst
  have hsplit := (txLive_fractional (GF := GF) rtx).fractional q.half q.half
  rw [Qp.half_add_half] at hsplit
  wp_apply (hfe rtx (.rd q rv.1) bk bi _
      (fun j => iprop(visitor_ptr ↦ fn ∗ dups_ptr ↦ dm ∗ dm ↦$ M ∗
        I (((es.take j).filter (fun e => !decide (e.1 ∈ bf.map Prod.fst))).length)))
      (fun _ err => iprop(∃ i : Nat,
        ⌜i < (es.filter (fun e => !decide (e.1 ∈ bf.map Prod.fst)) ++ bf).length⌝ ∗ E i err)))
    $$ [Hlive Hst visitor dups HM HI] as %err ⟨Hfo, Hres⟩
  · simp only [feOwn, FeSide.data, FeSide.q]
    rw [hes]
    iframe; iframe #
    imodintro
    iintro %j %e %k %v %He
    wp_start as ⟨⟨visitor, dups, HM, HI⟩, Hl, %Hk, #Hkb, #Hvb⟩
    wp_auto
    icases txBytes_acc rtx k e.1 q.half $$ [$Hkb $Hl] with ⟨%dk, Hkp, Hkback⟩
    wp_apply wp_bytes_to_string $$ Hkp as Hkp
    ispecialize Hkback $$ Hkp
    wp_apply wp_map_lookup2 $$ HM as HM
    try wp_auto
    by_cases hd : e.1 ∈ bf.map Prod.fst
    · have hp : (!decide (e.1 ∈ bf.map Prod.fst)) = false := by simp [hd]
      have hs : (M !! e.1).isSome = true := (HMk e.1).2 hd
      simp only [hs, decide_true]
      wp_auto
      iapply HΦ
      iframe
      ileft
      isplitr
      · ipureintro; rfl
      rw [cnt_step He, hp]
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      iframe
    · have hp : (!decide (e.1 ∈ bf.map Prod.fst)) = true := by simp [hd]
      have hs : (M !! e.1).isSome = false := by
        cases h : (M !! e.1).isSome
        · rfl
        · exact absurd ((HMk e.1).1 h) hd
      simp only [hs, Bool.false_eq_true, decide_false]
      wp_auto
      wp_apply Hf $$ %(((es.take j).filter (fun e => !decide (e.1 ∈ bf.map Prod.fst))).length) %e %k %v
        %(cnt_get He hp bf) [HI Hkback] as %err' ⟨Hl, Hr⟩
      · iframe Hkback
        isplitl [HI]
        · iexact HI
        unfold rdB; isplitl <;> iright <;> iframe #
      iapply HΦ
      iframe
      icases Hr with (⟨%Hn, HI⟩ | ⟨%Hn, HE⟩)
      · ileft
        isplitr
        · ipureintro; exact Hn
        rw [cnt_step He, hp]
        iframe
      · iright
        isplitr
        · ipureintro; exact Hn
        iexists _
        iframe
        ipureintro
        exact cnt_lt He hp bf
  simp only [feOwn, FeSide.data]
  rw [hes] at *
  icases Hfo with ⟨Hlive, -, Hst⟩
  imod stats_give γ P rtx cm rv.1 ⊤ (by solve_ndisj) $$ [$Hintv $Hst] with Htb
  try wp_auto
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hta Htb]
  · iframe
  icases Hres with (⟨%Hnil, visitor, dups, HM, HI⟩ | ⟨%i, ⟨%Hn, -⟩, %i', %Hi', HE⟩)
  rotate_left
  · obtain ⟨eo, rfl⟩ : ∃ eo, err = GoInterface.ok eo := by
      cases err with
      | nil => exact absurd rfl Hn
      | ok eo => exact ⟨eo, rfl⟩
    wp_auto
    iapply HΦ
    isplitl [Hrb Hrtx Hcm Hown Hlive]
    · iexists m, Pb, cm, tm; iframe; iframe #; ipureintro; exact Hwf
    iright
    iexists i'
    iframe
    ipureintro
    exact ⟨Hn, Hi'⟩
  subst Hnil
  rw [cnt_all]
  try wp_auto
  -- the buffer's entries
  icases hsplit.1 $$ Hlive with ⟨Hl1, Hl2⟩
  wp_apply (hFE (rbufOf base) dq m Pb rv.2 bk bi fn
      (fun i => iprop(I ((es.filter (fun e => !decide (e.1 ∈ bf.map Prod.fst))).length + i) ∗
        txLive rtx q.half))
      (fun err => iprop(txLive rtx q.half ∗ ∃ i : Nat,
        ⌜i < (es.filter (fun e => !decide (e.1 ∈ bf.map Prod.fst)) ++ bf).length⌝ ∗ E i err)))
    $$ [$Hrb HI Hl1] as %err ⟨Hrb, Hres⟩
  · rw [hbf]
    iframe #
    isplitr
    · iunfold visitorSpec
      imodintro
      iintro %i %e %ks %vs %He
      wp_start as ⟨⟨HI, Hl⟩, #Hks, #Hvs⟩
      wp_apply Hf $$ %((es.filter (fun e => !decide (e.1 ∈ bf.map Prod.fst))).length + i) %e %ks %vs
        %(buf_get He) [$HI $Hl] as %err' ⟨Hl, Hr⟩
      · unfold rdB; isplitl <;> ileft <;> iframe #
      iapply HΦ
      dsimp only
      icases Hr with (⟨%Hn, HI⟩ | ⟨%Hn, HE⟩)
      · ileft
        isplitr
        · ipureintro; exact Hn
        rw [Nat.add_assoc]
        iframe
      · iright
        isplitr
        · ipureintro; exact Hn
        iframe
        ipureintro
        exact (List.getElem?_eq_some_iff.1 (buf_get He)).1
    · simp only [Nat.add_zero]; iframe
  rw [hbf]
  icases Hres with (⟨%Hnil, HI, Hl1⟩ | ⟨%Hn, Hl1, %i, %Hi, HE⟩)
  · iapply HΦ
    isplitl [Hrb Hrtx Hcm Hown Hl1 Hl2]
    · iexists m, Pb, cm, tm
      iframe; iframe #
      isplitl [Hl1 Hl2]
      · iapply hsplit.2; iframe
      ipureintro; exact Hwf
    ileft
    isplitr
    · ipureintro; exact Hnil
    rw [List.length_append]
    iframe
  · iapply HΦ
    isplitl [Hrb Hrtx Hcm Hown Hl1 Hl2]
    · iexists m, Pb, cm, tm
      iframe; iframe #
      isplitl [Hl1 Hl2]
      · iapply hsplit.2; iframe
      ipureintro; exact Hwf
    iright
    iexists i
    iframe
    ipureintro
    exact ⟨Hn, Hi⟩

end proof

end EtcdGrove
end Perennial
