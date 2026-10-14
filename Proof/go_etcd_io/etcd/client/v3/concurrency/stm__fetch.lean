/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stm__fetch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__fetch
public import Spec.go_etcd_io.etcd.client.v3.concurrency.readSet__add
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMReads

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stm.fetch.wp_proof (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hAdd : readSet.add.spec (GF := GF) (hG := hG)) :
    stm.fetch.spec (GF := GF) (hG := hG) := by
  intro b pfx reads gs ksl ks
  wp_start as ⟨#Henv, Hrs, Hopts, %Hgs, #Hks, %Hpk⟩
  ihave %Hlen := ownSlice_len $$ Hks
  wp_auto
  wp_if_destruct
  · have Hks0 : ks = [] := by
      obtain ⟨h1, h2⟩ := Hlen
      rw [Hif] at h1
      exact List.length_eq_zero_iff.1 (by rw [h1]; rfl)
    subst Hks0
    iapply HΦ
    iapply stmRet_ret
    iexists reads
    iframe Hrs Hopts
    isplitr
    · ipureintro; exact ⟨fun _ _ h => h, fun k h => Or.inl h⟩
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_slice_make2 (V := go_etcd_io.etcd.client.v3.Op) ksl.len as %opsl ⟨Hops, Hcap⟩
  · ipureintro; exact Hlen.2
  have Hksne : 0 < ks.length := by
    have h1 := Hlen.1
    have h2 : sint.Z ksl.len ≠ 0 := by intro h; apply Hif; word
    have h3 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 h3; omega
  unfold stmRsetOwn
  icases Hrs with ⟨%m, %rsMap, Hrf, Hrm, #Hrat⟩
  unfold stmOptsOwn
  icases Hopts with ⟨%gsl, Hgf, #Hgo⟩
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave IH : iprop(∃ (n : w64) (vs : List go_etcd_io.etcd.client.v3.Op) (kv : GoString) (iv : w64),
      "Hi" ∷ i_ptr ↦ n ∗ "Hkey" ∷ key_ptr ↦ kv ∗ "Higo" ∷ igo ↦ iv ∗
      "Hops" ∷ opsl ↦* (vs ++ List.replicate (ks.length - vs.length)
        (zero_val go_etcd_io.etcd.client.v3.Op)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ks.length ∧ vs.length = sint.nat n ∧
        ∀ k ∈ ks.take (sint.nat n), reads !! k = none⌝ ∗
      "#Hvs" ∷ □ ∀ (j : Nat) (v : go_etcd_io.etcd.client.v3.Op) (k : GoString),
        ⌜vs[j]? = some v⌝ -∗ ⌜ks[j]? = some k⌝ -∗ opFullAt v (opGetModel k gs)) $$ [i Higo key Hops]
  · iexists W64 0, [], _, _
    iframe i Higo key
    rw [Hlen.1]
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    iframe Hops
    isplitr
    · ipureintro
      have h0 : sint.Z (W64 0) = 0 := by decide
      refine ⟨by decide, ?_, rfl, ?_⟩
      · rw [h0]; omega
      · intro k hk; rw [show sint.nat (W64 0) = 0 from rfl] at hk; simp at hk
    imodintro
    iintro %j %v %k %Hv
    simp at Hv
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hn0, Hnl, Hvl, Hnone⟩ := Hn
    have Hlt : sint.nat n < ks.length := by
      have := Hlen; simp only [sint.nat, sint.Z] at this Hif Hn0 ⊢; omega
    obtain ⟨k, Hk⟩ : ∃ k, ks[sint.nat n]? = some k := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ksl.len := ⟨Hn0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ksl (sint.Z n) ks _ k Hn0 $$ [Hks] as -
    · iframe Hks; ipureintro; exact Hk
    wp_apply wp_map_lookup2 $$ Hrm as Hrm
    ihave #Hrat' := Hrat
    unfold readsAt
    icases Hrat' with ⟨%Hdom, #Hall⟩
    cases Hrk : rsMap !! k with
    | some rp =>
      obtain ⟨e, He⟩ : ∃ e, reads !! k = some e := by
        have h := Hdom k
        rw [Hrk] at h
        exact Option.isSome_iff_exists.1 (by simpa using h.symm)
      ihave #Hr := Hall $$ %k %rp %e %Hrk %He
      simp only [Option.isSome_some, decide_true, Option.getD_some]
      wp_auto
      wp_for_post
      iapply HΦ
      iapply stmRet_ret
      iexists reads
      isplitl [Hrf Hrm]
      · iexists m, rsMap
        iframe Hrf Hrm Hrat
      isplitl [Hgf]
      · iexists gsl
        iframe Hgf Hgo
      isplitr
      · ipureintro; exact ⟨fun _ _ h => h, fun k h => Or.inl h⟩
      iright
      iexists k, e, e
      iframe Hr
      ipureintro
      exact ⟨List.mem_of_getElem? Hk, He, rfl⟩
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
      wp_auto
      ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
      · iPkgInit
      wp_apply hGet k gsl gs $$ [$Hcv $Hgo] as %op #Hop
      · ipureintro; exact readOp_not_panics gs Hgs
      ihave %Hol := ownSlice_len $$ Hops
      have Hvks : vs.length < ks.length := by rw [Hvl]; exact Hlt
      have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z opsl.len := by
        refine ⟨Hn0, ?_⟩
        obtain ⟨h1, h2⟩ := Hol
        simp only [List.length_append, List.length_replicate] at h1
        have := Hlen; simp only [sint.nat, sint.Z] at this h1 h2 Hif Hn0 ⊢; omega
      simp only [Hbnd2, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index opsl (sint.Z n) _ op $$ [Hops] as Hops
      · iframe Hops; ipureintro
        simp only [List.length_append, List.length_replicate]
        have := Hlen; simp only [sint.nat, sint.Z] at this Hif Hn0 ⊢; omega
      have Hidx : (sint.Z n).toNat = vs.length := by rw [Hvl]
      rw [Hidx, set_append_replicate vs _ op ks.length Hvks]
      wp_for_post
      iframe
      iexists n + W64 1, vs ++ [op], k, n
      iframe Hi Hkey Higo Hops
      have Hn1 : sint.Z (n + W64 1) = sint.Z n + 1 := by
        have := Hlen; simp only [sint.nat, sint.Z] at this Hif Hn0 ⊢; word
      have Hnat1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
        have h1 := Hn1; have h2 := Hn0; unfold sint.nat; simp only [sint.Z] at h1 h2 ⊢; omega
      isplitr
      · ipureintro
        refine ⟨by omega, ?_, by rw [List.length_append, Hvl, Hnat1]; rfl, ?_⟩
        · rw [Hn1]; simp only [sint.nat] at Hlt; omega
        · intro k' hk'
          rw [Hnat1, List.take_add_one, Hk] at hk'
          rcases List.mem_append.1 hk' with h | h
          · exact Hnone k' h
          · simp only [Option.toList_some, List.mem_singleton] at h
            subst h
            have h := Hdom k'
            rw [Hrk] at h
            cases hr : reads !! k' with
            | none => rfl
            | some _ => rw [hr] at h; simp at h
      imodintro
      iintro %j %v %k' %Hv %Hk'
      by_cases hj : j < vs.length
      · rw [List.getElem?_append_left hj] at Hv
        iapply Hvs $$ %j %v %k' %Hv %Hk'
      · rw [List.getElem?_append_right (by omega)] at Hv
        have hj' : j = vs.length := by
          rcases h : j - vs.length with _ | i
          · omega
          · rw [h] at Hv; simp at Hv
        subst hj'
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at Hv
        subst Hv
        rw [Hvl, Hk] at Hk'
        cases Hk'
        iexact Hop
  · obtain ⟨Hn0, Hnl, Hvl, Hnone⟩ := Hn
    have Hvk : vs.length = ks.length := by
      rw [Hvl]; have := Hlen; simp only [sint.nat, sint.Z] at this Hif Hnl Hn0 ⊢; omega
    rw [Hvk, Nat.sub_self, List.replicate_zero, List.append_nil]
    have Hnone' : ∀ k ∈ ks, reads !! k = none := by
      intro k hk; apply Hnone; rw [← Hvl, Hvk, List.take_length]; exact hk
    ipersist Hops
    ihave #Hos : opsAt (GF := GF) opsl (ks.map (fun k => opGetModel k gs)) $$ []
    · unfold opsAt
      iexists vs
      iframe Hops
      isplitr
      · ipureintro; simp [Hvk]
      imodintro
      iintro %j %v %o %Hv %Ho
      rw [List.getElem?_map] at Ho
      cases Hkj : ks[j]? with
      | none => rw [Hkj] at Ho; cases Ho
      | some k =>
        rw [Hkj] at Ho; cases Ho
        iapply Hvs $$ %j %v %k %Hv %Hkj
    unfold stmEnv
    icases Henv with ⟨%c, %ctx, %cs, #Hc, #Hcl, #Hctx, #Hcs⟩
    unfold isEtcdSTMClient
    icases Hcl with ⟨%kv, %cctx, %ccs, #HKV, -, #HRT, -, -⟩
    wp_auto
    iunfold isEtcdReadTxnKV at HRT
    wp_apply HRT $$ %ctx %cs [$Hcs] as %t ⟨%B, HB, #HBs⟩
    iunfold readTxnBuilderSpec at HBs
    icases HBs with ⟨#HThen, #HCommit⟩
    wp_apply_raw HThen $$ %opsl %(ks.map (fun k => opGetModel k gs)) [$HB $Hos]
    · ipureintro
      intro o ho
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ho
      exact readOp_ok pfx k gs Hgs (Hpk k hk)
    inext
    iintro HB
    wp_auto
    ihave #H0 : etcdReached (GF := GF) (W64 0) $$ []
    · iapply etcdReached_zero
    wp_apply HCommit $$ %(ks.map (fun k => opGetModel k gs)) %(W64 0) [$HB $H0] as %resp %err #Hres
    iunfold readTxnResult at Hres
    icases Hres with (%Hne | ⟨%Heq, %r, %hdr, %rsl, %ps, #HH, %Hhdr, #HRev, #HSucc, #HR, #Hps, #Hr, %Hrr, #Hops⟩)
    · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      wp_apply wp_panic
      iapply HΦ
      iapply stmRet_abort _ (by simp)
    subst Heq
    obtain ⟨Hpsl, -, -, -⟩ := Hrr
    simp only [List.length_map] at Hpsl
    -- the reads of the responses
    ihave #Hch : iprop(□ ∀ (i : Nat) (a : Loc × GoString), ⌜(ps.zip ks)[i]? = some a⌝ -∗
        ∃ e : ReadM, respOpReadAt pfx a.2 a.1 e ∗ ⌜e.rev = readRevAt r (opGetModel a.2 gs)⌝) $$ []
    · imodintro
      iintro %i %a %Ha
      obtain ⟨Hp, Hk⟩ := List.getElem?_zip_eq_some.1 Ha
      have Ho : (ks.map (fun k => opGetModel k gs))[i]? = some (opGetModel a.2 gs) := by
        rw [List.getElem?_map, Hk]; rfl
      ihave ⟨%s, %n, #Hs, %Hsw, #Hp⟩ := Hops $$ %i %a.1 %(opGetModel a.2 gs) %Hp %Ho
      ihave ⟨%e, %Her, #He⟩ := respOpRead_of pfx a.2 gs Hgs (Hpk a.2 (List.mem_of_getElem? Hk)) _ s n a.1 Hsw.1 $$ [Hs Hp]
      · isplitl
        · iexact Hs
        · iexact Hp
      iexists e
      iframe He
      ipureintro; exact Her
    ihave ⟨%es, %Hesl, #Hes⟩ := iChoice _ (ps.zip ks) $$ Hch
    rw [List.length_zip, Hpsl, Nat.min_self] at Hesl
    wp_auto
    rw [MethodUnfold.method_unfold (t := go.GoType.PointerType readSet.ty) (m := go!"add")]
    wp_auto
    wp_apply hAdd m pfx rsMap reads ksl ks resp rsl ps es $$ [$Hpkg $Hrm $Hrat $Hks $HR $Hps] as ⟨%rsMap', Hrm, #Hrat'⟩
    · isplitr
      · ipureintro; exact ⟨by omega, by omega⟩
      imodintro
      iintro %i %p %k %e %Hi
      obtain ⟨Hp, Hk, He⟩ := Hi
      ihave ⟨#H, -⟩ := Hes $$ %i %(p, k) %e %(List.getElem?_zip_eq_some.2 ⟨Hp, Hk⟩) %He
      iexact H
    obtain ⟨k0, Hk0⟩ : ∃ k, ks[0]? = some k := ⟨_, List.getElem?_eq_getElem Hksne⟩
    obtain ⟨p0, Hp0⟩ : ∃ p, ps[0]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e0, He0⟩ : ∃ e, es[0]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave ⟨#Hr0, %Hrev0⟩ := Hes $$ %0 %(p0, k0) %e0 %(List.getElem?_zip_eq_some.2 ⟨Hp0, Hk0⟩) %He0
    ihave %Hrsl := ownSlice_len $$ Hps
    have h0 : sint.Z (W64 0) = 0 := by decide
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
      rw [h0]; obtain ⟨h1, h2⟩ := Hrsl; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) ps _ p0 (by decide) $$ [Hps] as -
    · iframe Hps; ipureintro; exact Hp0
    have Hmem0 : (k0, e0) ∈ ks.zip es :=
      List.mem_iff_getElem?.2 ⟨0, List.getElem?_zip_eq_some.2 ⟨Hk0, He0⟩⟩
    obtain ⟨e', He', Hmem'⟩ := readsAdd_mem reads (ks.zip es) k0 e0 Hmem0
    obtain ⟨j, Hj⟩ := List.mem_iff_getElem?.1 Hmem'
    obtain ⟨Hkj, Hej⟩ := List.getElem?_zip_eq_some.1 Hj
    obtain ⟨pj, Hpj⟩ : ∃ p, ps[j]? = some p := by
      have : j < ks.length := (List.getElem?_eq_some_iff.1 Hkj).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave ⟨#Hrj, %Hrevj⟩ := Hes $$ %j %(pj, k0) %e' %(List.getElem?_zip_eq_some.2 ⟨Hpj, Hkj⟩) %Hej
    ihave #Hf0 := respOpRead_fact $$ Hr0
    ihave #Hfj := respOpRead_fact $$ Hrj
    ihave %Hkv := readFact_agree pfx k0 e' e0 (by simp only at Hrevj Hrev0; rw [Hrevj, Hrev0]) $$ [Hfj Hf0]
    · isplitl
      · iexact Hfj
      · iexact Hf0
    ihave #Hr0' := Hr0
    unfold respOpReadAt
    icases Hr0' with ⟨%Hpn, %w, %rr, #Hu, #Hw, #Hrr⟩
    ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRR p0 w rr $$ [$Hpbi $Hu $Hw]
    · ipureintro; exact Hpn
    iapply HΦ
    iapply stmRet_ret
    iexists readsAdd reads (ks.zip es)
    isplitl [Hrf Hrm]
    · iexists m, rsMap'
      iframe Hrf Hrm Hrat'
    isplitl [Hgf]
    · iexists gsl
      iframe Hgf Hgo
    isplitr
    · ipureintro; exact readsAdd_grow reads ks es Hnone'
    iright
    iexists k0, e0, e'
    iframe Hrr
    ipureintro
    exact ⟨List.mem_of_getElem? Hk0, He', Hkv⟩

end proof

end concurrency
end EtcdGrove
end Perennial
