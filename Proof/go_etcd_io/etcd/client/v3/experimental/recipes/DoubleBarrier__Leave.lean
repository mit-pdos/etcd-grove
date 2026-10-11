/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__Leave.lean`. Lean-first
(no Rocq counterpart). `Leave` calls itself: Löb induction.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.DoubleBarrier__Leave
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Delete
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Key
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.WaitEvents
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem DoubleBarrier.Leave.wp_proof
    (wp_Client : concurrency.Session.Client.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_Key : RemoteKV.Key.spec (GF := GF) (hG := hG))
    (wp_Delete : RemoteKV.Delete.spec (GF := GF) (hG := hG))
    (wp_WaitEvents : WaitEvents.spec (GF := GF) (hG := hG)) :
    DoubleBarrier.Leave.spec (GF := GF) (hG := hG) := by
  intro b s γ client id key count ek st lo
  iloeb as IH generalizing %st %lo
  wp_start as ⟨#Hb, Hmk, #Hlo, %Hst⟩
  ihave #Hb' := Hb
  iunfold isDoubleBarrier at Hb'
  icases Hb' with ⟨#Hbs, #Hbctx, #Hbkey, #Hbcount, %Hcount, #Hsess, #Hcl, #Hclosed⟩
  ihave ⟨%kv, #HKVf, #Hkvc⟩ := isEtcdRecipesClient_kv client (key ++ go!"/") $$ Hcl
  ihave #Hcp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  have hwp : key ++ go!"/waiters" ≠ [] := by simp
  have hpw : key ++ go!"/" <+: key ++ go!"/waiters" := by
    rw [show go!"/waiters" = go!"/" ++ go!"waiters" from rfl, ← List.append_assoc]
    exact List.prefix_append _ _
  have hpr : key ++ go!"/" <+: key ++ go!"/ready" := by
    rw [show go!"/ready" = go!"/" ++ go!"ready" from rfl, ← List.append_assoc]
    exact List.prefix_append _ _
  have hne : key ++ go!"/waiters" ≠ key ++ go!"/" := by simp
  wp_auto
  wp_apply wp_Client s γ client id $$ [$Hcp $Hsess]
  (try wp_auto)
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  generalize hsl : slice.mk sl _ _ = optsSl
  ihave #Hopts : optsAt optsSl [withPrefixM] $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | i
    · cases Hf'; cases Hg; iexact Hf1
    · simp at Hf'
  ihave #Hopts' := optsAt_res optsSl _ iprop(True) $$ Hopts
  ihave #Hkvc' := Hkvc
  iunfold isRecipesKV at Hkvc'
  icases Hkvc' with ⟨#HKV, -, #HDel, -⟩
  iunfold isEtcdKVTodo at HKV
  ihave #HG := HKV $$ %(key ++ go!"/waiters") %optsSl %([withPrefixM] : List (OpFull → OpFull))
    %iprop(True) %lo
  wp_auto
  wp_apply HG $$ [] as %gresp %gerr ⟨-, #Hgres⟩
  · iframe Hopts' Hlo
    ipureintro
    exact ⟨waitersOp_not_panics.2, (waitersOp_t _).2⟩
  iclear HG HKV
  have Hop : opGetModel (key ++ go!"/waiters") [withPrefixM] = leaveOp (key ++ go!"/waiters") := rfl
  rw [Hop]
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    isplitl [Hmk]
    · iexists st.kv; iexact Hmk
    unfold leaveResult
    iright; ipureintro; exact Hgne
  subst Hgnil
  obtain ⟨-, -, -, Hrev0, Hser, HnP⟩ :=
    waitersOp_rev (key ++ go!"/") (key ++ go!"/waiters") hne hwp (by simp)
  have HRle' : sint.Z lo ≤ sint.Z R := HRle.1 Hser
  rw [ite_eq_right (c := (leaveOp (key ++ go!"/waiters")).isPrefixGet (key ++ go!"/") = true)
    (by rw [HnP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (leaveOp (key ++ go!"/waiters")).base.rev = W64 0 ∧
      KeyRangeUnder (key ++ go!"/") (leaveOp (key ++ go!"/waiters")).key
        (leaveOp (key ++ go!"/waiters")).base.rangeEnd from
    ⟨Hrev0, (waitersOp_under _ _ hwp hpw).2⟩)]
  icases Hgr with ⟨%s', %gsl', %gps, %gkvs, #Hs', %Hwf', #Hgsl', #Hgps, #Hgkvs, %Hgok⟩
  have Hkvs := leaveOp_kvs _ s' gkvs hwp Hgok
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, #Hgkv⟩
  ihave %Hgsl := ownSlice_len $$ Hgps
  wp_auto
  wp_if_destruct
  · -- no waiter left: the key is absent
    have Hnil : gkvs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hgl, Hgsl.1, Hif]; rfl
    iapply HΦ
    isplitl [Hmk]
    · iexists st.kv; iexact Hmk
    unfold leaveResult
    ileft
    isplitr
    · ipureintro; rfl
    ileft
    iexists R
    iframe HRR
    isplitr
    · unfold etcdAbsent
      iexists s'
      iframe Hs'
      ipureintro
      intro v hv hvk
      have : v ∈ gkvs := by
        rw [Hkvs, List.mem_filter]; exact ⟨hv, by rw [hvk]; simpa using Hst⟩
      rw [Hnil] at this; cases this
    ipureintro; exact HRle'
  have Hlen0 : 0 < gps.length := by
    rcases Nat.eq_zero_or_pos gps.length with h | h
    · exfalso; apply Hif; have := Hgsl.1; rw [h] at this; word
    · exact h
  obtain ⟨p0, Hp0⟩ : ∃ p, gps[0]? = some p := ⟨_, List.getElem?_eq_getElem Hlen0⟩
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gsl'.len := by
    have := Hgsl.1; constructor <;> word
  rw [ite_eq_left Hb0]
  icases ownSlice_elem_acc (sint.Z (W64 0)) p0 gsl' DFrac.discard gps (by word) (by exact Hp0)
    $$ Hgps with ⟨#Hp0e, -⟩
  wp_auto
  rw [ite_eq_left Hb0]
  wp_auto
  ihave IL : iprop(∃ (n : w64) (k0 pl ph : Loc) (il ih : Nat),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ k0 ∗ "lowest" ∷ lowest_ptr ↦ pl ∗
      "highest" ∷ highest_ptr ↦ ph ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (gps.length : Int)⌝ ∗
      "%Hl" ∷ ⌜gps[il]? = some pl⌝ ∗ "%Hh" ∷ ⌜gps[ih]? = some ph⌝) $$ [i k lowest highest]
  · iexists W64 0, _, p0, p0, 0, 0
    simp only [named]
    iframe
    ipureintro; exact ⟨by constructor <;> word, Hp0, Hp0⟩
  wp_for IL
  have Hgl' : ∀ (j : Nat) (p : Loc), gps[j]? = some p → ∃ v, gkvs[j]? = some v := by
    intro j p hj
    have : j < gkvs.length := by rw [← Hgl]; exact (List.getElem?_eq_some_iff.1 hj).1
    exact ⟨_, List.getElem?_eq_getElem this⟩
  obtain ⟨wl, Hwl⟩ := Hgl' il pl Hl
  obtain ⟨wh, Hwh⟩ := Hgl' ih ph Hh
  ihave #Hwlv := Hgkv $$ %il %pl %wl %Hl %Hwl
  ihave #Hwhv := Hgkv $$ %ih %ph %wh %Hh %Hwh
  ihave #Hwlv' := Hwlv
  ihave #Hwhv' := Hwhv
  iunfold kvValAt at Hwlv' Hwhv'
  icases Hwlv' with ⟨%lkeySl, %lvalSl, #Hlkey, #HlkeySl, -, #Hlmod, -⟩
  icases Hwhv' with ⟨%hkeySl, %hvalSl, #Hhkey, #HhkeySl, -, #Hhmod, -⟩
  wp_if_destruct
  · have Hlt : sint.nat n < gps.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, gps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨v, Hv⟩ := Hgl' _ p Hp
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gsl'.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) p gsl' DFrac.discard gps Hn.1 Hp $$ Hgps with ⟨#Hpe, -⟩
    ihave #Hvv := Hgkv $$ %(sint.nat n) %p %v %Hp %Hv
    iunfold kvValAt at Hvv
    icases Hvv with ⟨%vkeySl, %vvalSl, -, -, -, #Hvmod, -⟩
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, p, p, p, sint.nat n, sint.nat n
        simp only [named]
        iframe
        ipureintro; exact ⟨by constructor <;> word, Hp, Hp⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, p, p, ph, sint.nat n, ih
        simp only [named]
        iframe
        ipureintro; exact ⟨by constructor <;> word, Hp, Hh⟩
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, p, pl, p, il, sint.nat n
        simp only [named]
        iframe
        ipureintro; exact ⟨by constructor <;> word, Hl, Hp⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, p, pl, ph, il, ih
        simp only [named]
        iframe
        ipureintro; exact ⟨by constructor <;> word, Hl, Hh⟩
  -- after the loop: `lowest` and `highest` are waiters
  wp_apply wp_bytes_to_string lkeySl wl.key DFrac.discard $$ [$HlkeySl] as -
  try simp only [dbMyKey]
  icases Hmk with ⟨Hmk, Hek, #Hkv, %Hk⟩
  try unfold ownEphemeralKV
  (try wp_auto)
  wp_method_call
  wp_auto
  wp_apply wp_Key $$ [$Hek] as Hek
  have Hwls : wl ∈ s' := by
    have := List.mem_of_getElem? Hwl; rw [Hkvs, List.mem_filter] at this; exact this.1
  have Hwhs : wh ∈ s' := by
    have := List.mem_of_getElem? Hwh; rw [Hkvs, List.mem_filter] at this; exact this.1
  ihave %Hrevs := etcdState_revs R _ s' $$ Hs'
  wp_if_destruct
  · (try wp_auto)
    wp_if_destruct
    · -- the only waiter, and the caller: delete `key/ready`, then the key
      ihave #Hnilo : optsAt (GF := GF) slice.nil ([] : List (OpFull → OpFull)) $$ []
      · iapply concurrency.optsAt_nil
      iunfold isEtcdDeleteKVTodo at HDel
      obtain ⟨hdk, hde⟩ := concurrency.deleteOp_fields (key ++ go!"/ready")
      (try wp_auto)
      wp_apply HDel $$ %(key ++ go!"/ready") %slice.nil %([] : List (OpFull → OpFull)) %lo
        [$Hnilo $Hlo] as %dresp %derr #Hdres
      · ipureintro
        refine ⟨concurrency.deleteOp_not_panics _, ?_⟩
        rw [hdk, hde]; exact concurrency.keyRangeUnder_key _ _ hpr
      iunfold deleteResult at Hdres
      icases Hdres with (%Hdne | ⟨%Hdnil, -⟩)
      · obtain ⟨e, rfl⟩ : ∃ e, derr = GoInterface.ok e := by
          cases derr with
          | nil => exact absurd rfl Hdne
          | ok e => exact ⟨e, rfl⟩
        (try wp_auto)
        iapply HΦ
        isplitl [Hmk Hek]
        · iexists st.kv
          try simp only [dbMyKey]
          try unfold ownEphemeralKV
          iframe Hmk Hek Hkv
          ipureintro; exact Hk
        unfold leaveResult
        iright; ipureintro; exact Hdne
      subst Hdnil
      iclear HDel
      (try wp_auto)
      wp_method_call
      wp_auto
      wp_apply wp_Delete _ st (key ++ go!"/") lo $$ [$Hek $Hkv $Hlo] as %err2 ⟨Hek, Hres⟩
      · ipureintro; exact Hk
      ihave #Hres := leaveResult_of_delete _ st lo err2 $$ Hres
      iapply HΦ
      iframe Hres
      iexists GoInterface.nil
      try simp only [dbMyKey]
      try unfold ownEphemeralKV
      iframe Hmk Hek
      isplitr
      · unfold isRecipesKV; itrivial
      ipureintro; exact Hk
    · -- not the lowest: delete the key, wait for the lowest's deletion, retry
      (try wp_auto)
      wp_method_call
      wp_auto
      wp_apply wp_Delete _ st (key ++ go!"/") lo $$ [$Hek $Hkv $Hlo] as %derr ⟨Hek, Hres⟩
      · ipureintro; exact Hk
      ihave #Hres := leaveResult_of_delete _ st lo derr $$ Hres
      iunfold leaveResult at Hres
      icases Hres with (⟨%Hdnil, #Hown⟩ | %Hdne)
      rotate_left
      · obtain ⟨e, rfl⟩ : ∃ e, derr = GoInterface.ok e := by
          cases derr with
          | nil => exact absurd rfl Hdne
          | ok e => exact ⟨e, rfl⟩
        (try wp_auto)
        iapply HΦ
        isplitl [Hmk Hek]
        · iexists GoInterface.nil
          try simp only [dbMyKey]
          try unfold ownEphemeralKV
          iframe Hmk Hek
          isplitr
          · unfold isRecipesKV; itrivial
          ipureintro; exact Hk
        unfold leaveResult
        iright; ipureintro; exact Hdne
      subst Hdnil
      (try wp_auto)
      wp_apply wp_bytes_to_string lkeySl wl.key DFrac.discard $$ [$HlkeySl] as -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %esl ⟨Hesl, -⟩
      ipersist Hesl
      wp_apply wp_WaitEvents client (key ++ go!"/") wl.key wl.modRev _ [W32 1] (W32 1)
        $$ [$Hclosed $Hcl $Hesl] as %ev %werr ⟨%Hwnil, -⟩
      · ipureintro; exact ⟨rfl, Hwf'.2 wl Hwls, by have := (Hrevs wl Hwls).2.1; have := (Hrevs wl Hwls).1; omega⟩
      subst Hwnil
      (try wp_auto)
      wp_method_call
      wp_apply IH $$ %{ st with kv := GoInterface.nil } %lo [Hmk Hek] as %lerr ⟨Hmk', #Hl⟩
      · iframe Hb Hlo
        try unfold ownEphemeralKV
        iframe Hmk Hek
        isplitr
        · unfold isRecipesKV; itrivial
        ipureintro; (try simp only); first | exact ⟨Hk, Hst⟩ | exact Hst | exact Hk
      iapply HΦ
      iframe Hmk'
      try unfold leaveResult
      (try iunfold leaveResult at Hl)
      icases Hl with (⟨%Hlnil, -⟩ | %Hlne)
      · ileft
        isplitr
        · ipureintro; exact Hlnil
        iexact Hown
      iright; ipureintro; exact Hlne
  · (try wp_auto)
    wp_if_destruct
    · -- the lowest of several: wait for the highest's deletion, retry
      (try wp_auto)
      wp_apply wp_bytes_to_string hkeySl wh.key DFrac.discard $$ [$HhkeySl] as -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %esl ⟨Hesl, -⟩
      ipersist Hesl
      wp_apply wp_WaitEvents client (key ++ go!"/") wh.key wh.modRev _ [W32 1] (W32 1)
        $$ [$Hclosed $Hcl $Hesl] as %ev %werr ⟨%Hwnil, -⟩
      · ipureintro; exact ⟨rfl, Hwf'.2 wh Hwhs, by have := (Hrevs wh Hwhs).2.1; have := (Hrevs wh Hwhs).1; omega⟩
      subst Hwnil
      (try wp_auto)
      wp_method_call
      wp_apply IH $$ %st %lo [Hmk Hek] as %lerr ⟨Hmk', #Hl⟩
      · iframe Hb Hlo
        try simp only [dbMyKey]
        try unfold ownEphemeralKV
        iframe Hmk Hek Hkv
        ipureintro; (try simp only); first | exact ⟨Hk, Hst⟩ | exact Hst | exact Hk
      iapply HΦ
      iframe Hmk' Hl
    · -- not the lowest: delete the key, wait for the lowest's deletion, retry
      (try wp_auto)
      wp_method_call
      wp_auto
      wp_apply wp_Delete _ st (key ++ go!"/") lo $$ [$Hek $Hkv $Hlo] as %derr ⟨Hek, Hres⟩
      · ipureintro; exact Hk
      ihave #Hres := leaveResult_of_delete _ st lo derr $$ Hres
      iunfold leaveResult at Hres
      icases Hres with (⟨%Hdnil, #Hown⟩ | %Hdne)
      rotate_left
      · obtain ⟨e, rfl⟩ : ∃ e, derr = GoInterface.ok e := by
          cases derr with
          | nil => exact absurd rfl Hdne
          | ok e => exact ⟨e, rfl⟩
        (try wp_auto)
        iapply HΦ
        isplitl [Hmk Hek]
        · iexists GoInterface.nil
          try simp only [dbMyKey]
          try unfold ownEphemeralKV
          iframe Hmk Hek
          isplitr
          · unfold isRecipesKV; itrivial
          ipureintro; exact Hk
        unfold leaveResult
        iright; ipureintro; exact Hdne
      subst Hdnil
      (try wp_auto)
      wp_apply wp_bytes_to_string lkeySl wl.key DFrac.discard $$ [$HlkeySl] as -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %esl ⟨Hesl, -⟩
      ipersist Hesl
      wp_apply wp_WaitEvents client (key ++ go!"/") wl.key wl.modRev _ [W32 1] (W32 1)
        $$ [$Hclosed $Hcl $Hesl] as %ev %werr ⟨%Hwnil, -⟩
      · ipureintro; exact ⟨rfl, Hwf'.2 wl Hwls, by have := (Hrevs wl Hwls).2.1; have := (Hrevs wl Hwls).1; omega⟩
      subst Hwnil
      (try wp_auto)
      wp_method_call
      wp_apply IH $$ %{ st with kv := GoInterface.nil } %lo [Hmk Hek] as %lerr ⟨Hmk', #Hl⟩
      · iframe Hb Hlo
        try unfold ownEphemeralKV
        iframe Hmk Hek
        isplitr
        · unfold isRecipesKV; itrivial
        ipureintro; (try simp only); first | exact ⟨Hk, Hst⟩ | exact Hst | exact Hk
      iapply HΦ
      iframe Hmk'
      try unfold leaveResult
      (try iunfold leaveResult at Hl)
      icases Hl with (⟨%Hlnil, -⟩ | %Hlne)
      · ileft
        isplitr
        · ipureintro; exact Hlnil
        iexact Hown
      iright; ipureintro; exact Hlne

end proof

end recipes
end EtcdGrove
end Perennial
