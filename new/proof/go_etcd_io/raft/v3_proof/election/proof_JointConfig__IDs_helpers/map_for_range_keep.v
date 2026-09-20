(** Two repairs to [new/golang/theory/map.v] that [JointConfig.IDs] needs,
    kept here so that this proof does not touch the framework file -- an
    edit to [theory/map.v] invalidates the [.vos] of ~90 files, the whole
    Goose-generated raft closure among them, under every agent sharing the
    checkout.  Both belong in [map.v]; move them there at a quiet moment and
    delete this file.  See the report / notes entry of 2026-09-19.

    This is **proof structure, not specification**: no [Module Type], no
    [Parameter], no triple about a Go function.  Nothing but
    [proof_JointConfig__IDs.v] may [Require] it (the [*_helpers] rule of
    [etc/check-module-discipline.py]).

    1. [wp_map_for_range] ([map.v:251]) *consumes* [mref ↦${dq} m] and never
       hands it back: its proof ends in [iApply "HΦ". iFrame.], which drops
       the [heap_pointsto] it got back from [FinishRead].  A caller that has
       to re-establish an invariant containing the map -- [own_tracker]'s
       [voters_ref ↦$ voters] here, [Progress'] in [TallyVotes] -- cannot.
       [wp_map_for_range_keep] is the same lemma with the map returned: in
       the final continuation, and, on [break]/[return], through the
       postcondition ([λ v, mref ↦${dq} m -∗ Φ v]).  The proof is [map.v]'s
       with the last line of each exit fixed.

    2. [wp_map_nil_for_range] ([map.v:343]) is stated in the section that
       carries [K], [V] and their [ZeroVal]/[Countable]/[IntoValInj]
       instances under [Local Set Default Proof Using "All"], so the
       closed constant takes [{K} {V}] and five instance arguments that its
       *statement* does not mention.  [tc_solve] cannot find such an
       instance (the evars for [K] and [V] are unconstrained), so [wp_pure]
       -- hence [wp_auto] -- never fires it: measured, [wp_pure] reports
       "Failed to progress" on
       [map.for_range go.uint64 (go.StructType []) #map.nil #body].
       [wp_map_nil_for_range_w64] is the same instance with [K := w64],
       [V := unit] filled in, which is enough for every map raft ranges over.
       The right fix in [map.v] is [Proof using ffi_sem ffi_interp0 heapGS0 sem_fn pre_sem.]
       (or moving the instance, and [pure_wp_map_nil_len] next to it, which
       has the same defect, out of the [K V] context). *)
From New.golang.theory Require Export map.

Set Default Proof Using "Type".

Section nil_range.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

#[global] Instance wp_map_nil_for_range_w64 (body : func.t) key_type elem_type :
  PureWp True (map.for_range key_type elem_type #map.nil #body) execute_val :=
  wp_map_nil_for_range (K:=w64) (V:=unit) body key_type elem_type.

End nil_range.

Section for_range_keep.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Local Set Default Proof Using "All".

Context `[!ZeroVal K] `[!EqDecision K] `[!Countable K] `[!ZeroVal V]
  `[IntoValInj0 : !go.IntoValInj K].

Lemma wp_map_for_range_keep P stk E (body : func.t) key_type elem_type mref (m : gmap K V) dq
  `{!TypedPointsto K} `{!IntoValTyped K key_type} :
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ -∗
     (P keys 0 ∗
      □ (∀ i key v, ⌜ keys !! (Z.to_nat i) = Some key ∧ m !! key = Some v ⌝ -∗ P keys i -∗
                    WP #body #key #v @ stk; E
                      {{ v, for_map_postcondition (P keys (i+1))
                              (λ v, mref ↦${dq} m -∗ Φ v) v }}) ∗
      (P keys (Z.of_nat (size m)) -∗ mref ↦${dq} m -∗ Φ execute_val))
  ) -∗
  WP map.for_range key_type elem_type #mref #body @ stk; E {{ Φ }}.
Proof.
  iIntros "% Hm HΦ".
  wp_call.
  iDestruct (own_map_not_nil with "[$]") as %?.
  wp_if_destruct; first by exfalso.
  rewrite own_map_unseal. iNamed "Hm".
  (* the map, re-sealed, once [FinishRead] has given the points-to back *)
  iAssert (□ ∀ mv', ⌜ is_map_pure mv' mp ⌝ -∗ ⌜ map_default mv' = #(zero_val V) ⌝ -∗
             heap_pointsto mref dq mv' -∗ own_map_def mref dq m)%I with "[]" as "#Hseal".
  { iIntros "!> % %% Hown". iExists _, _. iFrame "Hown". iPureIntro. eauto. }
  wp_apply (_internal_wp_untyped_start_read with "Hown") as "Hown".
  wp_apply (wp_InternalMapForRange with "[//]"). iIntros "%ks %Hdom'".
  eapply go.is_map_domain_pure in Hdom'; last done.
  destruct Hdom' as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv. rewrite -list_elem_of_In.
    intros Hk. specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hk. apply Hdom in Hk. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst.
  iAssert (⌜ _ ⌝)%I with "[]" as "%Hfacts".
  2: iDestruct ("HΦ" $! keys with "[]") as "(HP & #Hiter & HΦ)".
  2: iPureIntro; exact Hfacts.
  { iPureIntro. eassert _ as Hl.
    2:{ split; first eexact Hl.
        apply NoDup_fmap in Hks_nodup; last tc_solve.
        rewrite <- (size_list_to_set (C:=gset K)); last done.
        rewrite Hl. rewrite size_dom //. }
    rewrite sets.set_eq. intros k.
    rewrite elem_of_list_to_set.
    specialize (Hks #k). specialize (Hagree k).
    rewrite list_elem_of_fmap_inj in Hks.
    rewrite -Hks. rewrite Hagree. rewrite elem_of_dom.
    by destruct lookup.
  }
  (* foldr  *)
  pose (i := 0).
  change (P keys 0) with (P keys i).
  iFreeze "Hiter".
  replace (into_val <$> keys) with (into_val <$> (drop (Z.to_nat i) keys)).
  2:{ rewrite drop_0 //. }
  iThaw "Hiter".
  iAssert (⌜ 0 ≤ i ≤ length keys ⌝)%I as "-#Hi"; first word.
  generalize i. clear i. intros i.
  iLöb as "IH" forall (i). iDestruct "Hi" as "%".
  destruct (decide (i < length keys)).
  2:{
    assert (i = length keys) by word. subst.
    nat_cleanup. rewrite drop_all /=.
    wp_auto. wp_apply "Hown". iIntros "Hown".
    wp_auto.
    destruct Hfacts as (? & -> & ?).
    iApply ("HΦ" with "HP").
    by iApply ("Hseal" with "[//] [//] Hown").
  }
  list_elem keys i as key.
  destruct (m !! key) eqn:Hlookup.
  2:{
    exfalso. apply not_elem_of_dom_2 in Hlookup as Hkey_m.
    destruct Hfacts as [Hfact _]. rewrite <- Hfact in Hkey_m.
    rewrite elem_of_list_to_set in Hkey_m.
    rewrite list_elem_of_lookup in Hkey_m. naive_solver.
  }
  iSpecialize ("Hiter" $! i key v with "[//] HP").
  erewrite drop_S; last done. rewrite fmap_cons foldr_cons.
  rewrite Hagree Hlookup /=. wp_apply (wp_wand with "Hiter") as (execv) "Hpost" --no-auto.
  rewrite -Z2Nat.inj_succ; last lia.
  iDestruct "Hpost" as "[[-> H]|Hpost]".
  { wp_auto. rewrite continue_val_unseal. wp_auto.
    iApply ("IH" with "[$] [$] [$]").
    word. }
  wp_auto.
  iDestruct "Hpost" as "[[-> H]|Hpost]".
  { rewrite execute_val_unseal. wp_auto.
    iApply ("IH" with "[$] [$] [$]").
    word. }
  iDestruct "Hpost" as "[[-> H]|Hpost]".
  { rewrite break_val_unseal. wp_auto.
    wp_apply "Hown". iIntros "Hown". wp_auto.
    iApply "H". by iApply ("Hseal" with "[//] [//] Hown"). }
  iDestruct "Hpost" as "(%  & -> & HΦ')".
  rewrite return_val_unseal.
  wp_auto. wp_apply "Hown" as "Hown".
  iApply "HΦ'". by iApply ("Hseal" with "[//] [//] Hown").
Qed.

End for_range_keep.
