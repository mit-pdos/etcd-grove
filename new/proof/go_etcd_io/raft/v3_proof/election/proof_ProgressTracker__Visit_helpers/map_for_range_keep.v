(** [wp_map_for_range_keep]: the framework's [wp_map_for_range]
    ([new/golang/theory/map.v]) with the map's points-to handed back.

    [Visit] ranges over [p.Progress] to collect the ids and then needs the
    map again -- for the [p.Progress[id]] lookups in the second range and to
    re-establish [own_tracker] -- but [wp_map_for_range] *consumes*
    [mref ↦${dq} m]: its proof ends in [iApply "HΦ". iFrame.] and drops the
    [heap_pointsto] that [FinishRead] returned.  This lemma is the same
    proof with the last line of each exit fixed, so the map comes back in
    the final continuation and, on [break]/[return], through the
    postcondition ([λ v, mref ↦${dq} m -∗ Φ v]).

    It is a **verbatim copy** of the lemma of the same name in
    [proof_JointConfig__IDs_helpers/map_for_range_keep.v] (2026-09-19),
    which only [proof_JointConfig__IDs.v] may [Require] -- the [*_helpers]
    rule of [etc/check-module-discipline.py].  Both copies exist so that no
    proof edits [theory/map.v], an edit that invalidates the [.vos] of the
    whole Goose-generated raft closure under every agent sharing the
    checkout.  The repair belongs in [map.v]; when it lands there, delete
    both helper files.

    This is proof structure, not specification: no [Module Type], no
    [Parameter], no triple about a Go function.  Nothing but
    [proof_ProgressTracker__Visit.v] may [Require] it. *)
From New.golang.theory Require Export map.

Set Default Proof Using "Type".

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
