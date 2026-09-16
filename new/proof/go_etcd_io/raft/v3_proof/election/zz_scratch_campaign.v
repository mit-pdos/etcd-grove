(* TEMPORARY scratch file for developing proof_raft__campaign helpers.
   Delete before finishing. *)
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_slices.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Lemma wp_map_len_uint64 (mref : loc) dq (m : gmap w64 unit) :
  {{{ mref ↦${dq} m }}}
    #(functions go.len [go.MapType go.uint64 (go.StructType [])]) #mref
  {{{ RET #(W64 (size m)); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm". rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  destruct (go.is_map_domain_exists _ _ His_map) as [ks Hks].
  pose proof (go.internal_map_length_step_pure mv ks Hks) as Hlenstep.
  wp_auto.
  (* [length ks = size m]: the same argument [wp_map_for_range] makes. *)
  assert (length ks = size m) as ->.
  { eapply go.is_map_domain_pure in Hks; last exact His_map.
    destruct Hks as [Hnodup Hiff].
    assert (Forall (λ kv, ∃ (k : w64), kv = #k) ks) as Heq.
    { rewrite Forall_forall. intros kv. rewrite -list_elem_of_In.
      intros Hk. apply Hdom. by apply Hiff. }
    apply Forall_exists_Forall2_l in Heq as [keys Heq].
    apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
    rewrite list_fmap_id in Heq. subst.
    assert (list_to_set keys = dom m) as Hl.
    { rewrite sets.set_eq. intros k. rewrite elem_of_list_to_set.
      specialize (Hiff #k). specialize (Hagree k).
      rewrite list_elem_of_fmap_inj in Hiff.
      rewrite -Hiff Hagree elem_of_dom. by destruct lookup. }
    apply NoDup_fmap in Hnodup; last tc_solve.
    rewrite length_fmap.
    rewrite <- (size_list_to_set (C:=gset w64)); last done.
    rewrite Hl size_dom //. }
  (* nonce 983929366 *) iApply "HΦ". iFrame "∗%".
Qed.

Lemma own_raft_phys_outbox_perm (r : loc) (id : w64) (s : nstate.t)
    (o1 o2 : list msg.t) :
  o1 ≡ₚ o2 →
  own_raft_phys cfg r id (s <| nstate.outbox := o1 |>) -∗
  own_raft_phys cfg r id (s <| nstate.outbox := o2 |>).
Proof.
  intros Hperm. rewrite /own_raft_phys. iIntros "H". iNamed "H".
  iExists rv, msgs, msgsAA, lok. simpl in *. iFrame "∗#%".
  (* nonce 983929366 *) iPureIntro. by rewrite -Hperm.
Qed.

End helpers.
