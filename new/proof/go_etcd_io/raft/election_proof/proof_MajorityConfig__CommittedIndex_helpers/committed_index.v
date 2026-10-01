(** Pure lemmas for [MajorityConfig.CommittedIndex].

    The function fills an [n]-slot slice from the right with the
    acknowledged indexes it gets from the [AckedIndexer] (unacknowledged
    voters leave a [0]), sorts it, and returns slot [n - (n/2 + 1)].
    [fill_perm] says the filled slice is a permutation of the per-voter
    values (unacknowledged as [0]); [sorted_quorum_index] says the slot read
    from the sorted permutation is the quorum index ([is_quorum_index],
    [inv_tracker.v]).

    Proof structure only: no [Module Type], no [Parameter], no triple, so
    only [proof_MajorityConfig__CommittedIndex.v] may [Require] it. *)

Require Export New.proof.go_etcd_io.raft.election_proof.inv_tracker.

Section committed_index.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma length_omap_le {A B} (f : A → option B) (l : list A) :
  (length (omap f l) ≤ length l)%nat.
Proof.
  induction l as [|x l IH]; first done. cbn.
  destruct (f x) eqn:E; simpl; rewrite ?E; simpl; lia.
Qed.

(** The slice after the fill loop, as a multiset. *)
Lemma fill_perm (f : w64 → option w64) (l : list w64) :
  (λ v, default (W64 0) (f v)) <$> l
  ≡ₚ replicate (length l - length (omap f l)) (W64 0) ++ reverse (omap f l).
Proof.
  induction l as [|x l IH]; first done.
  pose proof (length_omap_le f l) as Hle.
  rewrite fmap_cons. cbn [omap list_omap length].
  destruct (f x) as [y|] eqn:Hfx; cbn [default length].
  - rewrite reverse_cons app_assoc.
    replace (S (length l) - S (length (omap f l)))%nat
      with (length l - length (omap f l))%nat by lia.
    rewrite IH. apply Permutation_cons_append.
  - replace (S (length l) - length (omap f l))%nat
      with (S (length l - length (omap f l))) by lia.
    rewrite replicate_S /=. by rewrite IH.
Qed.

(** One step of the fill loop: the last zero slot gets the value. *)
Lemma insert_replicate_last {A} (m : nat) (z a : A) (R : list A) :
  <[m := a]> (replicate (S m) z ++ R) = replicate m z ++ a :: R.
Proof. induction m as [|m IH]; first done. simpl. by rewrite IH. Qed.

Lemma length_filter_fmap (g : w64 → w64) (Q : w64 → Prop) `{∀ x, Decision (Q x)}
    (l : list w64) :
  length (filter Q (g <$> l)) = length (filter (λ x, Q (g x)) l).
Proof.
  induction l as [|x l IH]; first done. simpl.
  rewrite !filter_cons. destruct (decide (Q (g x))); simpl; auto.
Qed.

Lemma filter_Forall_id {A} (Q : A → Prop) `{∀ x, Decision (Q x)} (l : list A) :
  Forall Q l → filter Q l = l.
Proof.
  induction 1 as [|x l Hx _ IH]; first done.
  rewrite filter_cons_True //. by rewrite IH.
Qed.

Lemma filter_Forall_nil {A} (Q : A → Prop) `{∀ x, Decision (Q x)} (l : list A) :
  Forall (λ x, ¬ Q x) l → filter Q l = [].
Proof.
  induction 1 as [|x l Hx _ IH]; first done.
  rewrite filter_cons_False //.
Qed.

(** How many voters have a value [≥ M], counted on the sorted slice. *)
Lemma size_filter_sorted (s : gset w64) (keys : list w64) (g : w64 → w64)
    (ys : list w64) (M : w64) :
  NoDup keys → list_to_set keys = s →
  ys ≡ₚ g <$> keys →
  size (filter (λ v, uint.Z M ≤ uint.Z (g v)) s)
  = length (filter (λ x, uint.Z M ≤ uint.Z x) ys).
Proof.
  intros Hnd Hks Hperm.
  rewrite Hperm length_filter_fmap.
  symmetry.
  apply (nsat_size s (filter (λ v, uint.Z M ≤ uint.Z (g v)) s) keys
           (λ v, uint.Z M ≤ uint.Z (g v))); [| |done|done].
  - intros k Hk. split; [intros Hf%elem_of_filter; tauto | intros HP; apply elem_of_filter; done].
  - apply filter_subseteq.
Qed.

Lemma sorted_quorum_index (s : gset w64) (keys : list w64) (g : w64 → w64)
    (ys : list w64) (N : w64) :
  NoDup keys → list_to_set keys = s → length keys = size s → (0 < size s)%nat →
  ys ≡ₚ g <$> keys →
  (∀ (i j : nat) (xi xj : w64), ys !! i = Some xi → ys !! j = Some xj →
     (i < j)%nat → uint.Z xi ≤ uint.Z xj) →
  ys !! (size s - (size s / 2 + 1))%nat = Some N →
  is_quorum_index s g N.
Proof.
  intros Hnd Hks Hlen Hpos Hperm Hsorted HN.
  set (n := size s) in *.
  set (pos := (n - (n / 2 + 1))%nat) in *.
  assert (length ys = n) as Hys by (rewrite Hperm length_fmap //).
  assert (n / 2 + 1 ≤ n)%nat as Hhalf.
  { pose proof (Nat.div_mod_eq n 2). pose proof (Nat.mod_upper_bound n 2). lia. }
  split; [|split].
  - (* [N] is some voter's value *)
    assert (N ∈ g <$> keys) as Hin.
    { rewrite -Hperm. by eapply list_elem_of_lookup_2. }
    apply list_elem_of_fmap in Hin as [k [-> Hk]].
    exists k. split; last done. rewrite -Hks elem_of_list_to_set //.
  - (* the slots from [pos] on are all [≥ N]: [n/2 + 1] of them *)
    apply is_quorum_alt.
    replace (filter (λ v, uint.Z N ≤ uint.Z (g v)) s ∩ s)
      with (filter (λ v, uint.Z N ≤ uint.Z (g v)) s) by set_solver.
    rewrite (size_filter_sorted s keys g ys N Hnd Hks Hperm).
    rewrite -(take_drop pos ys) stdpp.list_basics.list.filter_app length_app.
    rewrite (filter_Forall_id _ (drop pos ys)).
    + rewrite length_drop. fold n. lia.
    + apply Forall_lookup_2. intros i x Hx.
      rewrite lookup_drop in Hx.
      destruct i as [|i].
      * rewrite Nat.add_0_r HN in Hx. by injection Hx as ->.
      * eapply Hsorted; [exact HN | exact Hx | lia].
  - (* any larger index: only the slots after [pos] can reach it *)
    intros N' HN' Hq.
    apply is_quorum_alt in Hq.
    replace (filter (λ v, uint.Z N' ≤ uint.Z (g v)) s ∩ s)
      with (filter (λ v, uint.Z N' ≤ uint.Z (g v)) s) in Hq by set_solver.
    rewrite (size_filter_sorted s keys g ys N' Hnd Hks Hperm) in Hq.
    rewrite -(take_drop (S pos) ys) stdpp.list_basics.list.filter_app length_app in Hq.
    rewrite (filter_Forall_nil _ (take (S pos) ys)) in Hq.
    + cbn [length] in Hq.
      match type of Hq with (_ ≤ 0 + length ?F)%nat => assert (length F ≤ length (drop (S pos) ys))%nat as Hl by apply length_filter end.
      rewrite length_drop Hys in Hl. unfold pos, n in *. remember (size s `div` 2) as h. remember (length (filter _ _)) as L. clear -Hq Hl Hhalf. lia.
    + apply Forall_lookup_2. intros i x Hx.
      rewrite lookup_take_Some in Hx. destruct Hx as [Hx Hi].
      assert (uint.Z x ≤ uint.Z N).
      { destruct (decide (i = pos)) as [->|Hne].
        - rewrite HN in Hx. by injection Hx as ->.
        - eapply Hsorted; [exact Hx | exact HN | lia]. }
      lia.
Qed.

End committed_index.
