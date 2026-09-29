Require Export New.proof.go_etcd_io.raft.election_proof.postulates_JointConfig__IDs.

Module JointConfigIDsProof (P : JOINTCONFIG__IDS_POSTULATES) : JOINTCONFIG__IDS.

  (* [Proof using Type], not the file's [W] default: [W] would force
     [package_sem] into the discharged signature, and this constant's former
     [Axiom] form did not have it.  Checked -- with [Proof using Type] the type
     of this lemma is syntactically identical to the axiom it replaces, so no
     call site changes.  See notes/gotchas.md. *)
  Lemma wp_JointConfig__IDs : wp_JointConfig__IDs_body.
  Proof.
    intros_ambient.
    intros cfg.
    intros trk tv votes prs pvs.
    wp_start as "[Htrk Hown]". iNamed "Hown".
    (* [wp_auto] reads [r.trk.Config.Voters] out of [trk ↦ tv] and reduces the
       pointer method to the value method applied to the [JointConfig] value. *)
    wp_auto.
    (* Two [wp_call]s, not one: [JointConfig'ptr_IDs_unfold] is the wrapper
       [λ: "$r", MethodResolve JointConfig "IDs" (![JointConfig] "$r")], so the
       first call enters the wrapper and the second enters [JointConfig__IDsⁱᵐᵖˡ].
       A single [wp_call] leaves [WP quorum.JointConfig__IDsⁱᵐᵖˡ …] and the next
       [wp_auto] then reports "Failed to progress". *)
    wp_method_call. wp_call. wp_call.
    (* [GoAlloc JointConfig] gives ["c" ∷ c_ptr ↦ tv.(Config').(Voters')]; note
       this does *not* hit the [alloc_array ⤳ AngelicExit] escape hatch. *)
    wp_auto.
    (* [m := map[uint64]struct{}{}] *)
    wp_apply wp_map_make1. iIntros "%mref Hmref".
    wp_auto.
    (* [c[0]]: [wp_auto] has reduced [IndexRef JointConfig (#c_ptr, #(W64 0))]
       to [#(array_index_ref map.t 0 c_ptr)] and stopped at the load of it.
       Peel element 0 off the array; [Hvoters_arr] says it is [voters_ref]. *)
    iDestruct (array_acc _ 0 with "c") as "[Hc0 Hcback]".
    { done. }
    { rewrite Hvoters_arr. done. }
    wp_auto.
    (* [for id := range c[0] { m[id] = struct{}{} }].  The invariant carries
       [dom] of the partial map: after [i] iterations it is the first [i]
       keys of the enumeration.  [id] is the loop variable, assigned every
       iteration, so it is existentially quantified inside the invariant. *)
    set (Pmap := (λ (keys : list w64) (i : Z),
      ∃ (x : w64) (idm : gmap w64 unit),
        "%Hi" ∷ ⌜ 0 ≤ i ⌝ ∗
        "%Hidm" ∷ ⌜ dom idm = list_to_set (take (Z.to_nat i) keys) ⌝ ∗
        "id" ∷ id_ptr ↦ x ∗
        "m" ∷ m_ptr ↦ mref ∗
        "Hmref" ∷ mref ↦$ idm)%I).
    wp_apply (wp_map_for_range Pmap with "Hvoters").
    iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
    iSplitL "id m Hmref".
    { rewrite /Pmap. iExists (W64 0), ∅. rewrite take_0. iFrame.
      iPureIntro. split; [lia|]. rewrite dom_empty_L //. }
    iSplitL "".
    { iIntros "!>" (i key vv) "[%Hkey %Hvv] HP". rewrite /Pmap. iNamed "HP".
      wp_auto.
      wp_apply (wp_map_insert with "Hmref"). iIntros "Hmref".
      wp_auto.
      iRight. iLeft. iSplitR; first done.
      iExists key, _. iFrame.
      iPureIntro. split; first lia.
      assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as Hsucc by lia.
      rewrite Hsucc (take_S_r _ _ _ Hkey) list_to_set_app_L dom_insert_L Hidm.
      set_solver. }
    (* the range is over: [dom idm] is every key, i.e. [dom voters = cfg] *)
    iIntros "HP Hvoters". rewrite /Pmap. iNamed "HP".
    rewrite Nat2Z.id -Hklen firstn_all in Hidm.
    (* [c[1]]: put element 0 back, peel element 1 off; it is [map.nil], and
       ranging over the nil map is the pure step [wp_map_nil_for_range],
       which [wp_auto] takes once the loop variable is allocated. *)
    iDestruct ("Hcback" with "Hc0") as "c".
    rewrite Hvoters_arr /=.
    iDestruct (array_acc _ 1 with "c") as "[Hc1 Hcback]".
    { done. }
    { done. }
    wp_auto.
    wp_alloc id2_ptr as "id2".
    wp_auto.
    (* [return m] *)
    (* [iFrame "Hmref"] before the split would be matched against
       [own_tracker]'s own [voters_ref ↦$ voters]; re-seal the tracker first. *)
    iApply "HΦ". iFrame "Htrk".
    iSplitL "Hvotes Hprogs Hvoters Hlearners HlearnersNext".
    { rewrite /own_tracker. iExists voters_ref, voters, learners, learnersNext.
      iFrame "∗#%". }
    iFrame "Hmref".
    iPureIntro. rewrite Hidm Hkset Hvoters_dom //.
  Qed.

End JointConfigIDsProof.
