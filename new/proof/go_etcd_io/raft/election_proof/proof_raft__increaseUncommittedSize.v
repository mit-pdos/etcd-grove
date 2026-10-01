Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__increaseUncommittedSize.

Module RaftIncreaseUncommittedSizeProof
  (P : RAFT__INCREASEUNCOMMITTEDSIZE_POSTULATES) :
  RAFT__INCREASEUNCOMMITTEDSIZE.
Import P.

  (** The fall-through: [uncommittedSize += s], then [return true]. *)
  Local Ltac incr :=
    wp_apply (wp_raft_load_uncommittedSize with "Hphys") as "%u_inc Hphys";
    wp_apply (wp_raft_store_uncommittedSize with "Hphys") as "Hphys";
    iApply "HΦ"; iFrame; done.

  Lemma wp_raft__increaseUncommittedSize :
    wp_raft__increaseUncommittedSize_body.
  Proof.
    intros_ambient.
    intros cfg r id s es ents dq.
    wp_start as "H". iNamed "H". wp_auto.
    (* [payloadsSize] pins the result only for an all-empty batch, as an
       implication -- exactly the shape the postcondition passes on. *)
    wp_apply (wp_payloadsSize with "[$Hes]") as "%psz [Hes %Hpsz]".
    (* [&&] is a nest of [if]s over fields [own_raft_phys] does not track;
       walk it.  Every fall-through (the [2:] goals) reaches the increment
       and [return true]: [incr]. *)
    wp_apply (wp_raft_load_uncommittedSize with "Hphys") as "%u Hphys".
    case_bool_decide as Hu; wp_auto.
    2: { incr. }
    case_bool_decide as Hp; wp_auto.
    2: { incr. }
    wp_apply (wp_raft_load_uncommittedSize with "Hphys") as "%u' Hphys".
    wp_apply (wp_raft_load_maxUncommittedSize with "Hphys") as "%m Hphys".
    case_bool_decide as Hm; wp_auto.
    2: { incr. }
    (* the reject path: the payload is positive, so the batch is not
       all-empty *)
    iApply "HΦ". iFrame. iPureIntro. intros Hz.
    rewrite (Hpsz Hz) in Hp. word.
  Qed.


End RaftIncreaseUncommittedSizeProof.
