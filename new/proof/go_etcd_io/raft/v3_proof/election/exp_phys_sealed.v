(** * EXPERIMENT: a sealed [own_raft_phys] with an access-lemma API

    Not reached from [should_build.v].  This file exists to measure what it
    costs to stop unfolding [own_raft_phys] -- see notes/journal.md. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** ** The predicate, indexed by the physical values of the fields the
       election path writes.

    [own_raft_phys' γ r id s] is the special case where those values agree
    with the model state [s].  The extra indices exist so that the states a
    Go function passes *through* -- [lead] updated but [state] not yet -- are
    expressible without unfolding. *)
Definition own_raft_phys_at_def γ (r : loc) (id : w64)
  (term vote lead : w64) (st : w64) (votes : gmap w64 bool) : iProp Σ :=
  ∃ (rv : raft.raft.t) (msgs msgsAA : list raftpb.Message.t)
    (lok : interface.t_ok),
  "Hr" ∷ r ↦ rv ∗
  "%Hid" ∷ ⌜ rv.(raft.raft.id') = id ⌝ ∗
  "%Hterm" ∷ ⌜ rv.(raft.raft.Term') = term ⌝ ∗
  "%Hvote" ∷ ⌜ rv.(raft.raft.Vote') = vote ⌝ ∗
  "%Hlead" ∷ ⌜ rv.(raft.raft.lead') = lead ⌝ ∗
  "%Hstate" ∷ ⌜ rv.(raft.raft.state') = st ⌝ ∗
  "Htrk" ∷ own_tracker rv.(raft.raft.trk') votes ∗
  "Hlog" ∷ own_raftLog rv.(raft.raft.raftLog') ∗
  "Hmsgs" ∷ rv.(raft.raft.msgs') ↦* msgs ∗
  "Hmsgs_cap" ∷ own_slice_cap raftpb.Message.t rv.(raft.raft.msgs') (DfracOwn 1) ∗
  "HmsgsAA" ∷ rv.(raft.raft.msgsAfterAppend') ↦* msgsAA ∗
  "HmsgsAA_cap" ∷ own_slice_cap raftpb.Message.t
                    rv.(raft.raft.msgsAfterAppend') (DfracOwn 1) ∗
  "#Hsent" ∷ ([∗ list] m ∈ msgs, is_phys_msg γ m) ∗
  "#HsentAA" ∷ ([∗ list] m ∈ msgsAA, is_phys_msg γ m) ∗
  "%HnoPreVote" ∷ ⌜ rv.(raft.raft.preVote') = false ⌝ ∗
  "%HnoCheckQuorum" ∷ ⌜ rv.(raft.raft.checkQuorum') = false ⌝ ∗
  "%HnoLearner" ∷ ⌜ rv.(raft.raft.isLearner') = false ⌝ ∗
  "%HnoTransfer" ∷ ⌜ rv.(raft.raft.leadTransferee') = W64 0 ⌝ ∗
  "%Hid_nz" ∷ ⌜ id ≠ W64 0 ⌝ ∗
  "%Hlok" ∷ ⌜ rv.(raft.raft.logger') = interface.ok lok ⌝ ∗
  "#Hlogger" ∷ is_Logger lok ∗
  "Hmisc" ∷ own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
             rv.(raft.raft.pendingReadIndexMessages').

Program Definition own_raft_phys_at := sealed @own_raft_phys_at_def.
Definition own_raft_phys_at_unseal : own_raft_phys_at = _ := seal_eq _.

Definition own_raft_phys' γ r id s : iProp Σ :=
  own_raft_phys_at γ r id s.(nstate.term) s.(nstate.vote) s.(nstate.lead)
    (state_w64 s.(nstate.role)) s.(nstate.votes).

Local Ltac unseal :=
  rewrite ?own_raft_phys_at_unseal /own_raft_phys_at_def.

(** Open the struct, hand out one field, put the rest back.  [rv'] is the
    struct value the reassembled predicate is at. *)
Local Ltac phys_open :=
  constructor; unseal; iIntros "H"; iNamed "H";
  iDestruct (typed_pointsto_not_null with "Hr") as "%Hnn";
  iStructNamed "Hr".

Local Ltac phys_close rv' :=
  iExists rv', _, _, _; iFrame "∗#%";
  first [ iApply typed_pointsto_combine; [done | iFrame]
        | iSplitL; [ iApply typed_pointsto_combine; [done | iFrame]
                   | by iPureIntro ] ].

(** ** Reads of the model-determined fields.

    Registered as [AccessStrict] instances, so [wp_auto] can pick them up
    exactly the way it picks up the generated whole-struct instances. *)

#[global] Instance phys_load_id γ r id t v l st vs :
  AccessStrict
    (r.[raft.raft.t, "id"] ↦ id) (r.[raft.raft.t, "id"] ↦ id)
    (own_raft_phys_at γ r id t v l st vs) (own_raft_phys_at γ r id t v l st vs).
Proof. phys_open. subst id. iFrame "id". iIntros "id". phys_close rv. Qed.

#[global] Instance phys_load_Term γ r id t v l st vs :
  AccessStrict
    (r.[raft.raft.t, "Term"] ↦ t) (r.[raft.raft.t, "Term"] ↦ t)
    (own_raft_phys_at γ r id t v l st vs) (own_raft_phys_at γ r id t v l st vs).
Proof. phys_open. subst t. iFrame "Term". iIntros "Term". phys_close rv. Qed.

#[global] Instance phys_load_state γ r id t v l st vs :
  AccessStrict
    (r.[raft.raft.t, "state"] ↦ st) (r.[raft.raft.t, "state"] ↦ st)
    (own_raft_phys_at γ r id t v l st vs) (own_raft_phys_at γ r id t v l st vs).
Proof. phys_open. subst st. iFrame "state". iIntros "state". phys_close rv. Qed.

(** ** Writes of model-determined fields: they move the index. *)

#[global] Instance phys_store_state γ r id t v l st st' vs :
  AccessStrict
    (r.[raft.raft.t, "state"] ↦ st) (r.[raft.raft.t, "state"] ↦ st')
    (own_raft_phys_at γ r id t v l st vs)
    (own_raft_phys_at γ r id t v l st' vs).
Proof.
  phys_open. subst st. iFrame "state". iIntros "state".
  phys_close (rv <| raft.raft.state' := st' |>).
Qed.

#[global] Instance phys_store_lead γ r id t v l l' st vs :
  AccessStrict
    (r.[raft.raft.t, "lead"] ↦ l) (r.[raft.raft.t, "lead"] ↦ l')
    (own_raft_phys_at γ r id t v l st vs)
    (own_raft_phys_at γ r id t v l' st vs).
Proof.
  phys_open. subst l. iFrame "lead". iIntros "lead".
  phys_close (rv <| raft.raft.lead' := l' |>).
Qed.

(** ** A write of a field the model does not constrain.

    [step] and [tick] hold closures the predicate says nothing about, so the
    old value cannot be named and this cannot be an [AccessStrict] instance
    (the class must produce a concrete [A]).  It is an explicit accessor the
    proof has to invoke by hand. *)
Lemma phys_step_acc γ r id t v l st vs :
  own_raft_phys_at γ r id t v l st vs -∗
  ∃ (f : raft.stepFunc.t), r.[raft.raft.t, "step"] ↦ f ∗
    (∀ (g : raft.stepFunc.t), r.[raft.raft.t, "step"] ↦ g -∗
       own_raft_phys_at γ r id t v l st vs).
Proof.
  unseal. iIntros "H". iNamed "H".
  iDestruct (typed_pointsto_not_null with "Hr") as "%Hnn".
  iStructNamed "Hr". iFrame "step". iIntros "%g step".
  phys_close (rv <| raft.raft.step' := g |>).
Qed.


(** [tick] is the same shape as [step]. *)
Lemma phys_tick_acc γ r id t v l st vs :
  own_raft_phys_at γ r id t v l st vs -∗
  ∃ (f : func.t), r.[raft.raft.t, "tick"] ↦ f ∗
    (∀ (g : func.t), r.[raft.raft.t, "tick"] ↦ g -∗
       own_raft_phys_at γ r id t v l st vs).
Proof.
  unseal. iIntros "H". iNamed "H".
  iDestruct (typed_pointsto_not_null with "Hr") as "%Hnn".
  iStructNamed "Hr". iFrame "tick". iIntros "%g tick".
  phys_close (rv <| raft.raft.tick' := g |>).
Qed.

(** [logger] is read, but its value is existentially quantified inside the
    predicate, so this cannot be an [AccessStrict] instance either. *)
Lemma phys_logger_acc γ r id t v l st vs :
  own_raft_phys_at γ r id t v l st vs -∗
  ∃ lok, r.[raft.raft.t, "logger"] ↦ interface.ok lok ∗ is_Logger lok ∗
    (r.[raft.raft.t, "logger"] ↦ interface.ok lok -∗
       own_raft_phys_at γ r id t v l st vs).
Proof.
  unseal. iIntros "H". iNamed "H".
  iDestruct (typed_pointsto_not_null with "Hr") as "%Hnn".
  iStructNamed "Hr". rewrite Hlok. iFrame "logger #".
  iIntros "logger". rewrite -Hlok. phys_close rv.
Qed.

(** The out-of-scope part of the struct, for the [traceX] specs. *)
Lemma phys_misc_acc γ r id t v l st vs :
  own_raft_phys_at γ r id t v l st vs -∗
  ∃ rs ro pri, own_raft_misc rs ro pri ∗
    (own_raft_misc rs ro pri -∗ own_raft_phys_at γ r id t v l st vs).
Proof.
  unseal. iIntros "H". iNamed "H". iFrame "Hmisc". iIntros "Hmisc".
  iExists rv, msgs, msgsAA, lok. iFrame "∗#%".
Qed.

(** ** The experiment proper: [becomeFollower] against the sealed predicate.

    [reset]'s spec is taken as a *hypothesis* rather than an axiom, so this
    file adds nothing to the trust base and can be built by CI.  It is the
    same triple as [spec_raft__reset.v], restated at [own_raft_phys']. *)
Definition wp_reset'_spec : iProp Σ :=
  □ ∀ γ (r : loc) (id : w64) s (term : w64),
  {{{ is_pkg_init raft ∗ own_raft_phys' γ r id s }}}
    r @! (go.PointerType raft.raft) @! "reset" #term
  {{{ RET #();
      own_raft_phys' γ r id
        {| nstate.term := term;
           nstate.vote := if decide (term = s.(nstate.term))
                          then s.(nstate.vote) else W64 0;
           nstate.lead := W64 0;
           nstate.role := s.(nstate.role);
           nstate.votes := ∅ |} }}}.

Lemma exp_wp_raft__becomeFollower γ (r : loc) (id : w64) s (term lead : w64) :
  {{{ is_pkg_init raft ∗ wp_reset'_spec ∗ own_raft_phys' γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeFollower" #term #lead
  {{{ RET #(); own_raft_phys' γ r id (become_follower s term lead) }}}.
Proof.
  wp_start as "[#Hreset Hphys]".
  (* [r.step := stepFollower]: a field the model does not constrain. *)
  iDestruct (phys_step_acc with "Hphys") as "(%f & Hstep & Hback)".
  wp_auto.
  iDestruct ("Hback" with "Hstep") as "Hphys".
  wp_apply ("Hreset" with "[$Hphys]") as "Hphys".
  (* [r.tick := r.tickElection] *)
  iDestruct (phys_tick_acc with "Hphys") as "(%g & Htick & Hback)".
  wp_auto.
  iDestruct ("Hback" with "Htick") as "Hphys".
  (* [r.lead := lead] and [r.state := StateFollower] go through the
     [AccessStrict] instances, so [wp_auto] handles them. *)
  wp_auto.
  (* the log call reads [r.logger] and [r.id], [r.Term] *)
  iDestruct (phys_logger_acc with "Hphys") as "(%lok & Hlogger & #His & Hback)".
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
  wp_auto.
  wp_apply (wp_Logger__logf with "His").
  { rewrite /log_methods. set_solver. }
  iDestruct ("Hback" with "Hlogger") as "Hphys".
  iDestruct (phys_misc_acc with "Hphys") as "(%rs & %ro & %pri & Hmisc & Hback)".
  wp_apply (wp_traceBecomeFollower with "[$Hmisc]") as "Hmisc".
  iDestruct ("Hback" with "Hmisc") as "Hphys".
  iApply "HΦ". rewrite /own_raft_phys' /become_follower /=. iFrame.
Qed.

End proof.
