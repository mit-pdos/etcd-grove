From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lang lifting ipersist.
From Perennial.Helpers Require Export ipm Tactics Transitions.
From iris.proofmode Require Import coq_tactics.
(* make sure solve_proper comes from stdpp and not Coq *)
From stdpp Require Export tactics.
From New.golang.defn Require Export pre.
From Perennial Require Export base.
From Ltac2 Require Import Ltac2.
Import Printf.
Set Default Proof Mode "Classic".

(** Classes that are used to tell [wp_pures] about steps it can take. *)
Section classes.

(* FIXME: add later credits *)
Class PureWp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
             {go_gctx : GoGlobalContext}
  φ (e : expr) (e' : expr) :=
  pure_wp_wp : ∀ stk E Φ (H : φ) K,
  ▷ (£ 1 -∗  WP (fill K e') @ stk ; E {{ Φ }}) -∗ WP (fill K e) @ stk; E {{ Φ }}.

Global Hint Mode PureWp - - - - - - - - - ! - : typeclass_instances.

Lemma tac_wp_pure_wp `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                     {go_gctx : GoGlobalContext}
      K e1 {e2 φ} (Hwp:PureWp φ e1 e2) Δ Δ' s E Φ :
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". iApply Hwp; [done|iIntros "!# _ //"].
Qed.

Lemma tac_wp_pure_wp_later_credit `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                                  {go_gctx : GoGlobalContext}
      K e1 {e2 φ} (Hwp:PureWp φ e1 e2) Δ Δ' s E Φ :
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (£ 1 -∗ WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". by iApply Hwp.
Qed.

(** Fast path for pure steps.

    The [▷] in [PureWp] lets a pure step strip one later off every hypothesis,
    which [tac_wp_pure_wp] does through [MaybeIntoLaterNEnvs]. That typeclass
    search unfolds every hypothesis through its definition looking for a [▷]
    (it recurses into [∗], [∃], big ops, ...), and on a context of a dozen
    abstract predicates it is the single most expensive part of a [wp_pure]
    step -- measured at ~40% of [wp_auto] on the etcd raft proofs. When no [▷]
    occurs syntactically in the context there is nothing to strip, and
    [later_intro] does the job with no search at all. [wp_pure] picks the fast
    path with [wp_envs_has_later] below. *)
Lemma tac_wp_pure_wp_no_later `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                     {go_gctx : GoGlobalContext}
      K e1 {e2 φ} (Hwp:PureWp φ e1 e2) Δ s E Φ :
  φ →
  envs_entails Δ (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ. rewrite HΔ. iIntros "H".
  iApply Hwp; [done|]. iNext. iIntros "_". iApply "H".
Qed.

Lemma tac_wp_pure_wp_later_credit_no_later `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                                  {go_gctx : GoGlobalContext}
      K e1 {e2 φ} (Hwp:PureWp φ e1 e2) Δ s E Φ :
  φ →
  envs_entails Δ (£ 1 -∗ WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ. rewrite HΔ. iIntros "H".
  iApply Hwp; [done|]. iNext. iApply "H".
Qed.

(* Now a few lemmas to help establish PureWp in other ways. *)
Lemma pure_exec_pure_wp n
  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
  {go_gctx : GoGlobalContext} {φ e e'} :
  PureExec φ (S n) e e' → PureWp φ e e'.
Proof.
  intros ??????.
  iIntros "Hk".
  pose proof @pure_exec_fill.
  iApply (lifting.wp_pure_step_later with "[-]"); [done|].
  repeat iModIntro. iIntros "[Hlc _]". by iApply "Hk".
Qed.

Lemma pure_wp_val `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                  {go_gctx : GoGlobalContext} φ (e : expr) (v' : val) :
  (∀ stk E Φ (H: φ),
     ▷ (£ 1 -∗  Φ v') -∗ WP e @ stk; E {{ Φ }}) →
  PureWp φ e v'.
Proof.
  intros Hwp.
  red. intros ?????.
  iIntros "HΦ".
  iApply wp_bind; auto.
  iApply Hwp; auto.
Qed.

End classes.

(** Some basic, primitive instances. Adapted to use `IntoVal`. *)
Section instances.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
         {go_gctx : GoGlobalContext} {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Ltac solve_exec_safe := intros; subst; do 4 eexists; econstructor; cbn; repeat (monad_simpl; simpl); try done.
Ltac solve_exec_puredet :=
  inversion 1; subst; unfold base_step in *; intros; repeat (monad_inv; simpl in * ); eauto.
Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance wp_snd (v1 v2 : val) : PureWp True (Snd (v1, v2)%V) v2.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_fst (v1 v2 : val) : PureWp True (Fst (v1, v2)%V) v1.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_recc f x erec : PureWp True (rec: f x := erec)%E #(func.mk f x erec).
Proof. rewrite !go.into_val_unfold. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_pair (v1 v2 : val) : PureWp True (v1, v2)%E (v1, v2)%V.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_if_false e1 e2 : PureWp True (if: #false then e1 else e2) e2.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. inv H2. done. Qed.

Global Instance wp_if_true e1 e2 : PureWp True (if: #true then e1 else e2) e1.
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. inv H2. done. Qed.

(* XXX: making this an instance results in this fact getting used even in places
  where the RecV is under a definition. Making it an explicit [Hint Extern]
  below alleviates this problem, and only applies [wp_call] when the goal
  expression is syntactically a [RecV]. *)
Definition wp_call (v2 : val) f x e :
  PureWp True (App (rec: f x := e)%V v2) (subst' x v2 (subst' f (rec: f x := e)%V e)).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance wp_call_go_func (v2 : val) f x e :
  PureWp True (App #(func.mk f x e) v2) (subst' x v2 (subst' f #(func.mk f x e) e)).
Proof. rewrite !go.into_val_unfold /=. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance pure_wp_LiteralValue l :
  PureWp True (LiteralValue l) (LiteralValueV l).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

Global Instance pure_wp_SelectStmtClauses d cs :
  PureWp True (SelectStmtClauses d cs) (SelectStmtClausesV d cs).
Proof. apply (pure_exec_pure_wp O). solve_pure_exec. Qed.

End instances.

Global Hint Extern 0 (PureWp _ (App (Val (RecV _ _ _)) _) _) => simple apply wp_call : typeclass_instances.

Section lemmas.
Lemma tac_wp_bind `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseLocalGS Σ, !gooseGlobalGS Σ}
                  {go_gctx : GoGlobalContext} K e Δ s E Φ f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that the `wp_bind`
                           tactic can `simpl` the RHS to get a concrete function
                           f which results in a nice looking output without
                           `fill K` appearing. *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

Lemma tac_wp_rec `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                 {go_gctx : GoGlobalContext} K v1 v2 {f x e} {Hwp:TCEq v1 (rec: f x := e)%V}
                 Δ Δ' s E Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (£ 1 -∗ WP (fill K (subst' x v2 (subst' f v1 e))) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K (App v1 v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". rewrite TCEq_eq in Hwp. rewrite Hwp.
  by iApply wp_call.
Qed.

(** See [tac_wp_pure_wp_no_later]. *)
Lemma tac_wp_rec_no_later `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                 {go_gctx : GoGlobalContext} K v1 v2 {f x e} {Hwp:TCEq v1 (rec: f x := e)%V}
                 Δ s E Φ :
  envs_entails Δ (£ 1 -∗ WP (fill K (subst' x v2 (subst' f v1 e))) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K (App v1 v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> HΔ. rewrite HΔ. iIntros "H".
  rewrite TCEq_eq in Hwp. rewrite Hwp.
  iApply wp_call; [done|]. iNext. iApply "H".
Qed.

Lemma tac_wp_call_go_func `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}
                          {go_gctx : GoGlobalContext} {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
      K f x e v2 Δ Δ' s E Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP (fill K (subst' x v2 (subst' f #(func.mk f x e) e))) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K (#(func.mk f x e) v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ'. iIntros "H". iApply wp_call_go_func; [done|iIntros "!# _ //"].
Qed.

End lemmas.

(** Tactics *)

(** * Keeping the program text out of the way

    A translated Go function body is a large term (the raft [Step] body is
    ~500KB printed), and it sits inside the goal for the whole proof. Every
    proof-mode operation that traverses or unifies against the goal -- a
    failing [FromPure]/[FromSep]/[FromExist] search, [pm_reduce], typing of a
    [refine]d term -- is then linear in the program size, and a failing
    typeclass search against the [WP] costs seconds instead of microseconds.
    [done] (and so [//] and [by]) tries several of those on a [WP] goal before
    giving up.

    The remedy is to let-bind the program text while running such tactics:
    unification sees a variable, while the goal is still convertible to its
    original form. [wp_hide_body] binds the whole expression of a [WP] goal,
    [wp_bind_next] (and so [wp_apply]) binds the evaluation context, and
    [wp_unhide_body] undoes both. Every stepping tactic ([wp_pure], [wp_load],
    ...) unhides first, so the program is visible whenever the user looks at a
    goal; the hiding is an implementation detail of individual tactics. Use
    [wp_hidden tac] to run an arbitrary proof-mode tactic ([iNamed], [iFrame],
    ...) on a [WP] goal with the program hidden. *)

(** Let-bind the expression of a [WP] goal under a name starting with [__wp_].
    No-op if the goal is not a [WP] or the expression is already a variable. *)
Ltac wp_hide_body :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ ?e _) =>
      tryif is_var e then idtac
      else let x := fresh "__wp_body" in first [ set (x := e) | idtac ]
  | _ => idtac
  end.

Ltac wp_subst_hidden x := first [ subst x | unfold x in * ].
Ltac wp_ectx_simpl := cbv [fill flip foldl ectxi_language.fill_item goose_ectxi_lang fill_item].

Ltac2 wp_ident_is_hidden (id : ident) : bool :=
  let s := Ident.to_string id in
  if Int.lt (String.length s) 5 then false
  else
    String.equal (String.sub s 0 5) "__wp_".

(** Substitute every [__wp_*] let-binding back into the goal and recompute
    the evaluation contexts it stood for. No-op (and cheap) if there is none. *)
Ltac2 wp_unhide_body () : unit :=
  Control.enter (fun () =>
    let hidden := List.map (fun (id, _, _) => id)
      (List.filter (fun (id, body, _) =>
        match body with
        | Some _ => wp_ident_is_hidden id
        | None => false
        end) (Control.hyps ())) in
    match hidden with
    | [] => ()
    | _ =>
        List.iter (fun id =>
          ltac1:(x |- wp_subst_hidden x) (Ltac1.of_ident id)) hidden;
        ltac1:(wp_ectx_simpl)
    end).
Tactic Notation "wp_unhide_body" := ltac2:(wp_unhide_body ()).

(** Run [tac] with the program text of a [WP] goal hidden; see above. *)
Tactic Notation "wp_hidden" tactic3(tac) :=
  wp_hide_body; tac; wp_unhide_body.

(** Does the proof-mode context syntactically contain a [▷] (or [▷^n])? This
    is the guard for the [_no_later] fast paths: if it fails, a pure step
    can skip [MaybeIntoLaterNEnvs]. It deliberately does not look through
    definitions; a later hidden behind a definition is not stripped by the
    fast path. *)
Ltac wp_envs_has_later :=
  lazymatch goal with
  | |- environments.envs_entails ?Δ _ =>
      lazymatch Δ with
      | context [bi_later _] => idtac
      | context [bi_laterN _ _] => idtac
      | _ => fail "wp_envs_has_later: no later in context"
      end
  end.
Ltac2 wp_envs_has_later () : bool :=
  match Control.case (fun () => ltac1:(wp_envs_has_later)) with
  | Val _ => true
  | Err _ => false
  end.

(** [done] on a [WP] goal is restricted and hides the program text first.

    stdpp's [done] runs [trivial], whose Iris hints try [iAssumption],
    [iPureIntro], [iSplit], ... against the goal, each of which is a failing
    typeclass search linear in the program size (~2s each on the raft [Step]
    body). It then [split]s the goal -- [envs_entails] unfolds to the
    [uPred_entails] record -- and keeps going *inside the model* with
    [intros], [trivial], [contradiction] on hypotheses that are the whole
    proof-mode context unfolded to [uPred]; on a big goal that alone was
    measured at ~38s per [//]. Nothing in a program proof is ever closed that
    way, so on a [WP] goal [done] tries only what can work: [fast_done] and
    [trivial], with the program let-bound. [solve] rolls the [set] back on
    failure, so nothing is visible outside. On every other goal [done] is
    stdpp's, copied verbatim into [wp_done_core] -- keep it verbatim: an
    extra arm that called [done] recursively on [¬_] hypotheses was
    exponential in the number of such hypotheses (345s on one [//] in
    [proof_raft__campaign.v]). *)
Ltac wp_done_core :=
  solve
  [ repeat first
    [ fast_done
    | solve [trivial]
    | progress intros
    | solve [symmetry; trivial]
    | solve [apply not_symmetry; trivial]
    | discriminate
    | contradiction
    | split
    | match goal with H : is_Some None |- _ => destruct H as [? [=]] end
    | match goal with H : ¬_ |- _ => case H; clear H; fast_done end ]
  ].
Ltac wp_done_wp_goal :=
  solve [ wp_hide_body; first [ fast_done | solve [trivial] ] ].
Ltac done ::=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ _ _) => wp_done_wp_goal
  | |- context [wp _ _ _ _] =>
      (* e.g. [H → envs_entails Δ (WP …)], which is what ssreflect's
         [rewrite … // in H] hands to [done]: the [in] clause reverts [H]
         first.  stdpp's [done] would [intros] and then run the whole
         cascade against the visible program (~36s measured). *)
      solve [ intros; wp_done_wp_goal ]
  | _ => wp_done_core
  end.

Ltac2 Type exn ::= [ Walk_expr_more ].
Ltac2 Type exn ::= [ Walk_expr_not_found ].

Ltac2 walk_expr (e : constr) (f : constr -> constr -> 'a) : 'a :=
  let rec walk_ctx (e : constr) (k : constr) :=
    lazy_match! e with | Val _ => Control.zero Walk_expr_not_found | _ => () end;
    match Control.case (fun () => f e k) with
    | Val (a, _) => a
    | Err Walk_expr_more =>
        lazy_match! e with
        | fill ?k' ?e                     => walk_ctx e constr:($k ++ $k')
        | App ?e1 (Val ?v)                => walk_ctx e1 constr:(@AppLCtx _ $v :: $k)
        | App ?e1 ?e2                     => walk_ctx e2 constr:(@AppRCtx _ $e1 :: $k)
        | If ?e0 ?e1 ?e2                  => walk_ctx e0 constr:(IfCtx $e1 $e2 :: $k)
        | Pair (Val ?v) ?e                => walk_ctx e constr:(PairRCtx $v :: $k)
        | Pair ?e1 ?e2                    => walk_ctx e1 constr:(PairLCtx $e2 :: $k)
        | Fst ?e                          => walk_ctx e constr:(@FstCtx _ :: $k)
        | Snd ?e                          => walk_ctx e constr:(@SndCtx _ :: $k)
        | Primitive2 ?op (Val ?v) ?e      => walk_ctx e constr:(@Primitive2RCtx _ $op $v :: $k)
        | Primitive2 ?op ?e1 ?e2          => walk_ctx e1 constr:(@Primitive2LCtx _ $op $e2 :: $k)
        | Primitive1 ?op ?e               => walk_ctx e constr:(@Primitive1Ctx _ $op :: $k)
        | @ExternalOp ?ext ?op ?e         => walk_ctx e constr:(@ExternalOpCtx $ext $op :: $k)
        | CmpXchg (Val ?v0) (Val ?v1) ?e2 => walk_ctx e2 constr:(CmpXchgRCtx $v0 $v1 :: $k)
        | CmpXchg (Val ?v0) ?e1 ?e2       => walk_ctx e1 constr:(CmpXchgMCtx $v0 $e2 :: $k)
        | CmpXchg ?e0 ?e1 ?e2             => walk_ctx e0 constr:(CmpXchgLCtx $e1 $e2 :: $k)
        | ResolveProph (Val ?v) ?e        => walk_ctx e constr:(@ResolveProphRCtx _ $v :: $k)
        | ResolveProph ?e1 ?e2            => walk_ctx e1 constr:(@ResolveProphLCtx _ $e2 :: $k)
        | Rec _ _ _ => Control.zero Walk_expr_not_found
        | Fork _ => Control.zero Walk_expr_not_found
        | Primitive0 _ => Control.zero Walk_expr_not_found
        | LiteralValue _ => Control.zero Walk_expr_not_found
        | SelectStmtClauses _ _ => Control.zero Walk_expr_not_found
        (* fprintf'ing the expression can be quite slow. | _ => Control.zero (Tactic_failure (Some (fprintf "walk_expr: no match for expr %t" e))) *)
        | _ => Control.zero (Tactic_failure (Some (fprintf "walk_expr: no match for expr")))
        end
    | Err e => Control.zero e
    end
  in (walk_ctx e) constr:(@nil ectx_item).

Ltac2 wp_walk_unwrap t s :=
  match Control.case t with
  | Val (a, _) => a
  | Err Walk_expr_not_found => Control.backtrack_tactic_failure s
  | Err e => Control.zero e
  end
.

(* Maybe avoid MaybeIntoLaterNEnvs if there are no  laters syntactically. *)
Ltac2 wp_pure_visit e k :=
     (* This looks for an instance before eapply to make to fail fast. *)
     let pure_wp := orelse (fun () => '(ltac:(tc_solve) : PureWp _ $e _))
                      (fun _ => Control.zero Walk_expr_more) in
     if wp_envs_has_later () then
       eapply (tac_wp_pure_wp $k $e $pure_wp) >
         [ltac1:(try done)|
           ltac1:(tc_solve)|
           ltac1:(reduction.pm_prettify; simpl subst'; simpl fill)]
     else
       (* [notypeclasses refine] rather than [eapply]: no typeclass
          post-processing, no evar normalization of the (large) goal; about
          half the cost. The context is unchanged, so no [pm_prettify]. *)
       ltac1:(k e pw |- notypeclasses refine (tac_wp_pure_wp_no_later k e pw _ _ _ _ _ _))
         (Ltac1.of_constr k) (Ltac1.of_constr e) (Ltac1.of_constr pure_wp) >
         [ltac1:(try done)| ltac1:(simpl fill)].

Ltac2 wp_pure () :=
  wp_unhide_body ();
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ (Val _) _) ] => ltac1:(iApply wp_value)
  | [ |- envs_entails _ (wp _ _ ?e _) ] =>
      wp_walk_unwrap
        (fun () => walk_expr e wp_pure_visit)
        "wp_pure: could not find a head subexpression with a known next step"
  | [ |-  _ ] => Control.backtrack_tactic_failure "wp_pure: current proof is not a WP"
  end.

Ltac2 wp_pure_lc_visit e k :=
  (* This looks for an instance before eapply to make to fail fast. *)
  let pure_wp := orelse (fun () => '(ltac:(tc_solve) : PureWp _ $e _))
                   (fun _ => Control.zero Walk_expr_more) in
  if wp_envs_has_later () then
    eapply (tac_wp_pure_wp_later_credit $k $e $pure_wp) >
      [ltac1:(try done)|
        ltac1:(tc_solve)|
        ltac1:(reduction.pm_prettify; simpl subst';
               simpl fill)]
  else
    ltac1:(k e pw |- notypeclasses refine (tac_wp_pure_wp_later_credit_no_later k e pw _ _ _ _ _ _))
      (Ltac1.of_constr k) (Ltac1.of_constr e) (Ltac1.of_constr pure_wp) >
      [ltac1:(try done)| ltac1:(simpl fill)].

Ltac2 wp_pure_lc () :=
  wp_unhide_body ();
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ (Val _) _) ] => ltac1:(iApply wp_value)
  | [ |- envs_entails _ (wp _ _ ?e _) ] =>
      wp_walk_unwrap (fun () => walk_expr e wp_pure_lc_visit)
        "wp_pure: could not find a head subexpression with a known next step"
  | [ |-  _ ] => Control.backtrack_tactic_failure "wp_pure: current proof is not a WP"
  end.
Tactic Notation "wp_pure" := ltac2:(Control.enter wp_pure).
Tactic Notation "wp_pure_lc" constr(H) := ltac2:(Control.enter wp_pure_lc); last iIntros H.
Tactic Notation "wp_pures" := repeat (wp_pure; []).

Ltac2 wp_call_visit e k :=
  orelse (fun () => Std.unify e '(App (rec: _ _ := _)%V _))
    (fun _ => Control.zero Walk_expr_more);
  if wp_envs_has_later () then
    eapply (tac_wp_rec $k) >
      [ltac1:(tc_solve) | ltac1:(tc_solve)|
        ltac1:(reduction.pm_prettify; simpl subst'; simpl fill)]
  else
    eapply (tac_wp_rec_no_later $k) >
      [ltac1:(tc_solve) | ltac1:(simpl subst'; simpl fill)].

Ltac2 wp_call () :=
  (* XXX: this is when `zero_val`s tend to show up (unfolding the body of a
     function), so try rewriting to use IntoValTyped's default. *)
  wp_unhide_body ();
  lazy_match! goal with
  | [ |- envs_entails _ (wp _  _ ?e _) ] =>
      wp_walk_unwrap (fun () => walk_expr e wp_call_visit)
        "wp_call: could not find a function call expression at the head"
      (* try (rewrite <- !default_val_eq_zero_val) *)
  | [ |-  _ ] => Control.backtrack_tactic_failure "wp_call: current proof is not a WP"
  end.
Tactic Notation "wp_call" := ltac2:(Control.enter wp_call); iIntros "_"; wp_pures.
Tactic Notation "wp_call_lc" constr(H) := ltac2:(Control.enter wp_call); iIntros H; wp_pures.

(* helper to prove PureWp for simple cases where we know what the final
evaluation result is *)
Ltac pure_wp_start :=
  apply pure_wp_val; intros ????;
  iIntros "HΦ";
  try (wp_call_lc "Hlc"; try iSpecialize ("HΦ" with "[$Hlc]"));
  try (wp_pure_lc "Hlc"; try iSpecialize ("HΦ" with "[$Hlc]"));
  wp_pures.

Ltac2 wp_bind_filter (filter_tac : constr -> unit) : constr :=
  wp_unhide_body ();
  lazy_match! goal with
  | [ |- envs_entails _ (wp _  _ ?e _) ] =>
      orelse (fun () => filter_tac e; e) (* if the top-level matches, don't walk down the expr at all. *)
        (fun _ => walk_expr e (fun e' k =>
                              orelse (fun () => filter_tac e')
                                (fun _ => Control.zero Walk_expr_more);
                              eapply (tac_wp_bind $k $e') >
                                [simpl; reflexivity|ltac1:(reduction.pm_prettify)]; e'))
  | [ |- _] => Control.zero (Tactic_failure (Some (fprintf "wp_bind: not a WP goal")))
  end.

Tactic Notation "wp_bind" open_constr(e) :=
  let f := ltac2:(e |-
                    let e := Ltac1.to_constr e in
                    let e := Option.get e in
                    orelse
                      (fun () => let _ := wp_bind_filter (Std.unify e) in ())
                      (fun _ => Control.backtrack_tactic_failure "wp_bind: could not find pattern")
                 ) in
  f e.


Ltac2 expr_is_unknown e : bool :=
  lazy_match! e with
  | fill _ _ => false
  | App _ _                => false
  | If _ _ _ => false
  | Pair _ _ => false
  | Pair _ _ => false
  | Fst _ => false
  | Snd _ => false
  | Primitive2 _ _ _ => false
  | Primitive1 _ _ => false
  | @ExternalOp _ _ _ => false
  | ResolveProph _ _ => false
  | ResolveProph _ _ => false
  | _ => true
  end.

(** [wp_bind_next] binds the next redex, leaving the evaluation context [K]
    as a let-bound function [__wp_ctx := λ e, fill K e] rather than inlining
    it into the postcondition, so that the [iApply] and everything else
    [wp_apply] runs afterwards works on a small goal; see the section on
    hiding above. [wp_apply] unhides at the end. *)
Ltac2 wp_bind_next () : unit :=
  wp_unhide_body ();
  lazy_match! goal with
  | [ |- envs_entails _ (wp _  _ ?e _) ] =>
      let bind_ctx := Ref.ref None in
      let is_call_so_far := Ref.ref true in
      match Control.case (
                fun () => walk_expr e
                         (fun e k => lazy_match! e with
                                  | App _ (Val _) => (if (Ref.get is_call_so_far) then ()
                                                     else Ref.set bind_ctx (Some (e,k)));
                                                    Ref.set is_call_so_far true
                                  | _ => Ref.set bind_ctx (Some (e,k));
                                        Ref.set is_call_so_far false
                                  end;
                                  if expr_is_unknown e then ()
                                  else Control.zero Walk_expr_more)) with
      | Err Walk_expr_not_found => ()
      | Err e => Control.zero e
      | Val _ => ()
      end;
      match (Ref.get bind_ctx) with
      | None => ()
      | Some (e, k) =>
          lazy_match! k with
          | nil => ()
          | _ =>
              let kf := Fresh.in_goal @__wp_ctx in
              Std.pose (Some kf) constr:(λ e, fill $k e);
              let kfc := Control.hyp kf in
              eapply (tac_wp_bind $k $e _ _ _ _ $kfc) > [reflexivity | ()]
          end
      end
  | [ |- _] => Control.zero (Tactic_failure (Some (fprintf "wp_bind_next: not a WP goal")))
  end.

Tactic Notation "wp_bind" := ltac2:(wp_bind_next ()).

Lemma tac_wp_true_elim Σ Δ (P: iProp Σ) :
  envs_entails Δ P ->
  envs_entails Δ (bi_wand (bi_pure True) P).
Proof. rewrite envs_entails_unseal=> ->. iIntros "$ _ //". Qed.

Lemma tac_wp_true Σ (Δ: envs (iPropI Σ)) :
  envs_entails Δ (bi_pure True).
Proof. done. Qed.

Ltac2 solve_bi_true () :=
  lazy_match! goal with
  | [ |- envs_entails _ (bi_pure True) ] => apply tac_wp_true
  | [ |- envs_entails _ (bi_wand (bi_pure True) _) ] => apply tac_wp_true_elim
  end.

(* This unshelves and calls tc_solve because the heuristic followed by
   shelve_unifiable and `notypeclasses refine` to decide what to put on the
   shelf is imperfect. shelve_unifiable will leave goals for EqDecision and
   Countable on the shelf when they arise from a `gmap` if the gmap is mentioned
   in the main WP goal. But, it may never actually get unified. *)
Tactic Notation "wp_apply_core" open_constr(lem) :=
  ltac2:(Control.enter wp_bind_next);
  unshelve (iApply lem; try iNext; try ltac2:(Control.enter solve_bi_true));
  try tc_solve; shelve_unifiable.

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem; wp_unhide_body.

Create HintDb cleanup_bool_decide_db.
Global Hint Rewrite bool_decide_True bool_decide_False : cleanup_bool_decide_db.

Ltac cleanup_bool_decide :=
  autorewrite with cleanup_bool_decide_db.

(* TODO: this is a very basic implementation that would benefit from
post-processing. This is because bool_decide can come with some complications
that should be simplified, like negb around bool_decide or equality of values
inside the bool_decide. *)
Ltac wp_if_destruct :=
  lazymatch goal with
  | |- environments.envs_entails _ ?g =>
      match g with
      | context[bool_decide ?b] =>
          destruct (bool_decide_reflect b); subst;
          wp_pures;
          cleanup_bool_decide
      end
  end.
