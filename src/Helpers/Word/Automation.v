From Ltac2 Require Import Ltac2.
From stdpp Require Import prelude.
From iris.proofmode Require Import proofmode.
From Coq Require Import ssreflect.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers.
From Perennial.Helpers.Word Require Export ZifyWord.  (* [Add Zify] is import-scoped *)
Set Default Proof Mode "Classic".

(** User's guide to the [word] tactic.

    The [word] tactic tries to solve goals related to [w64, w32, w16, w8]
  arithmetic reasoning; if it can't fully solve it, it leaves the proof state
  unchanged. [word] is good at solving "linear word arithmetic": expressions
  that are other expressions multiplied by constants or the addition of other
  expressions together along with (in)equalities. E.g.  [word.mul (W32 4)
  (word.add x y)] is a "linear" expression.

    To unfold a constant, use the [word] HintDb.
  For normal constants, do [Hint Unfold foo : word].
  For sealed constants, do [Hint Rewrite foo_unseal : word] and
  [Hint Unfold foo_def : word].

    [word] is likely to fail at handling non-linear expressions, e.g. [word.mul
  x y] where [x] and [y] are both non-constants. In some proofs, it is possible
  to handle non-linear reasoning first (e.g. by removing a common factor on both
  sides of an equality) and then successfully use [word] to finish the proof.
  [word] is also likely to fail at handling bitwise operations like [word.and],
  [word.or], etc.

  These word operations are entirely unsupported:
    [eqb ltu lts mulhss mulhsu mulhuu eqb ltu lts srs divs mods].
 *)


(** Developer's guide to the [word] tactic.

    [word] has a fast path and a fallback, chosen by [solve_unsafe_dispatch].
  The fast path unfolds [w64]/[W64] and friends, then lets [zify] translate the goal to [Z]
  in one pass using the instances in ZifyWord.v (which cover [uint.Z],
  [sint.Z], [word.of_Z], [add], [sub], [mul], [opp], the bitwise operations
  and word equality, for the four concrete widths), and calls [lia]. A word
  operation [zify] does not know -- a shift, a division, a modulus, a power
  with a non-numeral exponent, any operation on a word of generic width, or
  a word operation inside a boolean equation -- sends the goal to the fallback
  ([solve_unsafe_rewrite]), which is the older rewriting pipeline described
  below; the choice is made up front, by a syntactic scan of the context. A
  word term under an opaque constructor or function (say [NotLocked (W32 0) =
  NotLocked r]) is left alone by both paths, as it always was. The fallback is
  also what [word with tac] and [normalize] use.

    The fallback rewrites everything it can to involve arithmetic
  in [Z] (as opposed to operations on [word]), then it invokes [lia]. In more detail,
  the steps it takes are:
  - Unfold types like [w64] to expose the underlying [word.rep ...] type.
    The remaining steps work with arbitrary [word] types, rather than
    hard-coding [w64], [w32], etc.
  - Eliminate [word.signed] and [@eq (word.rep) a b]. The [Z] value [word.signed
    x] is rewritten into [word.swrap (word.unsigned x)]. [@eq (word.rep) a b] is
    replaced with the equivalent proposition [@eq Z (uint.Z a) (uint.Z b)].
  - Eliminate all word ops. This involves rewriting by the laws in [word.ok]
    with some alterations. Altered forms of the bit shifting laws are used in
    which [Z.shiftl] and [Z.shiftr] are replaced with multiplication/division by
    the appropriate power of 2.
  - Evaluate Z constants.
  - zify; Z.div_mod_to_equations.
  - lia.
 *)

Module word.

Import Interface.word.
Section lemmas.
(* Lemmas used in the word tactic tactics. *)
Local Lemma decision_assume_opposite `{!Decision P} : (¬ P → False) → P.
Proof. by destruct (decide P). Qed.

Local Lemma word_eq_iff_Z_eq {width} {word : word width} {word_ok : ok word} (x y : word):
  x = y ↔ unsigned x = unsigned y.
Proof. split; first by intros ->. apply inj. apply _. Qed.

Local Lemma unsigned_slu' {width} {word : word width} {word_ok : word.ok word}
  (x y : word) :
  Z.lt (unsigned y) width -> unsigned (slu x y) = wrap ((unsigned x) * (2^(unsigned y))).
Proof.
  intros. rewrite unsigned_slu //. pose proof (word.unsigned_range y) as [??].
  rewrite Z.shiftl_mul_pow2 //.
Qed.

Local Lemma unsigned_sru' {width} {word : word width} {word_ok : word.ok word}
  (x y : word) :
  Z.lt (unsigned y) width -> unsigned (sru x y) = ((unsigned x) / (2^(unsigned y))).
Proof.
  pose proof (word.unsigned_range y) as [??].
  pose proof (word.unsigned_range x) as [??].
  intros. rewrite unsigned_sru //. rewrite Z.shiftr_div_pow2 //. rewrite wrap_small //.
  Z.div_mod_to_equations. nia.
Qed.

(* variant of word.signed_divs that produces Z.div rather than Z.quot (which
differ only in their handling of negative numbers) *)
#[local]
Lemma word_signed_divs_nowrap_pos {width : Z} {word : Interface.word width} {word_ok : word.ok word} :
  ∀ x y : word,
  0 < sint.Z y
  ∧ 0 ≤ sint.Z x
  → sint.Z (divs x y) = sint.Z x `div` sint.Z y.
Proof.
  intros.
  rewrite word.signed_divs_nowrap; intuition.
  - rewrite Z.quot_div_nonneg; lia.
  - lia.
  - lia.
Qed.

(* word.signed_divs_nowrap with one side goal *)
#[local]
Lemma word_signed_divs_nowrap_side_goal {width : Z} {word : Interface.word width} {word_ok : word.ok word} :
  ∀ x y : word,
  sint.Z y ≠ 0
  ∧ (sint.Z x ≠ - 2 ^ (width - 1) ∨ sint.Z y ≠ -1)
  → sint.Z (divs x y) = sint.Z x `quot` sint.Z y.
Proof.
  intros.
  rewrite word.signed_divs_nowrap; intuition.
Qed.

End lemmas.

Import Printf.

Ltac2 verbose_logger m := printf "word: %a" (fun () () => m) ().

(* Normalize the proof state so the goal is [False] and everything relevant is in
   the hypotheses. *)
Ltac2 handle_goal logger :=
  lazy_match! goal with
  | [ |- False ] => ()
  | [ |- _ ] => first [
          apply decision_assume_opposite; intros | (* if decidable, assume the opposite; *)
          logger (fprintf "eliminating goal and trying to prove false instead");
          apply False_ind
        ]
  end.

Create HintDb word.

Ltac2 unfold_w_whatever () :=
  (* unlike autounfold, autorewrite fails if empty DB, so wrap in [try]. *)
  (* executing one hint may expose terms that another hint can act on. *)
  ltac1:(repeat (progress (try autorewrite with word in * ; autounfold with word in * )));
  unfold W64, W32, W16, W8, w64, w32, w16, w8 in *.

(* Runs [t] and panics unrecoverably if it throws an exception. *)
Ltac2 handle_unsafe t :=
  match Control.case t with
  | Val (v, _) => v
  | Err (e) => Control.throw e (* TODO: wrap with a better error *)
  end.

Ltac2 normalize_to_word_unsigned () :=
  (* eliminate sint.Z *)
  handle_unsafe (fun () => rewrite -> ?word.signed_eq_swrap_unsigned in * );
  (* eliminate any (eq (word.)*)
  handle_unsafe (fun () => rewrite -> ?word_eq_iff_Z_eq in * ).

(* Notation to more easily write [fun () => open_constr:(t)]. Thunks are used in
   rewrite laws because there are evars in the word lemmas that only get
   instantiated when a rewrite is successful (evars such as the particular
   [width] to instantiate a law with). *)
Local Ltac2 Notation "delayed:(" t(thunk(open_constr)) ")" := t.

Local Ltac2 Notation "delayed:[" ts(list1(thunk(open_constr))) "]" := ts.

(* TODO: check for these and throw an error if found. *)
Ltac2 unsupported_ops () : (unit -> constr) list :=
  delayed:[eqb ltu lts mulhss mulhsu mulhuu eqb ltu lts srs].

(* These equalities have no sideconditions *)
Ltac2 word_op_laws_without_side_goal () : (unit -> constr) list :=
  delayed:[unsigned_add unsigned_sub unsigned_opp unsigned_or
             unsigned_and unsigned_xor unsigned_not unsigned_ndn unsigned_mul].
    (* 'signed_mulhss; 'signed_mulhsu; 'unsigned_mulhuu; 'unsigned_eqb; *)
    (* 'unsigned_ltu; 'signed_lts *)

(* These equalities have 1 sidegoal, and the string is a description of what
   that sidegoal must prove. The string is used in error messages. *)
Ltac2 word_op_laws_with_side_goals () : ((unit -> constr) * string) list := [
    (delayed:(unsigned_slu'), "slu: the shift amount must be less than width");
    (delayed:(unsigned_sru'), "sru: the shift amount must be less than width");
    (* signed_srs *)
    (delayed:(word.unsigned_divu_nowrap), "divu: the divisor must be non-zero");
    (delayed:(word_signed_divs_nowrap_side_goal), "divs: the divisor must be non-zero and result must not overflow");
    (delayed:(word.unsigned_modu_nowrap), "modu: the modulus must be non-zero");
    (delayed:(word.signed_mods_nowrap), "mods: the modulus must be non-zero")
  ].

Ltac2 mutable solve_unsafe () := ().

Ltac2 Type exn ::= [Word_side_goal_failed (string, exn)].
Ltac2 Type exn ::= [Word_side_goal_not_expected (constr)].

(* safe *)
Ltac2 solve_side_goal logger (err : string) (parent_hyp : ident) :=
  logger (fprintf "side goal: begin (%s) on %t" err (Control.goal ()));
  let parent_expr := Constr.type (Control.hyp parent_hyp) in
  Std.clear [parent_hyp];
  orelse solve_unsafe
    (fun ex =>
       let m := (fprintf "side goal failed: %s from expression: %a %t" err (fun () () => Message.force_new_line) ()
                   parent_expr) in
       Control.throw (Word_side_goal_failed (Message.to_string m) ex));
  Control.enter
    (fun () =>
       Control.throw (Tactic_failure (Some (Message.of_string "fatal solve_side_goal: expected [solve_word] to succeed or throw an exception")))
    ).

(* safe, should not throw exceptions. *)
Ltac2 try_rewrite_anywhere logger dlaw side_goal_solver : bool :=
  let make_rw law := { Std.rew_orient := Some Std.LTR;
                       Std.rew_repeat := Std.RepeatPlus;
                       Std.rew_equatn := (fun () => (law, Std.NoBindings)) } in
  let make_cl h := Some { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
                          Std.on_concl := Std.NoOccurrences } in
  let rec loop hyps :=
    (match hyps with
     | [] => false
     | (h, _, _) :: hyps =>
         orelse
           (fun () =>
              let law := dlaw () in
              logger (fprintf "trying rewrite %t in %I" law h);
              rewrite0 false [make_rw law] (make_cl h) (Some (fun () => side_goal_solver h));
              if (Int.equal (Control.numgoals ()) 1) then ()
              else Control.throw (Tactic_failure (Some (Message.of_string "word fatal: rewrite failed")));
              logger (fprintf "succeeded word law %t in hypothesis %I" law h);
              true)
           (fun _ => loop hyps) (* [rewrite0] didn't find anything to rewrite *)
     end) in
  loop (Control.hyps ()).

Ltac2 no_side_condition logger h :=
  logger (fprintf "fatal: unexpected side condition in %I" h);
  Control.throw (Word_side_goal_not_expected (Control.goal ()));
  ().

(** All terms of type [word.rep _] that are either fed into [uint.Z] or fed into
    a [word] operation, which is eventually fed into [uint.Z], are called
    "relevant".

   Postcondition: in all "relevant" terms: all sub-terms of type [word.rep _]
   are directly wrapped in a [uint.Z]. In other words, there are no more [word]
   operations, only [word.rep] values that cannot be broken down any further.

   An example of "irrelevant" terms are [word.rep]s showing up underneath a
   word-opaque term. E.g. if [x y : w64] and [f : w64 → w64] is some function
   that's not a standard word op, then [uint.Z [word.add (f x) y]] will turn
   into [wrap (Z.add uint.Z (f x) (uint.Z y)]], which has the [word.rep] x that
   is not getting passed into [uint.Z]. In this case, [f x] is treated as opaque
   and unrelated to [x]. Any relationships e.g. beween [f x] and [x] should be
   proven and added to the context before running [word].
 *)
Ltac2 eliminate_word_ops logger :=
  let try_rewrite_anywhere := try_rewrite_anywhere logger in
  let no_side_condition := no_side_condition logger in
  let rec loop f := if (f ()) then loop f else () in

  (* Eliminate word equality, which should following rewrites should never reintroduce. *)
  loop (fun () => try_rewrite_anywhere (delayed:(word_eq_iff_Z_eq)) no_side_condition);

  (* Eliminate [signed] in favor of [swrap ∘ unsigned]. *)
  loop (fun () => try_rewrite_anywhere (delayed:(word.signed_eq_swrap_unsigned)) no_side_condition);

  (* At this point, every relevant term of type [rep] is wrapped in either
     a word op or [unsigned]. *)
  (* Eliminate word ops (add, mul, etc.). *)
  let rws := List.map (fun law () => try_rewrite_anywhere law no_side_condition)
                (word_op_laws_without_side_goal ()) in
  let rws' := List.map (fun y () =>
                           let (law, err_str) := y in
                           try_rewrite_anywhere law (solve_side_goal logger err_str)
                 )
                (word_op_laws_with_side_goals ()) in
  let rws := List.append rws' rws in
  loop (fun () => List.exist (fun f => f ()) rws);

  (* At this point, every relevant term of type [rep] is wrapped in
     [unsigned]. *)
  (* Eliminate [of_Z]. *)
  loop (fun () => try_rewrite_anywhere (delayed:(unsigned_of_Z)) no_side_condition);
    (* NOTE: don't want to rewrite by [of_Z_unsigned], since it results in a term
       wrapped by [unsigned] becoming no longer wrapped. *)
  ().

Ltac2 unfold_word_wrap () :=
  unfold wrap, swrap in *.

Ltac2 noop_logger _ := ().

Ltac2 eval_Z_constants_in_hyp (h : ident) : unit :=
  (* FIXME: This is a little inefficient: it repeatedly calls Std.eval_vm bottom-up. *)
  let rec try_eval_aux (e : constr) : (bool * constr) :=
    let (should_eval, e) :=
      lazy_match! e with
      | Zpos _ => (true, e)
      | Zneg _ => (true, e)
      | ?op ?a ?b =>
          let ((sa, a), (sb, b)) := (try_eval_aux a, try_eval_aux b) in
          let should_eval :=
            lazy_match! op with
            | Z.add => true | Z.sub => true
            | Z.mul => true | Z.div => true
            | Z.pow => true | Z.modulo => true
            | _ => false
            end
          in (Bool.and should_eval (Bool.and sa sb), '($op $a $b))
      | ?op ?b =>
          let (sb, b) := (try_eval_aux b) in
          let should_eval :=
            lazy_match! op with
            | Z.abs => true | Z.opp => true | _ => false
            end
          in (Bool.and should_eval sb, '($op $b))
      | _ => (false, e)
      end
    in
    if should_eval then (true, Std.eval_vm None e) else (false, e)
  in

  let try_eval () :=
    let e := Constr.type (Control.hyp h) in
    let (_, e') := try_eval_aux e in
    Std.change None (fun _ => e')
      { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)]; Std.on_concl := Std.NoOccurrences }
  in
  repeat0 (fun () => Control.progress try_eval).

Ltac2 simplify_Z_constants () :=
  List.iter (fun h => let (h, _, _) := h in eval_Z_constants_in_hyp h) (Control.hyps ()).

Ltac2 set_all () :=
  List.iter
    (fun h =>
       let (h, _, _) := h in
       repeat (
           lazy_match! Constr.type (Control.hyp h) with
           | context[Zpos ?x] => set (Zpos $x) in *
           | context[Zneg ?x] => set (Zneg $x) in *
           end
    )) (Control.hyps ()).

Ltac2 subst_all () :=
  List.iter (fun h => let (h, _, _) := h in orelse (fun () => Std.subst [h]) (fun _ => ()))
            (Control.hyps ()).

(* XXX: using ltac1 because constrs can't be directly used in patterns.
   Example workaround to do it in ltac2: https://github.com/rocq-prover/rocq/issues/13962
 *)
Ltac2 add_range_facts () :=
  ltac1:(
           repeat match goal with
             | [ H: context[uint.Z ?x] |- _ ] =>
                 lazymatch goal with
                 | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
                 | _ => pose proof (word.unsigned_range x)
                 end
           end
  ).

(* Does some subterm of [c] satisfy [p]? *)
Ltac2 rec constr_exists (p : constr -> bool) (c : constr) : bool :=
  if p c then true
  else
    let found := Ref.ref false in
    Constr.Unsafe.iter
      (fun c' => if Ref.get found then () else Ref.set found (constr_exists p c')) c;
    Ref.get found.

Ltac2 is_Z_numeral (c : constr) : bool :=
  lazy_match! c with
  | Z0 => true
  | Zpos _ => true
  | Zneg _ => true
  | _ => false
  end.


(* Evaluating closed constants, before the dispatch (so before either path). [uint.Z (W64 48)], [2^(64-1)],
   [uint.Z (word.add (W64 1) (W64 2))] are closed terms; [vm_compute]
   evaluates them (the word instances are [Opaque] to [unfold] and friends,
   but not to [vm_compute]), and the goal is easier with the numeral in their
   place: [lia] does not evaluate a power with a non-numeral exponent, and
   [zify] never enters a boolean equation, so a word term there gets no
   facts unless it is already a number. Every maximal closed subterm headed
   by [unsigned], [signed] or a [Z] operator is replaced by its value; the
   replacement is proved by [vm_compute; reflexivity].

   The guard is syntactic and runs before any evaluation: a term is evaluated
   only if it is built from numerals, [Z] operators, the word operators and
   the four concrete instances, nothing else. "No free variables" is not
   enough: a term with an axiom or a Qed-opaque constant in it (a [sealed]
   definition, say) is stuck, [vm_compute] grinds through the instance's
   range proofs around it -- minutes and gigabytes, observed -- and what
   comes out would put the instance's internals ([Naive.mk] and friends,
   which it is meant to hide) into the goal. [Z.of_nat] is deliberately not
   an operator here: a closed [Z.of_nat (2^64)%nat] would have [vm_compute]
   build a unary number. The value is also checked to be a numeral, as a
   second line of defence. *)
Ltac2 is_computable_atom (c : constr) : bool :=
  List.exist (fun k => Constr.equal c k)
    ['w64_word_instance; 'w32_word_instance; 'w16_word_instance; 'w8_word_instance;
     'W64; 'W32; 'W16; 'W8;
     '(@unsigned); '(@signed); '(@of_Z); '(@Interface.word.add); '(@Interface.word.sub);
     '(@Interface.word.mul); '(@Interface.word.opp); '(@Interface.word.or);
     '(@Interface.word.and); '(@Interface.word.xor); '(@Interface.word.not);
     '(@Interface.word.ndn);
     '(@Z.add); '(@Z.sub); '(@Z.mul); '(@Z.opp); '(@Z.pow); '(@Z.modulo); '(@Z.div);
     '(@Z.quot); '(@Z.rem); '(@Z.max); '(@Z.min); '(@Z.abs)].

(* Built from the atoms above, constructors (numerals) and nothing else:
   [vm_compute] on such a term terminates quickly and yields a numeral. *)
Ltac2 rec is_computable (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h args =>
      Bool.and (is_computable h) (Array.for_all is_computable args)
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.Constant _ _ => is_computable_atom c
  | _ => false
  end.

Ltac2 is_computable_head (h : constr) : bool :=
  List.exist (fun k => Constr.equal h k)
    ['(@unsigned); '(@signed); '(@Z.add); '(@Z.sub); '(@Z.mul); '(@Z.opp);
     '(@Z.pow); '(@Z.modulo); '(@Z.div); '(@Z.quot); '(@Z.rem);
     '(@Z.max); '(@Z.min); '(@Z.abs)].

(* A maximal computable, non-numeral subterm of [c] with a computable head, if any.
   [constr_exists] tests a term before its subterms, which gives maximality. *)
Ltac2 find_computable (c : constr) : constr option :=
  let found := Ref.ref None in
  let _ := constr_exists (fun sub =>
    match Constr.Unsafe.kind sub with
    | Constr.Unsafe.App h _ =>
        if Bool.and (is_computable_head h)
             (Bool.and (Bool.neg (is_Z_numeral sub)) (is_computable sub))
        then (Ref.set found (Some sub); true)
        else false
    | _ => false
    end) c in
  Ref.get found.

Ltac2 rec compute_closed_constants_in (h : ident) : unit :=
  match find_computable (Constr.type (Control.hyp h)) with
  | None => ()
  | Some occ =>
      let v := Std.eval_vm None occ in
      if Bool.neg (is_Z_numeral v) then ()   (* stuck: leave it alone *)
      else (
        ltac1:(occ v h |- replace occ with v in h by (vm_compute; reflexivity))
          (Ltac1.of_constr occ) (Ltac1.of_constr v) (Ltac1.of_ident h);
        compute_closed_constants_in h)
  end.

Ltac2 compute_closed_constants () : unit :=
  List.iter (fun h => let (h, _, _) := h in compute_closed_constants_in h) (Control.hyps ()).

(* [normalize] is the old pipeline, unchanged: proofs call it directly and
   then work on the exact shapes it produces ([sync_proof/waitgroup.v] does
   [set (x1 := 2 ^ (32 `mod` 2 ^ 64)) in *] after it), so nothing may be
   added here. [compute_closed_constants] runs in [solve_unsafe_dispatch]
   before either branch is chosen, which also covers the fallback when it is
   reached through [word]. *)
Ltac2 normalize tac :=
  handle_goal noop_logger;
  unfold_w_whatever ();
  eliminate_word_ops noop_logger;
  add_range_facts ();
  tac ();
  unfold_word_wrap ();
  simplify_Z_constants () (* FIXME: should probably simplify Z constants after zify *)
.

(** The rewriting pipeline: normalize by rewriting, then [lia]. This is the
    fallback branch of [solve_unsafe_dispatch] below, and what [solve_unsafe_with] uses. *)
Ltac2 solve_unsafe_rewrite () :=
  normalize (fun () => ());
  set_all ();
  ltac1:(zify; Z.div_mod_to_equations);
  subst_all ();
  ltac1:(lia).

(** Syntactic checks on the hypotheses (after [handle_goal] the goal is
    [False]), used to pick the path. Each is a single scan of the context. *)

(* Operations whose elimination has a side condition; ZifyWord.v has no
   instance for them. *)
Ltac2 has_side_goal_ops () : bool :=
  lazy_match! goal with
  | [ _ : context [ slu _ _ ] |- _ ] => true
  | [ _ : context [ sru _ _ ] |- _ ] => true
  | [ _ : context [ srs _ _ ] |- _ ] => true
  | [ _ : context [ divu _ _ ] |- _ ] => true
  | [ _ : context [ divs _ _ ] |- _ ] => true
  | [ _ : context [ modu _ _ ] |- _ ] => true
  | [ _ : context [ mods _ _ ] |- _ ] => true
  | [ |- _ ] => false
  end.

(* Divisions [zify] leaves as atoms; they need [Z.div_mod_to_equations]. The
   wraps ZifyWord.v itself introduces carry their own equations. *)
Ltac2 has_div_mod () : bool :=
  lazy_match! goal with
  | [ _ : context [ Z.modulo _ _ ] |- _ ] => true
  | [ _ : context [ Z.div _ _ ] |- _ ] => true
  | [ _ : context [ Z.quot _ _ ] |- _ ] => true
  | [ _ : context [ Z.rem _ _ ] |- _ ] => true
  | [ _ : context [ Nat.div _ _ ] |- _ ] => true
  | [ _ : context [ Nat.modulo _ _ ] |- _ ] => true
  | [ _ : context [ N.div _ _ ] |- _ ] => true
  | [ _ : context [ N.modulo _ _ ] |- _ ] => true
  | [ _ : context [ wrap _ ] |- _ ] => true
  | [ _ : context [ swrap _ ] |- _ ] => true
  | [ |- _ ] => false
  end.

(* [lia] evaluates [2^32] but not [2^(32-1)] or [2^(uint.Z (W64 48))]: a
   power whose exponent is not a numeral is an opaque atom to it. The
   rewriting pipeline evaluates such exponents ([simplify_Z_constants]), so a
   goal with one goes there. *)
Ltac2 is_nonliteral_pow (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h args =>
      if Bool.and (Constr.equal h '(@Z.pow)) (Int.equal (Array.length args) 2)
      then Bool.neg (is_Z_numeral (Array.get args 1))
      else false
  | _ => false
  end.

Ltac2 has_nonliteral_pow () : bool :=
  List.exist (fun h => let (_, _, t) := h in constr_exists is_nonliteral_pow t)
    (Control.hyps ()).

(* A word whose instance is not one of the four concrete ones (a Section
   variable [word : Interface.word width], say): ZifyWord.v has no instances
   for it, and [zify] would leave its equalities and ranges alone. *)
Ltac2 is_generic_word_type (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h args =>
      if Bool.and (Constr.equal h '(@rep)) (Int.equal (Array.length args) 2) then
        let inst := Array.get args 1 in
        Bool.neg (List.exist (fun k => Constr.equal inst k)
          ['w64_word_instance; 'w32_word_instance; 'w16_word_instance; 'w8_word_instance])
      else false
  | _ => false
  end.

Ltac2 has_generic_word () : bool :=
  List.exist (fun h => let (_, _, t) := h in constr_exists is_generic_word_type t)
    (Control.hyps ()).

(* [zify] does not translate a boolean equation (ZifyBool is not loaded),
   so a word operation inside one, [(uint.Z (word.add x y) <? 200) = true]
   say, would stay an atom without its wrap-around facts. The rewriting
   pipeline rewrites under any context, so such goals go there. *)
Ltac2 is_word_op_term (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ =>
      List.exist (fun k => Constr.equal f k)
        ['(@unsigned); '(@signed); '(@of_Z); '(@Interface.word.add); '(@Interface.word.sub);
         '(@Interface.word.mul); '(@Interface.word.opp); '(@Interface.word.or);
         '(@Interface.word.and); '(@Interface.word.xor); '(@Interface.word.not);
         '(@Interface.word.ndn)]
  | _ => false
  end.

Ltac2 is_bool_eq_with_word (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Bool.and (Constr.equal f '(@eq)) (Int.equal (Array.length args) 3) then
        if Constr.equal (Array.get args 0) 'bool then
          Bool.or (constr_exists is_word_op_term (Array.get args 1))
                  (constr_exists is_word_op_term (Array.get args 2))
        else false
      else false
  | _ => false
  end.

Ltac2 has_bool_eq_with_word () : bool :=
  List.exist (fun h => let (_, _, t) := h in constr_exists is_bool_eq_with_word t)
    (Control.hyps ()).

(** The top-level solver: a little normalization, then the syntactic checks
    above pick the branch -- [zify; lia], the fast path, or the rewriting
    pipeline. Everything before the branch is a constant number of cheap
    passes over the context; [zify] is one OCaml traversal. *)
Ltac2 solve_unsafe_dispatch () :=
  handle_goal noop_logger;
  unfold_w_whatever ();
  let divmod := has_div_mod () in
  (* [swrap] unfolds to a [2^(width-1)], so unfold before looking for
     non-numeral exponents; and evaluate closed constants first, so that a
     [2^uint.Z (W64 48)] or a [2^(64-1)] becomes a numeral power. *)
  unfold_word_wrap ();
  compute_closed_constants ();
  if Bool.or (has_side_goal_ops ())
       (Bool.or (has_generic_word ()) (Bool.or (has_nonliteral_pow ()) (has_bool_eq_with_word ())))
  then solve_unsafe_rewrite ()
  else
    (* [set_all]/[subst_all] as in the rewriting pipeline: big literals are
       abstracted while [zify] and [Z.div_mod_to_equations] run and put back
       for [lia]. Without this, a goal with a few nested [mod]s by [2^32] and
       [2^64] ([sync_proof/waitgroup.v]'s [enc_get_wait]) does not finish
       -- 50 minutes and 34 GB, observed -- and finishes in 30 ms with it. *)
    set_all ();
    ltac1:(zify);
    (if divmod then ltac1:(Z.div_mod_to_equations) else ());
    subst_all ();
    ltac1:(lia).

Module Export SetSolveUnsafe.
Ltac2 Set solve_unsafe as old := (fun () => solve_unsafe_dispatch ()).
End SetSolveUnsafe.

Ltac2 solve_unsafe_with tac :=
  normalize tac;
  set_all ();
  ltac1:(zify; Z.div_mod_to_equations);
  subst_all ();
  ltac1:(lia).
(* Add a warning/error for nonlinear arithmetic? Sometimes it's hard to
   notice. *)

Local Lemma test_sum_overflow_check (x y: u64) :
  uint.Z (word.add x y) < uint.Z x <-> uint.Z x + uint.Z y >= 2^64.
Proof.
  Time ltac2:(word.solve_unsafe ()).
Qed.

Local Lemma test_from_wg (delta' : w32) (delta : w64) :
  delta' = (W32 (sint.Z delta)) →
  word.slu delta (W64 32) = word.slu (W64 (sint.Z delta')) (W64 32).
Proof.
  intros. ltac2:(solve_unsafe ()).
Qed.

End word.

Export word.SetSolveUnsafe.

Tactic Notation "word" :=
  try iPureIntro; ltac2:(Control.enter word.solve_unsafe).

Tactic Notation "word" "with" tactic(t) :=
  try iPureIntro;
  let w := ltac2:(t |- Control.enter (fun () => word.solve_unsafe_with (fun () => Ltac1.run t))) in
  w t.

Tactic Notation "nat_cleanup" :=
  rewrite -> ?Nat2Z.id; rewrite -> ?Z2Nat.id by word.

(** Regression tests for the dispatch; each of these once sent a goal
    somewhere [lia] could not follow. *)
Module word_tests.
(* [zify] does not translate a boolean equation, so the [uint.Z (W64 48)]
   inside it has to be evaluated to [48] first. *)
Local Lemma closed_constant_in_bool (i : Z) : ¬ i < 48 → (i <? uint.Z (W64 48)) = false.
Proof. intros. word. Qed.
(* [swrap] unfolds to a [2^(64-1)]: the non-numeral exponent must be seen
   after the unfolding, not before. *)
Local Lemma swrap_exponent (i : w64) :
  0 ≤ Z.rem (sint.Z i) 2 → Z.rem (sint.Z i) 2 < 2 →
  0 ≤ word.swrap (word := w64_word_instance) (Z.rem (sint.Z i) 2) < 2.
Proof. intros. word. Qed.
(* A divisor [sint.Z (W64 2)] must become the numeral [2], or the division
   is non-linear to [lia]. *)
Local Lemma signed_divisor (x : w64) :
  sint.Z x / sint.Z (W64 2) = sint.Z x / 2 ∧ sint.Z (W64 (-1)) = -1.
Proof. word. Qed.
(* A word operation inside a boolean equation: [zify] does not go there,
   the rewriting pipeline does. *)
Local Lemma word_op_in_bool_eq (x y : w64) :
  uint.Z x < 100 → uint.Z y < 100 → (uint.Z (word.add x y) <? 200) = true.
Proof. intros. word. Qed.
(* Closed compound terms: a divisor built from words, and a [2^(64-1)]. *)
Local Lemma closed_compound_constants (x : w64) :
  uint.Z x / uint.Z (word.add (W64 1) (W64 1)) = uint.Z x / 2 ∧ uint.Z x < 2 ^ (64 - 1) + 2 ^ 63.
Proof. word. Qed.
(* A closed term [vm_compute] cannot finish -- here a Qed-opaque constant, as
   a [sealed] definition is -- must be left exactly as it was, not replaced
   by a partial evaluation exposing the word instance's internals. *)
Local Lemma opaque_five : Z. Proof. exact 5. Qed.
Local Lemma stuck_term_left_alone (x : w64) (H : uint.Z x = uint.Z (W64 opaque_five)) : True.
Proof.
  ltac2:(word.compute_closed_constants ()).
  lazymatch type of H with uint.Z x = uint.Z (W64 opaque_five) => exact I end.
Qed.
(* Nested [mod]s by big literals ([waitgroup.v]'s [enc_get_wait], after its
   own normalization): [lia] needs the literals abstracted while the
   division equations are generated, or it does not terminate. *)
Local Lemma nested_mods (a b : Z) :
  0 ≤ a < 4294967296 → 0 ≤ b < 2147483648 →
  ((((a `mod` 18446744073709551616 * 4294967296) `mod` 18446744073709551616
     + b `mod` 18446744073709551616) `mod` 18446744073709551616)
    `mod` 2147483648) `mod` 4294967296 = b.
Proof. intros. word. Qed.
Local Lemma pow_of_word_exponent (x : w64) :
  uint.Z x < 2 ^ uint.Z (W64 48) → uint.Z x < 281474976710656.
Proof. intros. word. Qed.
Local Lemma generic_width `{word : Interface.word width} `{!word.ok word} (w0 w1 : word) :
  Z.to_nat (uint.Z w0) = Z.to_nat (uint.Z w1) → w0 = w1.
Proof. intros. word. Qed.
End word_tests.
