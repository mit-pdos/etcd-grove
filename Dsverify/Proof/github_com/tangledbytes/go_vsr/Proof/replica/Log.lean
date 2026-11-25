/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Log.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
The replica's logging calls (`r.logger.Debug/Info/Warn/Error(msg, args...)`).

When every argument is `fmt.ArgsWf` (strings, `uint64`s, `int`s) the call is the `log/slog`
spec's. Some of the replica's calls log other values, which the `log/slog` spec does not allow:
* the `error` a `Send` returned (`"err", err`): the model's handler calls its `Error()` method,
  and `network.Send`'s spec says nothing of the error's dynamic type (HUB-REQUEST 2);
* named integer types (`ReplicaStatus`, `events.EventType`), a `*events.Event` and a
  `[3]uint64`: none has a `String()` or `Error()` method (`replica.noFmt_types`, decided from
  the method sets by `go_type_set`), so the model's `touch` calls nothing on them.
The calls use `replica.wp_logMethod` over `replica.logArg` (either kind).

Port: the lab proved `wp_logMethod` by stepping through its `log/slog` model (`touch`,
`handlerOf`); here the logger methods' specs are the hypotheses of `LibHyps.lean` (in the bundle
`replica.Hyps`), stated at `log.slog.argOk` (the lab's `replica.logArg`, now its definition), so
`wp_logMethod` takes `H : replica.Hyps`. `replica.NoFmtArg` is `log.slog.NoFmtArg`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net



section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

include hG in
/-- The named integer types, `*events.Event` and `[3]uint64` have no `String()`/`Error()`
method (their method sets: `ReplicaStatus`, `events.EventType` and `[3]uint64` have none,
`*events.Event` has `ToWriter`/`FromReader`/`FromDecoder`), decided by `go_type_set` from the
packages' `TypeAssumptions.method_set` facts and the semantics' `NoMethods` (arrays). -/
theorem replica.noFmt_types (t : go.GoType)
    (ht : t = replica.ReplicaStatus.ty ∨ t = events.EventType.ty ∨
      t = go.GoType.PointerType events.Event.ty ∨ t = go.ArrayType 3 go.uint64) (v : val) :
    log.slog.NoFmtArg (interface.mkOk t v) := by
  intro ii hii
  cases hii
  rcases ht with rfl | rfl | rfl | rfl <;> exact ⟨by go_type_set, by go_type_set⟩

/-- An argument the replica logs: `nil`, `fmt.ArgWf`-ok, an error with some message, or a value
without formatting methods (`log.slog.argOk`). -/
abbrev replica.logArg (v : GoInterface) : IProp GF := log.slog.argOk v

/-- An error `Send`/`ToWriter` returned is a log argument (`bufio.errOrNil`, D6/D10). -/
theorem replica.logArg_err (err : GoInterface) : bufio.errOrNil err ⊢ replica.logArg (GF := GF) err := by
  unfold bufio.errOrNil replica.logArg log.slog.argOk
  iintro (%h | ⟨#He, -⟩)
  · ileft; ipureintro; intro ii hii; subst h; cases hii
  · iright; ileft; iexact He

theorem replica.logArg_string (x : GoString) :
    ⊢ replica.logArg (GF := GF) (interface.mkOk go.string #x) := by
  unfold replica.logArg log.slog.argOk
  ileft; ipureintro
  intro ii hii
  exact fmt.ArgsWf.cons_string x [] fmt.ArgsWf.nil ii (by rw [hii]; simp)

theorem replica.logArg_u64 (n : w64) : ⊢ replica.logArg (GF := GF) (interface.mkOk go.uint64 #n) := by
  unfold replica.logArg log.slog.argOk
  ileft; ipureintro
  intro ii hii
  exact fmt.ArgsWf.cons_int _ _ [] (.uint64 n) fmt.ArgsWf.nil ii (by rw [← hii]; simp)

theorem replica.logArg_noFmt (t : go.GoType)
    (ht : t = replica.ReplicaStatus.ty ∨ t = events.EventType.ty ∨
      t = go.GoType.PointerType events.Event.ty ∨ t = go.ArrayType 3 go.uint64) (v : val) :
    ⊢ replica.logArg (GF := GF) (interface.mkOk t v) := by
  unfold replica.logArg log.slog.argOk
  iright; iright; ipureintro; exact replica.noFmt_types (GF := GF) t ht v

/-- A logger method (`Debug`, `Info`, `Warn`, `Error`) on log arguments: the hypotheses. -/
theorem replica.wp_logMethod (H : replica.Hyps (GF := GF) (hG := hG)) (l : Loc)
    (meth msg : GoString) (arg : GoSlice) (xs : List GoInterface)
    (dq : DFrac) (hm : meth = go!"Debug" ∨ meth = go!"Info" ∨ meth = go!"Warn" ∨
      meth = go!"Error") :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ log.slog.isLogger l ∗
        arg ↦*{dq} xs ∗ [∗list] x ∈ xs, replica.logArg x }}
      (App (App (Val (l @!! go.GoType.PointerType log.slog.Logger.ty @!! meth)) (Val #msg))
        (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  rcases hm with rfl | rfl | rfl | rfl
  · exact H.wp_Debug l msg arg xs dq
  · exact H.wp_Info l msg arg xs dq
  · exact H.wp_Warn l msg arg xs dq
  · exact H.wp_Error l msg arg xs dq


end proofs

theorem replica.sint_nat_lit (z : Int) (h0 : 0 ≤ z) (h : z < 2 ^ 63) :
    sint.nat (W64 z) = z.toNat := by word

/-- One log argument: a string, a `uint64`, an error a send returned (its `errOrNil` in the
context), or a value of a method-less type. -/
macro "log_arg" : tactic => `(tactic| first
  | iapply replica.logArg_string
  | iapply replica.logArg_u64
  | (iapply replica.logArg_err; iassumption)
  | (iapply replica.logArg_noFmt; simp))

set_option hygiene false in
/-- The arguments' big separating conjunction of a log call (the slice literal's list). -/
macro "log_args" : tactic => `(tactic| (
  try simp only [Int.reduceAdd]
  simp (disch := decide) only [replica.sint_nat_lit, Int.reduceToNat, List.set]
  repeat (iapply (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).2; isplitl []; log_arg)
  iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro))

set_option hygiene false in
/-- A logging call: build the arguments' slice literal, then the logger method. -/
macro "wp_log" : tactic => `(tactic| (
  try wp_auto
  wp_apply (wp_slice_literal (V := GoInterface))
  isplitr
  · ipureintro; rfl
  iintro %args_sl ⟨Hargs, -⟩
  try wp_auto
  wp_apply (replica.wp_logMethod H _ _ _ _ _ _ (by decide)) $$ [Hargs] as -
  · iframe Hlogger Hargs
    log_args))

set_option hygiene false in
/-- Close a handler whose replica state is unchanged: `HΦ` of `replica.own` with the same
witnesses (the names `iNamed` gave `replica.repInv`'s conjuncts). -/
macro "close_own" : tactic => `(tactic| (
  iapply HΦ
  iexists v
  iframe Hr
  iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
  iFrameNamed
  ipureintro
  exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩))

end Perennial.github_com.tangledbytes.go_vsr.pkg
