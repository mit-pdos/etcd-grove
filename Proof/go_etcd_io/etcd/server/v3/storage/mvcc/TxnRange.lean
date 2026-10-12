/-
What a range read of a transaction takes and answers, beside `rangeOutcome` (`InvStore.lean`):
its context, and the log and revision a transaction kind reads. Lean-first; added for the
server's txn package (`notes/decisions.md`, "The server's txn", unit 1).

**The context** (`rangeCtx todo ctx cd`): a context `isContext ctx cd` (its `Done` channel a
broadcast channel), or (`todo = true`) a context that is never canceled: `context.TODO()`'s value,
a `todoCtx{}` whose `Done()` is `nil` (`wp_todoCtx_Done`), or an `isContext` whose Done
proposition never holds (`neverDone`: its channel is never closed, a receive on it would give
`□ PDone`); `rangeKeys`' `select` on it takes its `default`, and a range read at it never fails
for the context (`todo = true → r ≠ null` in the specs of `rangeKeys` and the `Range`s above it).
The txn package's `getPrevKV` and `applyCompare` read at `context.TODO()`, which Perennial's
`isContext` does not describe; its `executeTxn` (txn unit 3) at the context `Txn` derives from
the apply thread's `context.TODO()` (`traceutil.EnsureTrace`), never canceled either.

**The kind's reads** (`TxnKind.readLog`, `readRev`, `readState`): a read transaction reads its
committed log at its revision; a write transaction the committed log with its pending revision
appended at `writeRev` (`storeTxnWrite.Range`): the state after the pending changes.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode

/-- The log a transaction of this kind reads: a write transaction's has its pending revision
appended. -/
def TxnKind.readLog : TxnKind → Log
  | .read log _ => log
  | .write ilog pend _ _ _ => ilog ++ [pend]

/-- The revision a transaction of this kind reads at (`storeTxnWrite.Range`'s `writeRev`). -/
def TxnKind.readRev : TxnKind → w64
  | .read _ rev => rev
  | .write ilog pend _ _ _ => W64 ((writeRev ilog pend : Nat) : Int)

/-- The revision a transaction of this kind began at (`Rev()`): a read transaction's, a write
transaction's committed log's last. -/
def TxnKind.beginRev : TxnKind → w64
  | .read _ rev => rev
  | .write ilog _ _ _ _ => W64 ((ilog.length : Int) - 1)

/-- The changes a transaction of this kind has pending (`Changes()`): none for a read one. -/
def TxnKind.pend : TxnKind → List Change
  | .read _ _ => []
  | .write _ pend _ _ _ => pend

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `context.TODO()`'s value (the cache's `todoCtxVal`): a `todoCtx{}` as a `Context`. -/
abbrev todoCtxV : GoInterfaceOk :=
  interface.mk context.todoCtx.ty #(zero_val context.todoCtx)

/-- The context `cd` is never canceled: its Done proposition never holds (txn unit 3). -/
def neverDone (cd : context.ContextDesc (IProp GF)) : IProp GF := iprop(□ (cd.PDone -∗ False))

instance neverDone_persistent (cd : context.ContextDesc (IProp GF)) :
    Persistent (neverDone (GF := GF) cd) := by
  unfold neverDone; infer_instance

instance ite_neverDone_persistent (nd : Bool) (cd : context.ContextDesc (IProp GF)) :
    Persistent (if nd then neverDone (GF := GF) cd else iprop(True)) := by
  cases nd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The context of a range read: an `isContext`, or (`todo`) one never canceled:
`context.TODO()`'s, or an `isContext` whose Done proposition never holds. -/
def rangeCtx (todo : Bool) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    IProp GF :=
  if todo then iprop(⌜ctx = todoCtxV⌝ ∨ (context.isContext ctx cd ∗ neverDone cd))
  else context.isContext ctx cd

instance rangeCtx_persistent (todo : Bool) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) : Persistent (rangeCtx (GF := GF) todo ctx cd) := by
  unfold rangeCtx; cases todo <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- `context.TODO()`'s `Done()` is `nil` (Perennial's `wp_background_Done`, for `todoCtx`). -/
theorem wp_todoCtx_Done :
    {{ (True : IProp GF) }}
      (App (Val #(methods context.todoCtx.ty go!"Done" #(zero_val context.todoCtx))) (Val #()))
    {{ RET #chan.nil; True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

/-- What a range read's context's `Done()` returns: `nil` for `context.TODO()`'s, a channel
of the context's `isContextDone` otherwise (never closed if `todo`). -/
def rangeDone (todo : Bool) (cd : context.ContextDesc (IProp GF)) (ch : GoChan) : IProp GF :=
  if todo then
    iprop(⌜ch = chan.nil⌝ ∨ ((∃ γch, context.isContextDone cd ch γch) ∗ neverDone cd))
  else iprop(∃ γch, context.isContextDone cd ch γch)

instance rangeDone_persistent (todo : Bool) (cd : context.ContextDesc (IProp GF)) (ch : GoChan) :
    Persistent (rangeDone (GF := GF) todo cd ch) := by
  unfold rangeDone; cases todo <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- **The context's `Done()`**, for either kind of context. -/
theorem rangeCtx_Done (todo : Bool) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    rangeCtx todo ctx cd ⊢
      {{ True }} (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #()))
      {{ (ch : GoChan), RET #ch; rangeDone todo cd ch }} := by
  unfold rangeCtx rangeDone
  cases todo
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro #Hctx
    imodintro
    iintro %Φ - HΦ
    iNamed Hctx
    iapply HDone
    · itrivial
    inext
    iintro %ch %γch #Hd
    iapply HΦ
    iexists γch
    iexact Hd
  · simp only [↓reduceIte]
    iintro (%Hc | ⟨#Hctx, #Hnd⟩)
    · subst Hc
      imodintro
      iintro %Φ - HΦ
      iapply wp_todoCtx_Done
      · itrivial
      inext
      iintro -
      iapply HΦ
      ileft
      ipureintro; rfl
    · imodintro
      iintro %Φ - HΦ
      iNamed Hctx
      iapply HDone
      · itrivial
      inext
      iintro %ch %γch #Hd
      iapply HΦ
      iright
      isplitl []
      · iexists γch
        iexact Hd
      · iexact Hnd

/-- A nonblocking `select` with one case, on a channel that is either one the case's
`nonblockingAltClausePre` describes, or `nil` (`chan.nilClausePre`: the case never fires): the
default runs with the frame `P` in the second. (`chan.wp_select_nonblocking_alt` with one case
and `chan.wp_select_nonblocking_nil`, in one.) -/
theorem wp_select1_alt_or_nil (c : comm_clause) (P : IProp GF) (dflt : Expr)
    (Φ : val → IProp GF) :
    ⊢ ((P -∗ chan.nonblockingAltClausePre c Φ iprop(P ∗ True)) ∨ chan.nilClausePre c) -∗ P -∗
      (P -∗ True -∗ WP dflt {{ Φ }}) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt) [c])))
        {{ Φ }} := by
  iintro Hc HP Hdef
  icases Hc with (Hc | Hc)
  · iapply chan.wp_select_nonblocking_alt [iprop(True)] P [c] dflt Φ $$ [Hc] HP [Hdef]
    · iapply BigSepL2.bigSepL2_singleton.2
      iexact Hc
    · iintro HP -
      iapply Hdef $$ HP
      itrivial
  · iapply chan.wp_select_nonblocking_nil [c] dflt Φ
    isplit
    · iapply BigAndL.bigAndL_singleton.2
      iright
      iexact Hc
    · iapply Hdef $$ HP
      itrivial

end defs

end mvcc
end EtcdGrove
end Perennial
