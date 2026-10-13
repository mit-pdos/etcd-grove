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

**`context.TODO()` and its derived contexts** (2026-10-12, the apply package, which calls the
txn package at `context.TODO()`): `doneNil ctx`, a context whose `Done()` returns `nil`, is
`TODO()`'s (`doneNil_todo`) and that of every context `context.WithValue` derives from such a
context (its `Done` is its parent's), as `traceutil.EnsureTrace` does; `rangeCtx true` takes it
in place of `TODO()`'s value alone. `txnCtx ctx cd` (an `isContext`, or `doneNil`) is the
context premise of the txn package's functions and of `traceutil`'s `EnsureTrace` and `Get`.

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

/-- The context `ctx`'s `Done()` returns `nil`: it is never canceled. `context.TODO()`'s
(`doneNil_todo`), and every context `context.WithValue` derives from one (its `Done` is its
parent's): the context `traceutil.EnsureTrace` returns for `TODO()`. -/
def doneNil (ctx : GoInterfaceOk) : IProp GF :=
  iprop(□ {{ True }} (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #()))
    {{ RET #chan.nil; True }})

instance doneNil_persistent (ctx : GoInterfaceOk) : Persistent (doneNil (GF := GF) ctx) := by
  unfold doneNil; infer_instance

/-- The context of the server's txn functions (and of `traceutil.EnsureTrace`/`Get`): an
`isContext`, or one whose `Done()` is `nil` (`context.TODO()`'s, or derived from it). -/
def txnCtx (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(doneNil ctx ∨ context.isContext ctx cd)

instance txnCtx_persistent (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (txnCtx (GF := GF) ctx cd) := by
  unfold txnCtx; infer_instance

/-- A descriptor whose Done proposition is `False`: never done (`neverDone_neverCd`), for a
context with a `nil` `Done()`, which no descriptor describes (`txnCtx` ignores it then). -/
def neverCd : context.ContextDesc (IProp GF) :=
  { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(False) }

theorem neverDone_neverCd : ⊢ neverDone (GF := GF) neverCd := by
  unfold neverDone neverCd
  imodintro
  iintro H
  iexact H

/-- The context of a range read: an `isContext`, or (`todo`) one never canceled: one whose
`Done()` is `nil` (`context.TODO()`'s, or derived from it), or an `isContext` whose Done
proposition never holds. -/
def rangeCtx (todo : Bool) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    IProp GF :=
  if todo then iprop(doneNil ctx ∨ (context.isContext ctx cd ∗ neverDone cd))
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
    iintro (#Hdn | ⟨#Hctx, #Hnd⟩)
    · iunfold doneNil at Hdn
      imodintro
      iintro %Φ - HΦ
      iapply Hdn
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

/-- `context.TODO()`'s `Done()` is `nil`. -/
theorem doneNil_todo : ⊢ doneNil (GF := GF) todoCtxV := by
  iunfold doneNil
  imodintro
  iapply wp_todoCtx_Done

/-- `context.TODO()`'s value is a `txnCtx` (with any descriptor). -/
theorem txnCtx_todo (cd : context.ContextDesc (IProp GF)) : ⊢ txnCtx (GF := GF) todoCtxV cd := by
  iunfold txnCtx
  ileft
  iapply doneNil_todo

/-- **A range read's context from a `txnCtx`**: the context `rangeCtx td` takes, never canceled
(`td`) if the caller's is (`nd`), or if its `Done()` is `nil`. -/
theorem txnCtx_rangeCtx (nd : Bool) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    txnCtx ctx cd ⊢ (if nd then neverDone cd else iprop(True)) -∗
      ∃ td : Bool, ⌜nd = true → td = true⌝ ∗ rangeCtx td ctx cd := by
  iunfold txnCtx
  iintro (#Hdn | #Hctx) #Hnd
  · iexists true
    isplitl []
    · ipureintro; intro _; rfl
    simp only [rangeCtx, ↓reduceIte]
    ileft; iexact Hdn
  · iexists nd
    isplitl []
    · ipureintro; exact id
    cases nd
    · simp only [rangeCtx, Bool.false_eq_true, ↓reduceIte]; iexact Hctx
    · simp only [rangeCtx, ↓reduceIte]; iright; iframe Hctx Hnd

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

section kinds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The revision a transaction reads at is not negative (2026-10-13, unit 6a: what
`rangeOutcomeC_neg` needs, for the frozen statements of the `Range`s). -/
theorem isTxn_readRev (mw s : Loc) (γ : StoreNames) (kind : TxnKind) (crev : Int)
    (Z : IProp GF) :
    isTxn (GF := GF) mw s γ kind crev Z ⊢ isTxn mw s γ kind crev Z ∗ ⌜0 ≤ sint.Z kind.readRev⌝ := by
  cases kind with
  | read log rev =>
    simp only [isTxn, TxnKind.readRev]
    iintro H
    ihave %Hr : ⌜0 ≤ sint.Z rev⌝ $$ [H]
    · iunfold isTxnRead at H
      iNamed H
      ihave %Hr := storeTxnReadIs_rev tr s rt trace γ log rev crev Z $$ Htr
      ipureintro; exact Hr.1
    iframe H
    ipureintro; exact Hr
  | write ilog pend puts deletes putSize =>
    simp only [isTxn, TxnKind.readRev]
    iintro H
    ihave %Hr : ⌜0 ≤ sint.Z (W64 ((writeRev ilog pend : Nat) : Int) : w64)⌝ $$ [H]
    · iunfold isTxnWrite at H
      iNamed H
      iapply storeTxnWriteIs_writeRev tw s γ ilog pend crev Z $$ Htw
    iframe H
    ipureintro; exact Hr

end kinds

end mvcc
end EtcdGrove
end Perennial
