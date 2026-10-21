/-
The sole writer of the server's txn package (units 0b, 0c): **the revision tokens and the
certificate pin the logs a caller's transactions see.** Lean-first; the plan's "Premise: the
sole writer", `notes/STATUS.md`, "The server's txn package".

`Txn` reads (`checkTxn`, at a read transaction), then writes (`executeTxn`, at a write
transaction): it is the client model's `runTxn` only if no revision is committed in between. The
apply thread is etcd's only writer; in the model, the store's revision budget says so: `NewStore`
hands out `2 ^ 63 - 5` revision tokens (`ownToks γ.revs`), a write transaction costs one
(`revToken`), and the budget's authority `ownTokAuth γ.revs ntok` (half the writer's, half under
`s.revMu`) keeps `log.length + ntok + 3 ≤ 2 ^ 63` for the committed log. A caller holding all
`2 ^ 63 - 3 - log.length` tokens that are not spent, with the certificate of `log`
(`soleWriter γ log`), therefore finds every transaction it opens at a committed log no longer
than `log`; and no shorter, for the certificate is a lower bound of the committed log
(`idxCert` carries the log itself: unit 0c). So the write pin is `ilog = log`
(`soleWriter_pins_write`) and the read pin `log' = log` (`soleWriter_pins_read`, from
`store.Read`'s post; `soleWriter_Read`, `store.Read` at the sole writer).

**The bookkeeping.** `soleWriter γ log` holds exactly `soleBudget log = 2 ^ 63 - 3 - log.length`
tokens: a write transaction is opened with one of them (`soleWriter_split`), and `End` spends it
on a commit (`pend ≠ []`: one revision more, one token less) or, with no change, returns it
(`storeTxnWrite.End`'s post): `soleWriter_close`, `soleWriter_close_end`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode mvcc

/-! ## The committed log -/

/-- The state after the log a write transaction commits: the pending changes applied (none if
`pend = []`, no revision made). -/
theorem stateAfter_commitLog (ilog : Log) (pend : List Change) :
    stateAfter (commitLog ilog pend) = applyChanges (W64 ilog.length) (stateAfter ilog) pend := by
  unfold commitLog
  split
  · subst pend; rfl
  · exact stateAfter_snoc ilog pend

/-- The tokens a sole writer at `log` holds: every token not spent on a committed revision. -/
def soleBudget (log : Log) : Nat := 2 ^ 63 - 3 - log.length

/-- **The sole writer's log's length** (D19c's move, 2026-10-18): at least `NewStore`'s two
revisions, and a revision per non-empty change set past those two (a commit makes a revision
only of a non-empty pending one, `commitLog`), so the log's length is bounded by its changes,
which the time receipts bound (`mvcc.idxCert`). -/
def soleLog (log : Log) : Prop := 2 ≤ log.length ∧ log.length ≤ logCh log + 2

theorem soleLog_boot : soleLog [[], []] := by unfold soleLog logCh; simp

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem soleLog_commit (log : Log) (pend : List Change) (h : soleLog log) :
    soleLog (commitLog log pend) := by
  unfold commitLog
  split
  · exact h
  · rename_i hp
    have : 0 < pend.length := List.length_pos_iff.2 hp
    unfold soleLog at h ⊢
    rw [logCh_snoc]; simp only [List.length_append, List.length_singleton]; omega

/-- **The sole writer** at the committed log `log`: its certificate and every revision token not
spent (`soleBudget log`), and the log at least `NewStore`'s two revisions (`[[], []]`: so a
response's revision is at least `1`, what the gRPC layer's `header.fill` needs not to overwrite
it; 2026-10-12, the request path's unit 3a); since D19c's move (2026-10-18) a revision per
non-empty change set past those (`soleLog`) and the time receipts' bound at most `2 ^ 48` (the
store's, `NewStore`'s premise), so that the log the apply thread meets is small
(`soleWriter_small`). Not persistent. -/
def soleWriter (γ : mvcc.StoreNames) (log : Log) : IProp GF :=
  iprop(idxCert γ.idx log ∗ ownToks γ.revs (soleBudget log) ∗
    ⌜soleLog log ∧ receiptBound GF ≤ 2 ^ 48⌝)

/-- The sole writer with a write transaction open: one token fewer (the transaction's). -/
def soleWriterOpen (γ : mvcc.StoreNames) (log : Log) : IProp GF :=
  iprop(idxCert γ.idx log ∗ ownToks γ.revs (soleBudget log - 1) ∗
    ⌜soleLog log ∧ receiptBound GF ≤ 2 ^ 48⌝)

/-- **The log the sole writer is at is small** (D19c's move, 2026-10-18): a revision per change
past its first two, fewer than `2 ^ 48` changes (its certificate's receipts, `idxCert`). -/
theorem soleWriter_small' (γ : mvcc.StoreNames) (log : Log) :
    soleWriter (GF := GF) γ log ⊢ ⌜log.length ≤ logCh log + 2 ∧ logCh log < 2 ^ 48⌝ := by
  unfold soleWriter
  iintro ⟨#Hc, -, %h⟩
  ihave #hc := idxCert_sealed γ.idx log $$ Hc
  ihave %hc' := idxSealed_small γ.idx log $$ hc
  ipureintro
  have h1 := h.1.2
  have h2 := h.2
  omega

/-- The sole writer's certificate (persistent). -/
theorem soleWriter_cert (γ : mvcc.StoreNames) (log : Log) :
    soleWriter (GF := GF) γ log ⊢ soleWriter γ log ∗ idxCert γ.idx log := by
  unfold soleWriter
  iintro ⟨#Hc, Ht, %Hl⟩
  iframe Hc Ht
  ipureintro; exact Hl

/-- `soleWriter_len`, keeping the sole writer. -/
theorem soleWriter_len' (γ : mvcc.StoreNames) (log : Log) :
    soleWriter (GF := GF) γ log ⊢ ⌜2 ≤ log.length⌝ ∗ soleWriter γ log := by
  unfold soleWriter
  iintro ⟨Hc, Ht, %h⟩
  iframe Hc Ht
  isplitl
  · ipureintro; exact h.1.1
  · ipureintro; exact h

/-- **`NewStore` makes the sole writer** of its initial log `[[], []]`: its `2 ^ 63 - 5` tokens
are the budget, with the certificate of `[[], []]` (both in `NewStore`'s post, in this order). -/
theorem soleWriter_of_NewStore (γ : mvcc.StoreNames) (hrb : receiptBound GF ≤ 2 ^ 48) :
    ownToks (GF := GF) γ.revs (2 ^ 63 - 5) ∗ idxCert γ.idx [[], []] ⊢ soleWriter γ [[], []] := by
  have h : soleBudget [[], []] = 2 ^ 63 - 5 := by unfold soleBudget; simp
  unfold soleWriter; rw [h]
  iintro ⟨Ht, Hc⟩
  iframe Ht Hc
  ipureintro; exact ⟨soleLog_boot, hrb⟩

/-- **Opening a write transaction**: one token for `store.Write`, while the log leaves room for
one more revision (`log.length + 4 ≤ 2 ^ 63`). -/
theorem soleWriter_split (γ : mvcc.StoreNames) (log : Log) (h : log.length + 4 ≤ 2 ^ 63) :
    soleWriter (GF := GF) γ log ⊢ revToken γ ∗ soleWriterOpen γ log := by
  have hb : soleBudget log = (soleBudget log - 1) + 1 := by unfold soleBudget; omega
  unfold soleWriter soleWriterOpen revToken
  rw [hb, Nat.add_sub_cancel]
  iintro ⟨#Hc, Hn, %hl⟩
  icases (ownToks_add 1 (soleBudget log - 1) γ.revs).1 $$ Hn with ⟨Hn, H1⟩
  iframe H1 Hn
  isplitl
  · iexact Hc
  ipureintro; exact hl

/-- **Closing a write transaction** at the sole writer's log, with what `storeTxnWrite.End`
returns: with a change, the committed log is one revision longer and the transaction's token is
spent; with none, `End` gives the token back. -/
theorem soleWriter_close (γ : mvcc.StoreNames) (log : Log) (pend : List Change)
    (h : log.length + 4 ≤ 2 ^ 63) :
    soleWriterOpen (GF := GF) γ log ∗ idxCert γ.idx (commitLog log pend) ∗
        (if pend = [] then revToken γ else iprop(True)) ⊢
      soleWriter γ (commitLog log pend) := by
  unfold soleWriterOpen soleWriter
  by_cases hp : pend = []
  · subst hp
    have hc : commitLog log [] = log := rfl
    have hb : soleBudget log = (soleBudget log - 1) + 1 := by unfold soleBudget; omega
    simp only [hc, ↓reduceIte, revToken]
    iintro ⟨⟨#Hc, Hn, %hl⟩, -, H1⟩
    iframe Hc
    rw [hb, Nat.add_sub_cancel]
    isplitl
    · iapply (ownToks_add 1 (soleBudget log - 1) γ.revs).2
      iframe Hn H1
    ipureintro; exact hl
  · have hc : commitLog log pend = log ++ [pend] := by unfold commitLog; simp [hp]
    have hb : soleBudget (log ++ [pend]) = soleBudget log - 1 := by
      unfold soleBudget; simp only [List.length_append, List.length_singleton]; omega
    simp only [hp, ↓reduceIte, hc, hb]
    iintro ⟨⟨-, Hn, %hl⟩, #Hc, -⟩
    iframe Hc Hn
    ipureintro; rw [← hc]; exact ⟨soleLog_commit log pend hl.1, hl.2⟩

/-! ## The pins -/

/-- **The sole writer pins its read transaction**, from `store.Read`'s post at the sole
writer's tokens and certificate: the log read extends `log` and leaves room for `log`'s tokens,
so it is `log`. -/
theorem soleWriter_pins_read (log log' : Log) (hlen : log.length + 3 ≤ 2 ^ 63)
    (h : log <+: log' ∧ log'.length + soleBudget log + 3 ≤ 2 ^ 63) : log' = log := by
  obtain ⟨hpre, hb⟩ := h
  have hl := hpre.length_le
  unfold soleBudget at hb
  exact (hpre.eq_of_length (by omega)).symm

end defs

section wp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

open go_etcd_io.etcd.server.v3.storage.mvcc in

open go_etcd_io.etcd.server.v3.storage.mvcc in
/-- **`store.Read` at the sole writer, with a floor** (the vertical slice's unit V2): as
`soleWriter_Read`, the read opened at the longer of the sole writer's log and a certified floor
`F` (a log a client saw), so the sole writer's log extends `F`. -/
theorem soleWriter_Read_floor (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (mode : w32) (trace : Loc) (log : Log) (te : Bool) (F : Log)
    (hlen : log.length + 3 ≤ 2 ^ 63) (htr : trace ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log ∗ traceutil.ownTrace trace te ∗
        idxCert γ.idx F }}
      (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Read")) (Val #mode)) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        ∃ rev : w64, mvcc.isTxnRead mw s γ trace log rev ∗ soleWriter γ log ∗ ⌜F <+: log⌝ }} := by
  have hRead := mvcc.store.Read.spec_frozen hRead
  wp_start_folded as ⟨#Hs, Hrd, Hsw, Htrc, #HF⟩
  iunfold soleWriter at Hsw
  icases Hsw with ⟨#Hc, Ht, %Hl2⟩
  ihave %Hp := idxCert_prefix γ.idx log F $$ [$Hc $HF]
  have hj : ∃ L0, log <+: L0 ∧ F <+: L0 ∧ (L0 = log ∨ L0 = F) := by
    rcases Hp with h | h
    · exact ⟨F, h, List.prefix_refl _, Or.inr rfl⟩
    · exact ⟨log, List.prefix_refl _, h, Or.inl rfl⟩
  obtain ⟨L0, hl, hf, hL0⟩ := hj
  ihave #Hc0 : idxCert γ.idx L0 $$ []
  · rcases hL0 with rfl | rfl
    · iexact Hc
    · iexact HF
  iapply (hRead s γ mode trace (soleBudget log) L0 te) $$ [Hrd Ht Htrc]
  · iframe # ∗
    ipureintro; exact htr
  inext
  iintro %mw ⟨%log', %rev, Htx, Ht, -, %Hp'⟩
  have heq := soleWriter_pins_read log log' hlen ⟨hl.trans Hp'.1, Hp'.2⟩
  subst heq
  iapply HΦ
  iexists rev
  iframe Htx
  isplitl [Ht]
  · iunfold soleWriter
    iframe Ht Hc
    ipureintro; exact Hl2
  ipureintro; exact hf.trans Hp'.1

end wp

end txn
end EtcdGrove
end Perennial
