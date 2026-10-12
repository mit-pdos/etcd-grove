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

theorem commitLog_length (ilog : Log) (pend : List Change) :
    (commitLog ilog pend).length = if pend = [] then ilog.length else ilog.length + 1 := by
  unfold commitLog; split <;> simp

/-- The tokens a sole writer at `log` holds: every token not spent on a committed revision. -/
def soleBudget (log : Log) : Nat := 2 ^ 63 - 3 - log.length

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The sole writer** at the committed log `log`: its certificate and every revision token not
spent (`soleBudget log`), and the log at least `NewStore`'s two revisions (`[[], []]`: so a
response's revision is at least `1`, what the gRPC layer's `header.fill` needs not to overwrite
it; 2026-10-12, the request path's unit 3a). Not persistent. -/
def soleWriter (γ : mvcc.StoreNames) (log : Log) : IProp GF :=
  iprop(idxCert γ.idx log ∗ ownToks γ.revs (soleBudget log) ∗ ⌜2 ≤ log.length⌝)

/-- The sole writer with a write transaction open: one token fewer (the transaction's). -/
def soleWriterOpen (γ : mvcc.StoreNames) (log : Log) : IProp GF :=
  iprop(idxCert γ.idx log ∗ ownToks γ.revs (soleBudget log - 1) ∗ ⌜2 ≤ log.length⌝)

/-- The sole writer's log has `NewStore`'s two revisions. -/
theorem soleWriter_len (γ : mvcc.StoreNames) (log : Log) :
    soleWriter (GF := GF) γ log ⊢ ⌜2 ≤ log.length⌝ := by
  unfold soleWriter
  iintro ⟨-, -, %h⟩
  ipureintro; exact h

instance soleWriter_timeless (γ : mvcc.StoreNames) (log : Log) : Timeless (soleWriter (GF := GF) γ log) := by
  unfold soleWriter idxCert; infer_instance

instance soleWriterOpen_timeless (γ : mvcc.StoreNames) (log : Log) :
    Timeless (soleWriterOpen (GF := GF) γ log) := by
  unfold soleWriterOpen idxCert; infer_instance

/-- `soleWriter_len`, keeping the sole writer. -/
theorem soleWriter_len' (γ : mvcc.StoreNames) (log : Log) :
    soleWriter (GF := GF) γ log ⊢ ⌜2 ≤ log.length⌝ ∗ soleWriter γ log := by
  unfold soleWriter
  iintro ⟨Hc, Ht, %h⟩
  iframe Hc Ht
  isplitl
  all_goals (ipureintro; exact h)

/-- **`NewStore` makes the sole writer** of its initial log `[[], []]`: its `2 ^ 63 - 5` tokens
are the budget, with the certificate of `[[], []]` (both in `NewStore`'s post, in this order). -/
theorem soleWriter_of_NewStore (γ : mvcc.StoreNames) :
    ownToks (GF := GF) γ.revs (2 ^ 63 - 5) ∗ idxCert γ.idx [[], []] ⊢ soleWriter γ [[], []] := by
  have h : soleBudget [[], []] = 2 ^ 63 - 5 := by unfold soleBudget; simp
  unfold soleWriter; rw [h]
  iintro ⟨Ht, Hc⟩
  iframe Ht Hc
  ipureintro; simp

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
    ipureintro; simp only [List.length_append, List.length_singleton]; omega

/-- `soleWriter_close` from what `metricsTxnWrite.End` returns (`txnEndPost`). -/
theorem soleWriter_close_end (γ : mvcc.StoreNames) (log : Log) (pend : List Change)
    (puts deletes putSize : w64) (h : log.length + 4 ≤ 2 ^ 63) :
    soleWriterOpen (GF := GF) γ log ∗ txnEndPost γ (.write log pend puts deletes putSize) ⊢
      soleWriter γ (commitLog log pend) := by
  unfold txnEndPost
  exact soleWriter_close γ log pend h

/-! ## The pins -/

/-- **Two certificates' shapes are comparable**: both are lower bounds of the index's history. -/
theorem idxCert_logShape (γ : mvcc.StoreNames) (a b : Log) :
    ⊢ idxCert (GF := GF) γ.idx a -∗ idxCert γ.idx b -∗
      ⌜logShape a <+: logShape b ∨ logShape b <+: logShape a⌝ := by
  unfold idxCert
  iintro ⟨Ha, -, -⟩ ⟨Hb, -, -⟩
  ihave %h := mono_list_lb_valid _ _ _ $$ Ha Hb
  ipureintro
  exact h.imp (histOf_prefix_logShape a b) (histOf_prefix_logShape b a)

/-- **The sole writer pins its write transaction** (`store.Write` returns `∃ ilog`): the
transaction's committed log `ilog` is the sole writer's. The tokens bound `ilog`'s length by
`log`'s (`ownTokAuth`'s count covers the sole writer's tokens and the transaction's:
`soleBudget log - 1 + 1 ≤ ntok`, and `ilog.length + ntok + 3 ≤ 2 ^ 63`); the index writer's
committed-log authority is above `log`'s certificate (`log <+: ilog`, `idxWriter_cert_prefix`). -/
theorem soleWriter_pins_write (γ : mvcc.StoreNames) (log ilog : Log) (pend : List Change) (tw s : Loc) :
    soleWriterOpen (GF := GF) γ log ∗ storeTxnWriteIs tw s γ ilog pend ⊢ ⌜ilog = log⌝ := by
  unfold soleWriterOpen
  iintro ⟨⟨#Hmycert, Hmine, -⟩, H⟩
  unfold storeTxnWriteIs
  icases H with ⟨%trace, %ti, %bt, %Locked, %chs, %ps, %ntok, H⟩
  iNamed H
  unfold revToken
  icombine Hmine Htok as Hall
  icombine Htoks Hall gives %hle
  ihave %hpre := idxWriter_cert_prefix γ.idx ilog pend log $$ [$Hw $Hmycert]
  ipureintro
  have hlen : (log <+: ilog) := hpre
  have hl := hlen.length_le
  have heq : ilog.length = log.length := by unfold soleBudget at hle; omega
  exact (hlen.eq_of_length heq.symm).symm

/-- `soleWriter_pins_write`, keeping the resources. -/
theorem soleWriter_pins_write' (γ : mvcc.StoreNames) (log ilog : Log) (pend : List Change) (tw s : Loc) :
    soleWriterOpen (GF := GF) γ log ∗ storeTxnWriteIs tw s γ ilog pend ⊢
      ⌜ilog = log⌝ ∗ (soleWriterOpen γ log ∗ storeTxnWriteIs tw s γ ilog pend) :=
  persistent_entails_right (soleWriter_pins_write γ log ilog pend tw s)

/-- **The sole writer pins its read transaction**, from `store.Read`'s post at the sole
writer's tokens and certificate: the log read extends `log` and leaves room for `log`'s tokens,
so it is `log`. -/
theorem soleWriter_pins_read (log log' : Log) (hlen : log.length + 3 ≤ 2 ^ 63)
    (h : log <+: log' ∧ log'.length + soleBudget log + 3 ≤ 2 ^ 63) : log' = log := by
  obtain ⟨hpre, hb⟩ := h
  have hl := hpre.length_le
  unfold soleBudget at hb
  exact (hpre.eq_of_length (by omega)).symm

/-- What a read transaction's log is to the sole writer's, from the certificates alone: shapes
in prefix order, one way or the other (`soleWriter_pins_read` has equality, from `store.Read`'s
post). -/
theorem soleWriter_read_shape (γ : mvcc.StoreNames) (log log' : Log) (tr s : Loc) (rt : GoInterfaceOk)
    (trace : Loc) (rev : w64) :
    ⊢ soleWriter (GF := GF) γ log -∗ storeTxnReadIs tr s rt trace γ log' rev -∗
      ⌜logShape log <+: logShape log' ∨ logShape log' <+: logShape log⌝ := by
  unfold soleWriter
  iintro ⟨#Hc, -, -⟩ H
  unfold storeTxnReadIs
  icases H with ⟨%m, H⟩
  iNamed H
  iapply idxCert_logShape $$ Hc Hcert

end defs

section wp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

open go_etcd_io.etcd.server.v3.storage.mvcc in
/-- **`store.Read` at the sole writer** reads its log: `store.Read`'s spec at the sole writer's
tokens and certificate, with `soleWriter_pins_read`. -/
theorem soleWriter_Read (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (mode : w32) (trace : Loc) (log : Log)
    (hlen : log.length + 3 ≤ 2 ^ 63) (htr : trace ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ soleWriter γ log }}
      (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Read")) (Val #mode)) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        ∃ rev : w64, mvcc.isTxnRead mw s γ log rev ∗ soleWriter γ log }} := by
  wp_start_folded as ⟨#Hs, Hrd, Hsw⟩
  iunfold soleWriter at Hsw
  icases Hsw with ⟨#Hc, Ht, %Hl2⟩
  iapply (hRead s γ mode trace (soleBudget log) log) $$ [Hrd Ht]
  · iframe # ∗
    ipureintro; exact htr
  inext
  iintro %mw ⟨%log', %rev, Htx, Ht, %Hp⟩
  have heq := soleWriter_pins_read log log' hlen Hp
  subst heq
  iapply HΦ
  iexists rev
  iunfold soleWriter
  iframe Htx Ht Hc
  ipureintro; exact Hl2

end wp

end txn
end EtcdGrove
end Perennial
