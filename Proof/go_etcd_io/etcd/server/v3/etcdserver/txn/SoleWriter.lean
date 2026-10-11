/-
The sole writer of the server's txn package (unit 0b): **the revision tokens pin the write
transaction's log.** Lean-first; the plan's "Premise: the sole writer", `notes/STATUS.md`, "The
server's txn package".

`Txn` reads (`checkTxn`, at a read transaction), then writes (`executeTxn`, at a write
transaction): it is the client model's `runTxn` only if no revision is committed in between. The
apply thread is etcd's only writer; in the model, the store's revision budget says so: `NewStore`
hands out `2 ^ 63 - 5` revision tokens (`ownToks γ.revs`), a write transaction costs one
(`revToken`), and the writer's authority `ownTokAuth γ.revs ntok` keeps
`ilog.length + ntok + 3 ≤ 2 ^ 63` (`writerRes`, `storeTxnWriteIs`). A caller holding all
`2 ^ 63 - 3 - log.length` tokens that are not spent, with the certificate of `log`
(`soleWriter γ log`), therefore finds every write transaction it opens at a committed log no
longer than `log`, and (the certificates) no shorter.

**What the certificates pin.** `idxCert γ.idx log` is a lower bound of the index's history,
whose items are the events (revision, key, delete or not) and the commit markers: it fixes the
log's length and *shape* (`logShape`), not its values and leases. So the write pin is
`ilog.length = log.length ∧ logShape ilog = logShape log` (`soleWriter_pins_write`); `ilog = log`
needs a certificate of the log's values from mvcc (`notes/STATUS.md`: the history's commit
marker carrying the revision's changes would do).

**The bookkeeping.** `soleWriter γ log` holds exactly `soleBudget log = 2 ^ 63 - 3 - log.length`
tokens: a write transaction is opened with one of them (`soleWriter_split`), and `End` spends it
on a commit (`pend ≠ []`: one revision more, one token less) or, with no change, should return
it (`soleWriter_close`). mvcc's `End` returns it in neither case (`txnEndPost`: the certificate
alone): after an `End` with no change, the token is lost (`writerRes`'s count does not drop) and
the exact count — on which the pin rests — is gone; no weaker bookkeeping recovers the pin (each
lost token lets a writer commit one revision unseen). So `soleWriter_close` takes the token
back as a premise for `pend = []`, which `End`'s spec must supply (`notes/STATUS.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
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
spent (`soleBudget log`). Not persistent. -/
def soleWriter (γ : mvcc.StoreNames) (log : Log) : IProp GF :=
  iprop(idxCert γ.idx log ∗ ownToks γ.revs (soleBudget log))

/-- The sole writer with a write transaction open: one token fewer (the transaction's). -/
def soleWriterOpen (γ : mvcc.StoreNames) (log : Log) : IProp GF :=
  iprop(idxCert γ.idx log ∗ ownToks γ.revs (soleBudget log - 1))

instance soleWriter_timeless (γ : mvcc.StoreNames) (log : Log) : Timeless (soleWriter (GF := GF) γ log) := by
  unfold soleWriter idxCert; infer_instance

instance soleWriterOpen_timeless (γ : mvcc.StoreNames) (log : Log) :
    Timeless (soleWriterOpen (GF := GF) γ log) := by
  unfold soleWriterOpen idxCert; infer_instance

/-- **`NewStore` makes the sole writer** of its initial log `[[], []]`: its `2 ^ 63 - 5` tokens
are the budget, with the certificate of `[[], []]` (which `NewStore`'s spec does not return yet:
`notes/STATUS.md`). -/
theorem soleWriter_of_NewStore (γ : mvcc.StoreNames) :
    idxCert (GF := GF) γ.idx [[], []] ∗ ownToks γ.revs (2 ^ 63 - 5) ⊢ soleWriter γ [[], []] := by
  have h : soleBudget [[], []] = 2 ^ 63 - 5 := by unfold soleBudget; simp
  unfold soleWriter; rw [h]

/-- **Opening a write transaction**: one token for `store.Write`, while the log leaves room for
one more revision (`log.length + 4 ≤ 2 ^ 63`). -/
theorem soleWriter_split (γ : mvcc.StoreNames) (log : Log) (h : log.length + 4 ≤ 2 ^ 63) :
    soleWriter (GF := GF) γ log ⊢ revToken γ ∗ soleWriterOpen γ log := by
  have hb : soleBudget log = (soleBudget log - 1) + 1 := by unfold soleBudget; omega
  unfold soleWriter soleWriterOpen revToken
  rw [hb, Nat.add_sub_cancel]
  iintro ⟨#Hc, Hn⟩
  icases (ownToks_add 1 (soleBudget log - 1) γ.revs).1 $$ Hn with ⟨Hn, H1⟩
  iframe H1 Hn
  iexact Hc

/-- **Closing a write transaction** at the sole writer's log: with a change, the committed log is
one revision longer and the transaction's token is spent; with none, the token comes back
(a premise: mvcc's `End` does not return it). -/
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
    iintro ⟨⟨#Hc, Hn⟩, -, H1⟩
    iframe Hc
    rw [hb, Nat.add_sub_cancel]
    iapply (ownToks_add 1 (soleBudget log - 1) γ.revs).2
    iframe Hn H1
  · have hc : commitLog log pend = log ++ [pend] := by unfold commitLog; simp [hp]
    have hb : soleBudget (log ++ [pend]) = soleBudget log - 1 := by
      unfold soleBudget; simp only [List.length_append, List.length_singleton]; omega
    simp only [hp, ↓reduceIte, hc, hb]
    iintro ⟨⟨-, Hn⟩, #Hc, -⟩
    iframe Hc Hn

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
transaction's committed log `ilog` has the sole writer's length and shape. The tokens bound
`ilog`'s length by `log`'s (`ownTokAuth`'s count covers the sole writer's tokens and the
transaction's: `soleBudget log ≤ ntok`, and `ilog.length + ntok + 3 ≤ 2 ^ 63`), the index's
authority (the writer's) is above `log`'s certificate (`ilog` at least as long, its shape
extending `log`'s). -/
theorem soleWriter_pins_write (γ : mvcc.StoreNames) (log ilog : Log) (pend : List Change) (tw s : Loc) :
    soleWriterOpen (GF := GF) γ log ∗ storeTxnWriteIs tw s γ ilog pend ⊢
      ⌜ilog.length = log.length ∧ logShape ilog = logShape log⌝ := by
  unfold soleWriterOpen
  iintro ⟨⟨Hmycert, Hmine⟩, H⟩
  unfold storeTxnWriteIs
  icases H with ⟨%trace, %ti, %bt, %Locked, %chs, %ps, %ntok, H⟩
  iNamed H
  unfold revToken
  icombine Hmine Htok as Hall
  icombine Htoks Hall gives %hle
  unfold idxCert
  icases Hmycert with ⟨Hlb, -, -⟩
  unfold idxWriter
  icases Hw with ⟨Hauth, -, -⟩
  ihave %hpre := mono_list_auth_lb_valid _ _ _ _ $$ Hauth Hlb
  ipureintro
  obtain ⟨-, hpre⟩ := hpre
  have hlen : ilog.length < 2 ^ 63 := by omega
  obtain ⟨-, -, -, hge⟩ := histOf_prefix_shape log ilog pend hpre hlen
  have hsh := histOf_prefix_shape_logShape log ilog pend hpre
  have heq : ilog.length = log.length := by unfold soleBudget at hle; omega
  exact ⟨heq, (logShape_eq_of_prefix hsh (by omega)).symm⟩

/-- `soleWriter_pins_write`, keeping the resources. -/
theorem soleWriter_pins_write' (γ : mvcc.StoreNames) (log ilog : Log) (pend : List Change) (tw s : Loc) :
    soleWriterOpen (GF := GF) γ log ∗ storeTxnWriteIs tw s γ ilog pend ⊢
      ⌜ilog.length = log.length ∧ logShape ilog = logShape log⌝ ∗
        (soleWriterOpen γ log ∗ storeTxnWriteIs tw s γ ilog pend) :=
  persistent_entails_right (soleWriter_pins_write γ log ilog pend tw s)

/-- What a read transaction's log is to the sole writer's, from the certificates alone: shapes
in prefix order, one way or the other. (Equality needs mvcc's `store.Read` to relate the log it
reads to the caller's tokens and certificate: `notes/STATUS.md`.) -/
theorem soleWriter_read_shape (γ : mvcc.StoreNames) (log log' : Log) (tr s : Loc) (rt : GoInterfaceOk)
    (trace : Loc) (rev : w64) :
    ⊢ soleWriter (GF := GF) γ log -∗ storeTxnReadIs tr s rt trace γ log' rev -∗
      ⌜logShape log <+: logShape log' ∨ logShape log' <+: logShape log⌝ := by
  unfold soleWriter
  iintro ⟨#Hc, -⟩ H
  unfold storeTxnReadIs
  icases H with ⟨%m, H⟩
  iNamed H
  iapply idxCert_logShape $$ Hc Hcert

end defs

end txn
end EtcdGrove
end Perennial
