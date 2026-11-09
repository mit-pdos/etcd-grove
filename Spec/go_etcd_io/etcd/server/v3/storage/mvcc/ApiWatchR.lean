/-
**DRAFT (mvccfull's Freeze list, item 5): `WatchStream.Watch` takes the caller's update only for a
non-empty range.** Candidate restatement of `mvcc.api.WatchStream.Watch.contract` (`Api.lean`), side
by side with it (the original untouched). Scratch: not imported, not linked.

Today's contract asks the caller's atomic update `au` even when the range is empty, where the code
registers nothing and hands `au` back unused. A client whose invariant excludes unregistered
watchers cannot build such an `au` (mvccfull's `Watch(k, k)` check; mvccrand builds one only through
`register_au_empty`, a vacuous update). `contractR` asks `⌜empty⌝ ∨ au`: a case split on the input
(the principles' "a case split on the input is not one" disjunction of alternative specs). The empty
branch of the post gives nothing back (review round 1's F4.1: a give-back `⌜empty⌝ ∨ au` there was
vacuous, its left disjunct holding; a caller who held `au` frames it around the call,
`contract_of_contractR`).

**True of the code** (`server/v3/storage/mvcc/watcher.go`, `watchStream.Watch`, l.115-147): the
range check `if len(end) != 0 && bytes.Compare(key, end) != -1 { return -1, ErrEmptyWatcherRange }`
(l.118-120) is the first statement, before `ws.mu.Lock()` (l.122), the closed check (l.124), the id
choice (l.128-136), the store's `watch` (l.138) and `trace.SpanFromContext` (l.140): on that path
nothing but `key`, `end` and the two slices' contents is read, so the update is never needed there;
`len(end) != 0 ∧ compare ≠ -1` is `e ≠ [] ∧ ¬ GoStringLt kk e` (the proof's `bytes.compareResult`
cases, `watchStream__Watch.lean` l.75-96). The other paths (closed, registered) use the update
exactly as today, and there the range is non-empty, so `au` is the disjunct given.

**The proof's change** (`Proof/.../mvcc/watchStream__Watch.lean`, 345 lines): the `key ≥ end`
branch (l.84-93) drops the disjunction where it framed `Hau` (nothing is given back there),
unchanged otherwise; the two other branches (`len(end) = 0`, `key < end`) have
`hne : e = [] ∨ GoStringLt kk e` already in hand (l.66-81, l.95), so one
`icases Hau with (%Hemp | Hau)` and an `exfalso` from `hne` at the top of the shared `all_goals`
block (l.96) reduce them to today's proof: about 5 lines.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- **`Watch(ctx, 0, key, end, startRev, fcs...)`** (DRAFT, item 5; the id the stream's; a start
revision not negative): an empty range (`end` non-empty and `key ≥ end`), `ErrEmptyWatcherRange`
and `-1`, with no update needed; else the caller's update over the store's state (unchanged) and
the stream's: closed, unchanged (`ErrEmptyWatcherRange`); open, a watcher registered under a fresh
id, of the range, filtered by `fs`, from `watchLo σ startRev`, after the `k` responses sent so far,
live. As `WatchStream.Watch.contract`, but the pre's `au` is `⌜empty⌝ ∨ au`. -/
abbrev WatchStream.Watch.contractR (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (ι : WsName) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key endk fcs : GoSlice) (kk e : List w8) (fs : List (EvM → Bool)) (startRev : w64)
    (Q : MvccState → StreamState → w64 → IProp GF),
  let au := iprop(AU <{ ∃∃ (σ : MvccState) (S : StreamState), mvccState γ σ ∗ wsState ι S }>
      @ ⊤ \ ↑mvccN, ∅
    <{ ∀∀ (id : w64) (k : Nat), mvccState γ σ ∗
        (if S.closed then ⌜id = W64 (-1)⌝ ∗ wsState ι S
         else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ wsSentLb ι k ∗
           wsState ι (S.register id
             ⟨watchRangeOf kk e endk startRev id, fs, watchLo σ startRev, k, true⟩)),
      COMM Q σ S id }>)
  {{ pkgInit ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ mvccReaders γ 1 ∗
      (⌜ctx = interface.mk context.todoCtx.ty #(zero_val context.todoCtx)⌝ ∨
        (context.isContext ctx cd ∗ trace.spanCtxOk ctx)) ∗
      key ↦*□ kk ∗ endk ↦*□ e ∗ filtersImpl fcs fs ∗ ⌜0 ≤ sint.Z startRev⌝ ∗
      (⌜e ≠ [] ∧ ¬ go.GoStringLt kk e⌝ ∨ au) }}
    (App (App (App (App (App (App (Val #(methods ty go!"Watch" v)) (Val #(GoInterface.ok ctx)))
      (Val #(W64 0))) (Val #key)) (Val #endk)) (Val #startRev)) (Val #fcs))
  {{ (id : w64) (err : GoInterface), RET (PairV #id #err); mvccReaders γ 1 ∗
      ((⌜e ≠ [] ∧ ¬ go.GoStringLt kk e ∧ id = W64 (-1)⌝ ∗ globalAddr ErrEmptyWatcherRange ↦□ err) ∨
       (⌜e = [] ∨ go.GoStringLt kk e⌝ ∗ ∃ (σ : MvccState) (S : StreamState), Q σ S id ∗
          (if S.closed then globalAddr ErrEmptyWatcherRange ↦□ err
           else ⌜err = GoInterface.nil⌝))) }}

/-- **Today's contract is an instance** (a caller holding `au` gives the right disjunct): on an empty
range the caller frames its `au` around the call and gives the left disjunct, getting back the empty
branch (the other contradicts the range); on a non-empty one it gives `au` and the empty branch
contradicts the range. -/
theorem WatchStream.Watch.contract_of_contractR (ty : go.GoType) (v : val)
    (h : WatchStream.Watch.contractR (GF := GF) ty v) :
    WatchStream.Watch.contract (GF := GF) ty v := by
  intro γ ι ctx cd key endk fcs kk e fs startRev Q
  iintro %Φ ⟨#Hpkg, Hws, Hrd, Hctx, #Hk, #He, Hfi, %Hsr, Hau⟩ HΦ
  by_cases hemp : e ≠ [] ∧ ¬ go.GoStringLt kk e
  · iapply (h γ ι ctx cd key endk fcs kk e fs startRev Q) $$ [Hws Hrd Hctx Hfi]
    · iframe; iframe #
      isplitr
      · ipureintro; exact Hsr
      · ileft; ipureintro; exact hemp
    iintro !> %id %err ⟨Hrd, Hres⟩
    iapply HΦ
    iframe Hrd
    icases Hres with (⟨%Hi, #Herr⟩ | ⟨%Hne, -⟩)
    · ileft
      iframe Herr Hau
      ipureintro; exact Hi
    · iexfalso; ipureintro
      rcases Hne with h1 | h1
      · exact hemp.1 h1
      · exact hemp.2 h1
  · iapply (h γ ι ctx cd key endk fcs kk e fs startRev Q) $$ [Hws Hrd Hctx Hfi Hau]
    · iframe; iframe #
      ipureintro; exact Hsr
    iintro !> %id %err ⟨Hrd, Hres⟩
    iapply HΦ
    iframe Hrd
    icases Hres with (⟨%Hi, -⟩ | Hres)
    · iexfalso; ipureintro; exact hemp ⟨Hi.1, Hi.2.1⟩
    · iright; iexact Hres

end contracts

end api
end mvcc
end EtcdGrove
end Perennial
