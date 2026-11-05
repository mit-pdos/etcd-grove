/-
**The txn package's vocabulary over mvcc's API** (strict M1, 2026-11-05; the frozen draft
`notes/mvcc-api-clients/TxnSpecs.lean`, its `txn.api.*` names without the prefix): what a
transaction's reads see (`mstate`), its kind after changes (`MTxn.isRead`, `MTxn.append`), what
txn records of a state at an update (`Reach`), a put's and a delete's pending changes, `Txn`'s
premise at its log (`TxnPreA`) and changes (`txnChs`); and the caller's updates in the exact
shapes of the API's contracts (`readAU`, `beginAU`, `commitAU`, `putAU`, `delAU`, `txnBeginAU`),
the critical section under the batch lock (`csA`) and the writer's backend (`kvBackend`).

txn allocates no ghost state and keeps no invariant (`notes/mvcc-api-clients/clients-txn.md` §3):
its entry points pass the caller's updates to mvcc's contracts.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccReachable MvccName BkRef mvccN mvccLeases)

/-! ## The vocabulary (pure) -/

/-- The state a transaction's reads see: a read transaction's committed state, a write
transaction's pending one. -/
def txn.mstate : MTxn → List EtcdKv
  | .read σ => mvcc.stateAfter σ.log
  | .write σ pend => txn.pendState σ.log pend

/-- A read transaction (the read-only wrapper's kind). -/
def txn.MTxn.isRead : MTxn → Bool
  | .read _ => true
  | .write _ _ => false

/-- The transaction after the changes `chs` (a read transaction's is unchanged: `executeTxn`'s
read-only runs make none). -/
def txn.MTxn.append : MTxn → List mvcc.Change → MTxn
  | .read σ, _ => .read σ
  | .write σ pend, chs => .write σ (pend ++ chs)

/-- What txn knows of every state it reads at an update (`mvccState_reachable`), carried to the
internal specs: reachable, room for its revisions. -/
def txn.Reach (σ : MvccState) : Prop := MvccReachable σ ∧ σ.log.length + 3 ≤ 2 ^ 63

/-- **A put's pending changes** at the state `σ₀` its write transaction began at: none if it needs
the previous key-value and the key has none (`ErrKeyNotFound`), else its one change. -/
def txn.putPend (o : OpFull) (σ₀ : MvccState) : List mvcc.Change :=
  if txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter σ₀.log) = none then []
  else [txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))]

/-- **A delete's pending changes**: the range's keys at `σ₀`'s state (`delChanges`), or none when
its `PrevKv` range read failed with the context's error (`ok = false`). -/
def txn.delPend (o : OpFull) (σ₀ : MvccState) (ok : Bool) : List mvcc.Change :=
  if ok then txn.delChanges (mvcc.stateAfter σ₀.log) o else []

/-- `Txn`'s premise at the log it runs at: today's `TxnPre` without its two size conjuncts (room
for a revision is `mvccState_reachable`'s, the sort's premise `Txn.Range`'s `stateOk`). -/
def txn.TxnPreA (log : mvcc.Log) (t : TxnModel) : Prop :=
  txn.OpsOk true (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
    (t.branch (txn.txnOk (mvcc.stateAfter log) t))

/-- The changes `Txn` makes at the log `log`. -/
abbrev txn.txnChs (log : mvcc.Log) (t : TxnModel) : List mvcc.Change :=
  (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-! ## The vocabulary (the caller's updates, as the API's contracts take them) -/

/-- **The caller's update at a read** (`KV.Read`'s, `KV.Range`'s): the state unchanged, `Q σ`. -/
abbrev txn.readAU (γ : MvccName) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvcc.api.mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ mvcc.api.mvccState γ σ, COMM Q σ }>)

/-- **The caller's update at a write transaction's begin** (`KV.Write`'s): nothing pending, the
state unchanged, `R σ` (the caller gives `R σ`: for the sole writer, its pin and the next
updates). -/
abbrev txn.beginAU (γ : MvccName) (R : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvcc.api.mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ.pending = none⌝ ∗ mvcc.api.mvccState γ σ, COMM R σ }>)

/-- **The caller's two updates at a write transaction's `End`** (`Txn.End`'s, at the state `σ₀` it
began at, with the changes `pend`): the notification (mvcc gives with it the receipt of the history
it makes, round 16, which the caller keeps: the server's `LogSmall`), then the commit, then `Q`. -/
abbrev txn.commitAU (γ : MvccName) (σ₀ : MvccState) (pend : List mvcc.Change) (Q : IProp GF) :
    IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvcc.api.mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ = σ₀⌝ ∗ mvcc.api.mvccState γ (σ.notify pend) ∗ ⧖ (mvcc.logCh (σ.log ++ [pend])), COMM
      AU <{ ∃∃ (σ' : MvccState), mvcc.api.mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvcc.api.mvccState γ σ'.commitPending, COMM Q }> }>)

/-- **The critical section under the store's batch lock** (today's `csContract`, in the API's
terms: `Write` runs the hook from `Pre` to `Q` under the lock, `hookRun`, which also covers a `nil`
hook; txn turns `Q` into the lock's invariant and `Post` before `End`). -/
def txn.csA (P : IProp GF) (f : GoFunc) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(Pre ∗ mvcc.api.hookRun P f Pre Q ∗ (Q ={⊤}=∗ P ∗ Post))

/-- **The writer's backend**: a share of the store's backend `B` (batch-lock invariant `P`) and its
hook `f` (persistent). -/
def txn.kvBackend (γ : MvccName) (q : Qp) (B : BkRef) (P : IProp GF) (f : GoFunc) :
    IProp GF :=
  iprop(mvcc.api.mvccBackend γ q B P ∗ mvcc.api.hookIs B f)

/-- **A put's updates**: the begin (the caller gives the lessor's item map `I` at the state, and,
for `IgnoreLease`, that the key's lease is live), then the commit of `putPend o σ₀`, then `R σ₀`. -/
def txn.putAU (γ : MvccName) (o : OpFull) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (R : MvccState → IProp GF) : IProp GF :=
  txn.beginAU γ (fun σ₀ =>
    iprop(⌜mvcc.pendItems σ₀.log [] = I⌝ ∗
      (if o.ignoreLease then txn.leaseOk L (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log)))
       else iprop(True)) ∗
      txn.commitAU γ σ₀ (txn.putPend o σ₀) (R σ₀)))

/-- **A delete's updates**: the begin (the item map `I` at the state), then the commit of the
deletes (or, after a context error, of nothing), then `R σ₀ ok`. -/
def txn.delAU (γ : MvccName) (o : OpFull)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (R : MvccState → Bool → IProp GF) :
    IProp GF :=
  txn.beginAU γ (fun σ₀ =>
    iprop(⌜mvcc.pendItems σ₀.log [] = I⌝ ∗
      ∀ ok : Bool, txn.commitAU γ σ₀ (txn.delPend o σ₀ ok) (R σ₀ ok)))

/-- **`Txn`'s write updates at the sole writer of `log`** (a request that writes): the begin, where
the caller gives the pin (the state's log is `log`: no commit since the read), then the commit of
the run's changes at `log`, then `Qw σ`. The caller builds them from its read update's `Qr`, only
once the checks passed (`Txn.specSole`'s wand), so that a failed check leaves its resources in `Qr`. -/
def txn.txnBeginAU (γ : MvccName) (log : mvcc.Log) (t : TxnModel) (Qw : MvccState → IProp GF) :
    IProp GF :=
  txn.beginAU γ (fun σ =>
    iprop(⌜σ.log = log⌝ ∗ txn.commitAU γ σ (txn.txnChs log t) (Qw σ)))

/-- **A transaction's response after a failed run** (read-only; `txn`'s error outcome): not
nil, its header and the header's revision, its `Responses` slice (what `Txn` reads for its
trace). (Moved from `Spec/.../txn/txn.lean` at strict M1.) -/
def txn.txnRespShell (resp : Loc) : IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (rev : w64),
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl)

instance txn.txnRespShell_persistent (resp : Loc) :
    Persistent (txn.txnRespShell (GF := GF) resp) := by
  unfold txn.txnRespShell; infer_instance

end vocab

/-! ## The sort's premise from `Txn.Range`'s `stateOk` (pure)

`txn.kvOk` (non-negative values) is gone, unified with the API's `kvSortOk` (round 16: positive
values, stronger). The comparators (`kvSortBy*__Less`, `sortRangeResults`) need only non-negative
values (Go's `(a - b) < 0` is the signed order for values in `[0, 2^63)`), so they take `kvSortOk`
and weaken by `kvSortOk_nonneg`. `sortSmall` (`TxnRun.lean`) is stated over `kvSortOk`. -/

section sortpure
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- **The sort's premise from a range's `stateOk`** (`srvPre_small` at `kvSortOk`). -/
theorem txn.srvPre_stateOk (o : OpFull) (st : List EtcdKv) (h : mvcc.api.stateOk st) :
    txn.sortSmall o st := by
  intro _
  unfold txn.srvPre
  split
  · simp
  · have hin : (rangeIn st o).length ≤ st.length := List.length_filter_le _ _
    have htk : ∀ (lim : Option Nat) (l : List EtcdKv), (mvcc.takeLimit lim l).length ≤ l.length := by
      intro lim l; cases lim <;> simp [mvcc.takeLimit]; omega
    have hmem : ∀ (lim : Option Nat) (l : List EtcdKv) (x : EtcdKv), x ∈ mvcc.takeLimit lim l → x ∈ l := by
      intro lim l x hx; cases lim with
      | none => exact hx
      | some n => exact List.mem_of_mem_take hx
    refine ⟨?_, ?_⟩
    · have := List.length_filter_le (kvFilterOk o)
        ((mvcc.takeLimit (mvcc.limitOf (txn.rangeLimitOf o)) (rangeIn st o)).map
          (txn.kvRead (txn.fastKeysOnly o)))
      have := htk (mvcc.limitOf (txn.rangeLimitOf o)) (rangeIn st o)
      have := h.1
      simp only [List.length_map] at *
      omega
    · intro v hv
      obtain ⟨hv, _⟩ := List.mem_filter.1 hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      have hw' := h.2 w (List.mem_filter.1 (hmem _ _ _ hw)).1
      unfold txn.kvRead; split <;> exact hw'

end sortpure

end EtcdGrove
end Perennial
