/-
**The watch workload's shared vocabulary** (`examples/common/watch.go`; 2026-10-22, D33). Lean-first
(no Rocq counterpart). What watchkv's `Defs.lean`, `WatchModel.lean` and `WatchFacts.lean` defined
that cachekv and linkv3p's watch workload used too, over the shared Go types (`KV`, `Event`,
`PutRec`): the values `Gen` picks from, a `KV`'s pair, what `Check` needs not to panic (`CheckOk`),
a revision of the store as a put (`revAt`), the watch's position after `n` events (`Cur`), an
event's facts at a per-revision predicate `R` (`evFactR`: `revAt E` at one server, the cluster
history's for linkv3p), what `Collect` returns (`collectOk`), and the receive from a client watch
channel.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The program's structs (`KV`, `Event`, `PutRec`), by short names. -/
abbrev wkv := github_com.mit_pdos.etcd_grove.examples.common.KV
abbrev wev := github_com.mit_pdos.etcd_grove.examples.common.Event
abbrev wrec := github_com.mit_pdos.etcd_grove.examples.common.PutRec

/-- The values `Gen` picks from. -/
abbrev genVals : List GoString := [go!"a", go!"b", go!"c", go!"d"]

/-- A `kv`'s key and value. -/
def pairOf (p : wkv) : GoString × GoString := (p.Key', p.Val')

/-- A `KV` `Gen` of `keys` may return. -/
def GenKv (keys : List GoString) (p : wkv) : Prop := p.Key' ∈ keys ∧ p.Val' ∈ genVals

/-- **What `check` needs not to panic**: the events are puts at revisions `2, 3, ...` (one per
revision, in order), each of a key and value tried, fewer than `2 ^ 63 - 1`; and each successful Put
is the event at its revision with its key and value. -/
def CheckOk (evs : List wev) (tried : List wkv) (oks : List wrec) : Prop :=
  evs.length + 1 < 2 ^ 63 ∧
  (∀ (i : Nat) (e : wev), evs[i]? = some e →
    e.Put' = true ∧ sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ tried.map pairOf) ∧
  (∀ p ∈ oks, 2 ≤ sint.Z p.Rev' ∧ ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e ∧
    e.Key' = p.Key' ∧ e.Val' = p.Val')


/-- **The watch's position after `n` events** (see the file header). -/
def Cur (n : Nat) (c : w64) : Prop :=
  (n = 0 ∧ 0 ≤ sint.Z c ∧ sint.Z c ≤ 1) ∨ (1 ≤ n ∧ sint.Z c = 1 + n)

theorem Cur_zero : Cur 0 (W64 0) := Or.inl ⟨rfl, by decide, by decide⟩

end pure

section rev
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Revision `r` of the store is the put of `k ↦ v`** (persistent): a sealed log of the store
`E.γ` has it. -/
def revAt (E : apply.AEnv GF) (r : Nat) (k v : GoString) : IProp GF :=
  iprop(∃ L : mvcc.Log, mvcc.idxSealed E.γ.idx L ∗ ⌜L[r]? = some [mvcc.Change.put k v (W64 0)]⌝)

instance revAt_persistent (E : apply.AEnv GF) (r : Nat) (k v : GoString) :
    Persistent (revAt (GF := GF) E r k v) := by
  unfold revAt; infer_instance

/-- **Two `revAt`s of one revision agree.** -/
theorem revAt_agree (E : apply.AEnv GF) (r : Nat) (k v k' v' : GoString) :
    revAt (GF := GF) E r k v ∗ revAt E r k' v' ⊢ ⌜k = k' ∧ v = v'⌝ := by
  unfold revAt
  iintro ⟨⟨%L, #H, %h⟩, ⟨%L', #H', %h'⟩⟩
  ihave %Hp := mvcc.idxSealed_prefix E.γ.idx L L' $$ [H H']
  · isplit
    · iexact H
    · iexact H'
  ipureintro
  have hrL : r < L.length := (List.getElem?_eq_some_iff.mp h).1
  have hrL' : r < L'.length := (List.getElem?_eq_some_iff.mp h').1
  have e : L[r]? = L'[r]? := by
    rcases Hp with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [List.getElem?_append_left hrL]
    · rw [List.getElem?_append_left hrL']
  rw [h, h'] at e
  simp at e
  exact e

end rev

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An event's facts at revision `r`** (persistent): a put at `r`, its key-value's value `v`, the
pair one of the plan's `P`, and `R r key v` (`revAt E` at one server). -/
def evFactR (R : Nat → GoString → GoString → IProp GF) (P : List (GoString × GoString)) (r : Nat) (e : EvModel) :
    IProp GF :=
  iprop(⌜e.typ = W32 0 ∧ sint.Z e.rev = r⌝ ∗ ∃ (v : GoString) (kvv : EtcdKv),
    kvValAt e.kv kvv ∗ ⌜kvv.value = v ∧ (e.key, v) ∈ P⌝ ∗ R r e.key v)

/-- **What `Collect` returns with `true`**, at `upTo`: the events are the puts at revisions
`2, 3, ...` (one per revision, in order), each of a key and value of the plan `P`, at least up to
`upTo`, and fewer than `2 ^ 63 - 1`; each the put `R` has at its revision. -/
def collectOk (R : Nat → GoString → GoString → IProp GF) (P : List (GoString × GoString))
    (upTo : w64) (evs : List wev) : IProp GF :=
  iprop(⌜(upTo = W64 0 ∨ sint.Z upTo ≤ 1 + evs.length) ∧ evs.length + 1 < 2 ^ 63 ∧
      ∀ (i : Nat) (e : wev), evs[i]? = some e →
        e.Put' = true ∧ sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ P⌝ ∗
    □ ∀ (i : Nat) (e : wev), ⌜evs[i]? = some e⌝ -∗ R (2 + i) e.Key' e.Val')

/-- **Receiving from a client watch channel** (`etcdWatch_recv_au` as a triple). -/
theorem wp_etcdWatch_receive [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF]
    (ch : Loc) (γ : EtcdWatchNames) (pfx : GoString) (n : Nat) (cursor : w64) :
    {{ isEtcdWatchChan ch γ pfx ∗ etcdWatchConsumer γ n cursor }}
      (App (Val (chan.receive go_etcd_io.etcd.client.v3.WatchResponse.ty)) (Val #ch))
    {{ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(|==> ∃ (r : RespModel) (c' : w64), respAt (GF := GF) v r ∗
            watchRespOk pfx cursor c' v r ∗ etcdWatchConsumer γ (n + 1) c')
         else iprop(⌜v = zero_val go_etcd_io.etcd.client.v3.WatchResponse⌝)) }} := by
  iintro %Φ ⟨#Hw, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.spsc.chanName go_etcd_io.etcd.client.v3.WatchResponse $$ [Hw]
  · iunfold isEtcdWatchChan at Hw
    icases Hw with ⟨%Pw, #Hsp, -⟩
    iunfold isSpsc at Hsp; icases Hsp with ⟨$, -⟩
  iapply chan.wp_receive ch γ.spsc.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply etcdWatch_recv_au ch γ pfx n cursor (fun v ok => Φ (PairV #v #ok)) $$ Hw [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

/-- The close error of a response etcd's watch contract allows is one grpc's `status` accepts (as
the cache's `watchRespOk_closeErr`). -/
theorem watchRespOk_closeErr' [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF]
    (pfx : GoString) (k k' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    watchRespOk (GF := GF) pfx k k' v r ⊢ go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr' := by
  unfold watchRespOk
  iintro (⟨%H, #He⟩ | %H | ⟨%H, -⟩ | ⟨%H, -⟩)
  · iexact He
  all_goals
    have hn : v.closeErr' = GoInterface.nil :=
      Classical.byContradiction fun h => H.1 (Or.inl h)
    rw [hn]; iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil

end facts

end common
end EtcdGrove
end Perennial
