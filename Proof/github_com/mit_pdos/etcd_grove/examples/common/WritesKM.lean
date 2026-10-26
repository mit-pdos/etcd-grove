/-
**The writers' log, at the clients' model of etcd over its KV state** (D48, 2026-10-26).
Lean-first (no Rocq counterpart).

`Writes.lean`'s vocabulary with the facts about the KV state the client saw (the adapter of
`client/v3/EtcdModelKV.lean`, its names `γ : client.KMNames`) instead of the server's sealed logs:

* `kmRevAt γ r k v`: revision `r` of a state the client saw (its changes' lower bound `l`, the log
  `[] :: l`) is the put of `k ↦ v` (no lease); two agree (`kmRevAt_agree`: the lower bounds are in
  prefix order).
* `okFactKM γ p`: what the program knows of a successful Put it logged, `p` (its reply's header
  revision, key and value): the revision is at least `2` and is the put of the key and value
  (`kmRevAt`), from the reply with the adapter's write update (`okFactKM_of_reply`: `putReplied`'s
  state, `kmWriteQ`'s lower bound of the changes after).
* `wsInvKM w γ`: the lock invariant of the log `w` (a `Writes`): its slice of successful Puts, each
  with `okFactKM`.
* `checkOk_of_km`: `Check`'s premise from what `Collect` returns at `kmRevAt γ` and the successful
  Puts' `okFactKM`s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase
public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- The put of `k ↦ v` with no options appends its one change. -/
theorem kvOpStep_putKeyOp_changes (k v : GoString) (σ : KVState) :
    (kvOpStep (.put (client.putKeyOp k v)) σ).changes =
      σ.changes ++ [[mvcc.Change.put k v (W64 0)]] := by
  have hnp : txn.needsPrev (txn.putOpOf k v (W64 0) false false false) = false := by
    simp [txn.needsPrev, txn.putOpOf]
  simp only [client.putKeyOp, kvOpStep, hnp, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    KVState.commit, List.cons_ne_nil]
  simp [txn.putChangeOf, txn.putValOf, txn.putLeaseOf, txn.putOpOf]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Revision `r` of a state the client saw is the put of `k ↦ v`** (persistent). -/
def kmRevAt (γ : client.KMNames) (r : Nat) (k v : GoString) : IProp GF :=
  iprop(∃ l : List (List mvcc.Change), monoListLbOwn γ.ch l ∗
    ⌜([] :: l : mvcc.Log)[r]? = some [mvcc.Change.put k v (W64 0)]⌝)

instance kmRevAt_persistent (γ : client.KMNames) (r : Nat) (k v : GoString) :
    Persistent (kmRevAt (GF := GF) γ r k v) := by
  unfold kmRevAt; infer_instance

/-- **Two `kmRevAt`s of one revision agree.** -/
theorem kmRevAt_agree (γ : client.KMNames) (r : Nat) (k v k' v' : GoString) :
    kmRevAt (GF := GF) γ r k v ∗ kmRevAt γ r k' v' ⊢ ⌜k = k' ∧ v = v'⌝ := by
  unfold kmRevAt
  iintro ⟨⟨%l, #H, %h⟩, ⟨%l', #H', %h'⟩⟩
  ihave %Hp := mono_list_lb_valid γ.ch l l' $$ H H'
  ipureintro
  have hp : ([] :: l : mvcc.Log) <+: [] :: l' ∨ ([] :: l' : mvcc.Log) <+: [] :: l :=
    Hp.imp client.log_prefix_of client.log_prefix_of
  have hrL : r < ([] :: l : mvcc.Log).length := (List.getElem?_eq_some_iff.mp h).1
  have hrL' : r < ([] :: l' : mvcc.Log).length := (List.getElem?_eq_some_iff.mp h').1
  have e : ([] :: l : mvcc.Log)[r]? = ([] :: l' : mvcc.Log)[r]? := by
    rcases hp with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [← ht, List.getElem?_append_left hrL]
    · rw [← ht, List.getElem?_append_left hrL']
  rw [h, h'] at e
  simp at e
  exact e

/-- **What the program knows of a successful Put it logged** (persistent; see the file header). -/
def okFactKM (γ : client.KMNames) (p : wrec) : IProp GF :=
  iprop(⌜2 ≤ sint.Z p.Rev'⌝ ∗ kmRevAt γ (sint.Z p.Rev').toNat p.Key' p.Val')

instance okFactKM_persistent (γ : client.KMNames) (p : wrec) :
    Persistent (okFactKM (GF := GF) γ p) := by
  unfold okFactKM; infer_instance

variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A successful Put's reply with the adapter's write update gives `okFactKM`** of its revision,
key and value: the update fired at the state of the reply's log `x.log`, whose revision the reply's
header is one past, and the changes after end with the put's. -/
theorem okFactKM_of_reply (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (k v : GoString)
    (γ : client.KMNames) (l0 : List (List mvcc.Change)) (cid mid : w64) (m : PutRespM) :
    client.putReplied E γr F (client.putKeyOp k v)
        (client.kmWriteQ γ l0 (.put (client.putKeyOp k v))) cid mid m ⊢
      okFactKM γ ⟨m.hdr.revision, k, v⟩ := by
  iintro H
  unfold client.putReplied
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, -, -, -, -, HQ⟩
  obtain ⟨-, hrev, -, -, -, -, h2, h4⟩ := Hp
  iunfold client.kmWriteQ at HQ
  icases HQ with ⟨#Hlb, -⟩
  have hz : sint.Z (W64 (x.log.length : Int)) = x.log.length := by word
  unfold okFactKM kmRevAt
  simp only
  rw [hrev, hz]
  isplitr
  · ipureintro; omega
  iexists _
  iframe Hlb
  ipureintro
  have hc : (kvStateOf x.log).changes = x.log.drop 1 := rfl
  rw [kvOpStep_putKeyOp_changes, hc]
  have hlen : ([] :: x.log.drop 1 : mvcc.Log).length = x.log.length := by
    simp; omega
  rw [show (x.log.length : Int).toNat = x.log.length by omega, ← List.cons_append,
    List.getElem?_append_right (by omega), hlen]
  simp

/-- **The log's lock invariant** (see the file header). -/
def wsInvKM (w : Loc) (γ : client.KMNames) : IProp GF :=
  iprop(∃ (sl : GoSlice) (oks : List wrec),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Ok" w ↦ sl ∗
    sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗
    □ [∗list] p ∈ oks, okFactKM γ p)

/-- **The check's premise** (`CheckOk`), from what `collect` returns at `upTo` (`collectOk` at
`kmRevAt γ`) and the successful Puts' facts (`okFactKM`), their revisions at most `upTo`: each
Put's revision is a watched event's, whose key and value are the Put's (`kmRevAt_agree`). -/
theorem checkOk_of_km
    (γ : client.KMNames) (trs : List wkv) (upTo : w64) (evs : List wev) (oks : List wrec)
    (hup : ∀ p ∈ oks, sint.Z p.Rev' ≤ sint.Z upTo) :
    common.collectOk (kmRevAt (GF := GF) γ) (trs.map pairOf) upTo evs ∗ □ ([∗list] p ∈ oks, okFactKM γ p) ⊢
      ⌜CheckOk evs trs oks⌝ := by
  unfold common.collectOk
  iintro ⟨⟨%Hc, #Hrevs⟩, #Hoks⟩
  obtain ⟨hup0, hlen, hevs⟩ := Hc
  ihave %H : ⌜∀ p, p ∈ oks → 2 ≤ sint.Z p.Rev' ∧ ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e ∧
      e.Key' = p.Key' ∧ e.Val' = p.Val'⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %p
    by_cases hp : p ∈ oks
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
      ihave Hf := BigSepL.bigSepL_lookup (Φ := fun _ p => okFactKM (GF := GF) γ p) hk $$ Hoks
      iunfold okFactKM at Hf
      icases Hf with ⟨%h2, #Hra⟩
      have hle := hup p hp
      have hlt : (sint.Z p.Rev' - 2).toNat < evs.length := by
        rcases hup0 with h0 | h0
        · rw [h0] at hle; simp at hle; omega
        · omega
      obtain ⟨e, he⟩ : ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : 2 + (sint.Z p.Rev' - 2).toNat = (sint.Z p.Rev').toNat := by omega
      ihave #He : kmRevAt γ (sint.Z p.Rev').toNat e.Key' e.Val' $$ []
      · rw [← hidx]; iapply Hrevs; ipureintro; exact he
      ihave %Hag := kmRevAt_agree γ (sint.Z p.Rev').toNat e.Key' e.Val' p.Key' p.Val' $$ [He Hra]
      · iframe #
      ipureintro; intro _; exact ⟨h2, e, he, Hag.1, Hag.2⟩
    · ipureintro; intro h; exact absurd h hp
  ipureintro
  exact ⟨hlen, hevs, H⟩

end defs

end common
end EtcdGrove
end Perennial
