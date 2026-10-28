/-
**watchkv's invariant over etcd's KV state, and the writers' vocabulary** (D23, 2026-10-20; over
the KV's specs, without the clients' model, 2026-10-26). Lean-first (no Rocq counterpart).

The program sees etcd through the client's KV and watch specs only (`isKv`, `isKvWatcher`, their
updates over the KV state `etcdKV γk σ`); its own invariant (`wkInv γk γc P`) holds the state's
half, the list of its changes (`monoListAuthOwn γc`: append-only, every change of the KV being a
writer's update firing here) and the plan's fact (`wkW P`, `Workload.lean`: every change a put of
the plan `P`).

* `wk_write_au`: a writer's put of a pair of the plan, as `Writer`'s update (`kvOpAu1`): it learns
  the changes after it (`wkWriteQ`: the state's, then the put's revision). With the reply's facts
  (`σ.rev + 4 < 2 ^ 63`, `kvLogOk σ`, `Writer.spec`), what the program knows of the Put it logged
  (`okFactW_of_write`).
* `wk_read_au`: the watch's read update (`kvReadAu`, `watcher.Watch.spec`'s): the state read is one
  of a watchkv log, its changes seen (`wkReadQ`).
* `wkRevAt γc r k v`: revision `r` of a state the program saw (a lower bound `l` of the changes,
  the log `[] :: l`) is the put of `k ↦ v` (no lease); two agree (`wkRevAt_agree`: the lower bounds
  are in prefix order). `okFactW γc p`: a logged Put's (its reply's header revision, key and
  value): the revision is at least `2` and is that put.
* `checkOk_of_wk`: `Check`'s premise from what `Collect` returns at `wkRevAt γc` and the
  successful Puts' `okFactW`s.

(Until 2026-10-26, D48, the state's half was in the adapter's invariant `client.kmInv` of the
clients' model of etcd, at the plan's fact; cachekv still is, `cachekv/Writes.lean`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WritesF
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLogOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The put of `k ↦ v` with no options appends its one change. -/
theorem kvOpStep_put_changes (k v : GoString) (σ : KVState) :
    (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ).changes =
      σ.changes ++ [[mvcc.Change.put k v (W64 0)]] := by
  have hnp : txn.needsPrev (txn.putOpOf k v (W64 0) false false false) = false := by
    simp [txn.needsPrev, txn.putOpOf]
  have hlm : ¬ σ.leaseMissing (txn.putOpOf k v (W64 0) false false false).leaseID := by
    simp [txn.putOpOf, KVState.leaseMissing]
  simp only [kvOpStep, hlm, hnp, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    KVState.commit, List.cons_ne_nil]
  simp [txn.putChangeOf, txn.putValOf, txn.putLeaseOf, txn.putOpOf]

/-- A well-formed state's log starts at revision `0`. -/
theorem kvLogOkTo_compacted {σ : KVState} {r : Nat} (h : kvLogOkTo σ r) : σ.compacted = 0 := by
  rw [h.1]; rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A writer's put: the key and value, no options. -/
theorem putWireOf_plain (k v : GoString) :
    putWireOf (opPutModel k v []) = txn.putOpOf k v (W64 0) false false false := rfl

/-! ## The invariant -/

/-- watchkv's namespace. -/
def wkN : Namespace := nroot .@ "watchkv_kv"

theorem wkN_mask : (↑wkN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- **watchkv's invariant** (see the file header). -/
def wkInv (γk : KVNames) (γc : GName) (P : List (GoString × GoString)) : IProp GF :=
  inv wkN iprop(∃ σ : KVState, etcdKV γk σ ∗ monoListAuthOwn γc 1 σ.changes ∗ ⌜wkW P σ.changes⌝)

instance wkInv_persistent (γk : KVNames) (γc : GName) (P : List (GoString × GoString)) :
    Persistent (wkInv (GF := GF) γk γc P) := by
  unfold wkInv; infer_instance

/-- **The invariant's start**, from the KV state's half, the plan's fact true of its changes. -/
theorem wkInv_alloc (γk : KVNames) (σ0 : KVState) (P : List (GoString × GoString))
    (hW : wkW P σ0.changes) :
    etcdKV (GF := GF) γk σ0 ⊢ |={⊤}=> ∃ γc : GName, wkInv γk γc P := by
  iintro Hσ
  imod (mono_list_own_alloc (GF := GF) σ0.changes) with ⟨%γc, Hc, -⟩
  imod (inv_alloc wkN ⊤ iprop(∃ σ : KVState, etcdKV (GF := GF) γk σ ∗
      monoListAuthOwn γc 1 σ.changes ∗ ⌜wkW P σ.changes⌝)) $$ [Hσ Hc] with #Hinv
  · inext
    iexists σ0
    iframe
    ipureintro; exact hW
  imodintro
  iexists γc
  unfold wkInv
  iexact Hinv

/-! ## Revisions the program saw -/

/-- **Revision `r` of a state the program saw is the put of `k ↦ v`** (persistent). -/
def wkRevAt (γc : GName) (r : Nat) (k v : GoString) : IProp GF :=
  iprop(∃ l : List (List mvcc.Change), monoListLbOwn γc l ∗
    ⌜([] :: l : mvcc.Log)[r]? = some [mvcc.Change.put k v (W64 0)]⌝)

instance wkRevAt_persistent (γc : GName) (r : Nat) (k v : GoString) :
    Persistent (wkRevAt (GF := GF) γc r k v) := by
  unfold wkRevAt; infer_instance

/-- **Two `wkRevAt`s of one revision agree.** -/
theorem wkRevAt_agree (γc : GName) (r : Nat) (k v k' v' : GoString) :
    wkRevAt (GF := GF) γc r k v ∗ wkRevAt γc r k' v' ⊢ ⌜k = k' ∧ v = v'⌝ := by
  unfold wkRevAt
  iintro ⟨⟨%l, #H, %h⟩, ⟨%l', #H', %h'⟩⟩
  ihave %Hp := mono_list_lb_valid γc l l' $$ H H'
  ipureintro
  have hp : ([] :: l : mvcc.Log) <+: [] :: l' ∨ ([] :: l' : mvcc.Log) <+: [] :: l :=
    Hp.imp (List.prefix_cons_inj _).2 (List.prefix_cons_inj _).2
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
def okFactW (γc : GName) (p : wrec) : IProp GF :=
  iprop(⌜2 ≤ sint.Z p.Rev'⌝ ∗ wkRevAt γc (sint.Z p.Rev').toNat p.Key' p.Val')

instance okFactW_persistent (γc : GName) (p : wrec) : Persistent (okFactW (GF := GF) γc p) := by
  unfold okFactW; infer_instance

/-! ## The updates -/

/-- **What a writer's put learns**: the changes after it (the state's, then the put's), and the
plan's fact of the state's. -/
def wkWriteQ (γc : GName) (P : List (GoString × GoString)) (k v : GoString) (σ : KVState) :
    IProp GF :=
  iprop(monoListLbOwn γc (σ.changes ++ [[mvcc.Change.put k v (W64 0)]]) ∗ ⌜wkW P σ.changes⌝)

/-- **A writer's put of a pair of the plan** (`Writer`'s update; see the file header). -/
theorem wk_write_au (γk : KVNames) (γc : GName) (P : List (GoString × GoString)) (k v : GoString)
    (hkv : (k, v) ∈ P) :
    wkInv (GF := GF) γk γc P ⊢
      kvOpAu1 γk (.put (putWireOf (opPutModel k v []))) (wkWriteQ γc P k v) := by
  have Hm := wkN_mask
  iintro #Hinv
  rw [putWireOf_plain]
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc
  iunfold wkInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hc, %HW⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑wkN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ; iframe; ipureintro; exact HW
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    have hch := kvOpStep_put_changes k v σ
    imod (monoListAuthOwn_update (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false))
      σ).changes (by rw [hch]; exact List.prefix_append _ _)) $$ Hc with ⟨Hc, #Hlb⟩
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists _; iframe; ipureintro; exact wkW_put P k v hkv σ HW
    imodintro
    unfold wkWriteQ
    rw [hch] at *
    iframe Hlb
    ipureintro; exact HW

/-- **A logged Put's fact** from its update's and its reply's (`Writer.spec`'s conversion): the
reply's header revision `σ.rev + 1` is the put's revision of the changes after it. -/
theorem okFactW_of_write (γc : GName) (P : List (GoString × GoString)) (k v : GoString)
    (σ : KVState) :
    wkWriteQ (GF := GF) γc P k v σ -∗ ⌜σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ⌝ -∗
      okFactW γc ⟨W64 ((σ.rev + 1 : Nat) : Int), k, v⟩ := by
  unfold wkWriteQ
  iintro ⟨#Hlb, %HW⟩ %Hok
  obtain ⟨h63, hok⟩ := Hok
  have hc := kvLogOkTo_compacted hok
  have hrev : σ.rev = σ.changes.length := by simp [KVState.rev, hc]
  have hne := List.length_pos_iff.2 HW.2
  have hz : sint.Z (W64 ((σ.rev + 1 : Nat) : Int)) = σ.rev + 1 := by word
  unfold okFactW wkRevAt
  simp only
  rw [hz]
  isplitr
  · ipureintro; omega
  iexists _
  iframe Hlb
  ipureintro
  rw [show ((σ.rev : Int) + 1).toNat = σ.changes.length + 1 by omega, ← List.cons_append,
    List.getElem?_append_right (by simp)]
  simp

/-- **What the watch's read learns**: the state read is one the program saw, of a watchkv log. -/
def wkReadQ (γc : GName) (P : List (GoString × GoString)) (σ : KVState) : IProp GF :=
  iprop(monoListLbOwn γc σ.changes ∗ ⌜wkW P σ.changes⌝)

instance wkReadQ_persistent (γc : GName) (P : List (GoString × GoString)) (σ : KVState) :
    Persistent (wkReadQ (GF := GF) γc P σ) := by
  unfold wkReadQ; infer_instance

/-- **The watch's read update** (`watcher.Watch.spec`'s; see the file header). -/
theorem wk_read_au (γk : KVNames) (γc : GName) (P : List (GoString × GoString)) :
    wkInv (GF := GF) γk γc P ⊢ kvReadAu γk (wkReadQ γc P) := by
  have Hm := wkN_mask
  iintro #Hinv
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold wkInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hc, %HW⟩
  ihave #Hlb := monoListLbOwn_get γc 1 σ.changes $$ Hc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑wkN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ; iframe; ipureintro; exact HW
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ; iframe; ipureintro; exact HW
    imodintro
    imodintro
    unfold wkReadQ
    iframe Hlb
    ipureintro; exact HW

/-! ## The check -/

/-- **The check's premise** (`CheckOk`), from what `collect` returns at `upTo` (`collectOk` at
`wkRevAt γc`) and the successful Puts' facts (`okFactW`), their revisions at most `upTo`: each
Put's revision is a watched event's, whose key and value are the Put's (`wkRevAt_agree`). -/
theorem checkOk_of_wk
    (γc : GName) (trs : List wkv) (upTo : w64) (evs : List wev) (oks : List wrec)
    (hup : ∀ p ∈ oks, sint.Z p.Rev' ≤ sint.Z upTo) :
    common.collectOk (wkRevAt (GF := GF) γc) (trs.map pairOf) upTo evs ∗
        □ ([∗list] p ∈ oks, okFactW γc p) ⊢
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
      ihave Hf := BigSepL.bigSepL_lookup (Φ := fun _ p => okFactW (GF := GF) γc p) hk $$ Hoks
      iunfold okFactW at Hf
      icases Hf with ⟨%h2, #Hra⟩
      have hle := hup p hp
      have hlt : (sint.Z p.Rev' - 2).toNat < evs.length := by
        rcases hup0 with h0 | h0
        · rw [h0] at hle; simp at hle; omega
        · omega
      obtain ⟨e, he⟩ : ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : 2 + (sint.Z p.Rev' - 2).toNat = (sint.Z p.Rev').toNat := by omega
      ihave #He : wkRevAt γc (sint.Z p.Rev').toNat e.Key' e.Val' $$ []
      · rw [← hidx]; iapply Hrevs; ipureintro; exact he
      ihave %Hag := wkRevAt_agree γc (sint.Z p.Rev').toNat e.Key' e.Val' p.Key' p.Val' $$ [He Hra]
      · iframe #
      ipureintro; intro _; exact ⟨h2, e, he, Hag.1, Hag.2⟩
    · ipureintro; intro h; exact absurd h hp
  ipureintro
  exact ⟨hlen, hevs, H⟩

end defs

end watchkv
end EtcdGrove
end Perennial
