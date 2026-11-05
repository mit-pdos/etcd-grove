/-
Lean-first (no Rocq counterpart).

# The store's transactions are the model's steps (`StepOk`, D30h, `notes/k8s-etcd3-plan.md` phase 4)

On etcd's states that are the store's, each transaction the store sends moves the model as its
operation (`Model.lean`'s `absK_*` at the level of linkv's model, lifted to etcd's `kvOpStep` by
linkv's `absSt_kvOpStep`), and keeps the store's states (`KWf_*`, sortedness by
`kvOpStep_sorted`):

- `stepOk_create`: `Create`'s `OptimisticPut(key, value, 0)` of a value that reads as the object,
  canonically, is the model's `create`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.FirstRead
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.State
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.TxnModelKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Enc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- `OptimisticPut`'s transaction is linkv's `putTxn` on the wire. -/
theorem kvOpStep_optPut (k v : GoString) (rev : w64) (g : Bool) (σ : KVState) :
    kvOpStep (.txn (kubernetes.optPutTxn k v rev g)) σ =
      kvOpStep (linkv.opOf [] [] (putTxn k v rev g)) σ := by
  cases g <;> rfl

/-- **`Create`'s transaction is the model's `create`.** -/
theorem stepOk_create (c : StoreCfg GF Obj) (pk v : GoString) (o : Obj) (hpk : c.pfx <+: pk)
    (hv : c.S.dec v = some (o, true)) :
    StepOk c (.txn (kubernetes.optPutTxn pk v (W64 0) false))
      (fun s => (s.create (E := Empty) pk o 0).1) := by
  intro σ hwf hb
  have hs := hwf.1
  have habs := linkv.absSt_kvOpStep [] [] [] σ hs (putTxn pk v (W64 0) false)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact linkv.kvOpStep_sorted _ σ
  · rw [kvOpStep_optPut, habs]
    exact KWf_putTxn c.S.dec c.pfx [] (linkv.absSt σ) hwf.2 hb pk v (W64 0) false
      (fun _ => by rw [hv]; rfl)
  · unfold StoreCfg.abs
    rw [kvOpStep_optPut, habs]
    exact (absK_create c.S.dec c.pfx [] (linkv.absSt σ) hwf.2 pk v o hpk hv).1

/-- **`Create`'s answer** at a state of the store: the object at the transaction's revision if it
succeeded (the key was absent), the key existing otherwise. -/
theorem create_out (c : StoreCfg GF Obj) (σ : KVState) (hwf : kvWf c σ) (pk v : GoString) (o : Obj)
    (hpk : c.pfx <+: pk) (hv : c.S.dec v = some (o, true)) :
    ((c.abs σ).create (E := Empty) pk o 0).2 =
      if (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optPutTxn pk v (W64 0) false)).1 then
        .obj o (kvOpStep (.txn (kubernetes.optPutTxn pk v (W64 0) false)) σ).rev
      else .err (.keyExists pk) := by
  have hc := (absK_create (E := Empty) c.S.dec c.pfx [] (linkv.absSt σ) hwf.2 pk v o hpk hv).2
  have hout := linkv.mStep_txn_out [] [] [] σ hwf.1 [.mod pk (W64 0)] [.put pk v] []
  have heq : putTxn pk v (W64 0) false = .txn [.mod pk (W64 0)] [.put pk v] [] := rfl
  rw [heq, hout] at hc
  unfold StoreCfg.abs
  rw [kvOpStep_optPut, heq]
  have ht : kubernetes.optPutTxn pk v (W64 0) false =
      linkv.txnOf [.mod pk (W64 0)] [.put pk v] [] := rfl
  rw [ht]
  cases hok : (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
      (linkv.txnOf [.mod pk (W64 0)] [.put pk v] [])).1
  · rw [hok] at hc
    exact hc
  · rw [hok] at hc
    exact hc

/-- **`Delete`'s model step** (`pre`, whether the preconditions hold; `validate`, the caller's
`validateDeletion`). -/
def delStep {E : Type} (key : GoString) (pre : Obj → Nat → Bool) (validate : Obj → Nat → Option E)
    (s : KSt Obj) : KSt Obj :=
  (s.delete key pre validate).1

/-- **The model's `delete` at a state where the key's key-value is the one the store read**
(`s`, read from `kv0`; at the same mod revision, so the same value) and `validateDeletion`
passed on it: the item goes, answered with the store's object at the next revision. -/
theorem delete_at {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (v kv0 : EtcdKv) (hv : mvcc.findKey key σ.kvs = some v)
    (s : OState Obj) (hs : stOfKv c kv0 s) (hval : v.value = kv0.value)
    (hmod : v.modRev = s.rev) (pre : Obj → Nat → Bool) (validate : Obj → Nat → Option E)
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : validate s.o (uint.nat s.rev) = none) :
    (c.abs σ).delete key pre validate =
      (⟨(c.abs σ).delItem key, (c.abs σ).rv + 1⟩, .obj s.o (σ.rev + 1)) := by
  obtain ⟨-, hfs, hdc, -⟩ := hs
  have hd : c.S.dec v.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hval, hfs, hdc]
  have hit := c.abs_some σ key hpk v hv _ _ hd
  unfold KSt.delete
  rw [hit]
  simp only [hmod, hpre, hok]
  rfl

/-- `OptimisticDelete`'s transaction is linkv's `delTxn` on the wire. -/
theorem kvOpStep_optDel (k : GoString) (rev : w64) (g : Bool) (σ : KVState) :
    kvOpStep (.txn (kubernetes.optDelTxn k rev g)) σ =
      kvOpStep (linkv.opOf [] [] (delTxn k rev g)) σ := by
  cases g <;> rfl

/-- **`deleteOnce`'s transaction** (`OptimisticDelete(key, r, GetOnFailure: true)`, `r` a mod
revision, so not `0`) at a state of the store: if it fails, nothing changed; if it succeeds, the
key had a key-value at mod revision `r`, and the key is gone at the next revision, a state of the
store. -/
theorem del_cases (c : StoreCfg GF Obj) (σ : KVState) (hwf : kvWf c σ)
    (hb : σ.rev + 2 < 2 ^ 63) (pk : GoString) (r : w64) (hr : r ≠ W64 0) :
    ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (kubernetes.optDelTxn pk r true)).1 =
        false → kvOpStep (.txn (kubernetes.optDelTxn pk r true)) σ = σ) ∧
    ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (kubernetes.optDelTxn pk r true)).1 =
        true → ∃ v, mvcc.findKey pk σ.kvs = some v ∧ v.modRev = r ∧
      kvWf c (kvOpStep (.txn (kubernetes.optDelTxn pk r true)) σ) ∧
      c.abs (kvOpStep (.txn (kubernetes.optDelTxn pk r true)) σ) =
        ⟨(c.abs σ).delItem pk, (c.abs σ).rv + 1⟩ ∧
      (kvOpStep (.txn (kubernetes.optDelTxn pk r true)) σ).rev = σ.rev + 1) := by
  have hs := hwf.1
  have habs := linkv.absSt_kvOpStep [] [] [] σ hs (delTxn pk r true)
  have hout := linkv.mStep_txn_out [] [] [] σ hs [.mod pk r] [.del pk] [.get pk]
  have heq : delTxn pk r true = .txn [.mod pk r] [.del pk] [.get pk] := rfl
  have ht : kubernetes.optDelTxn pk r true = linkv.txnOf [.mod pk r] [.del pk] [.get pk] := rfl
  rw [← heq] at hout
  rw [kvOpStep_optDel] at ⊢
  rw [ht]
  -- the step is the identity when the model's step is
  have hid : (linkv.mStep [] (delTxn pk r true) (linkv.absSt σ)).1 = linkv.absSt σ →
      kvOpStep (linkv.opOf [] [] (delTxn pk r true)) σ = σ := by
    intro h1
    have hrev := congrArg linkv.MSt.rev (habs.trans h1)
    rcases etcd_txnlin.kvOpStep_cases (linkv.opOf [] [] (delTxn pk r true)) σ (linkv.opOf_isKV _ _ _) with h | h
    · exact h
    · simp only [linkv.absSt] at hrev
      omega
  cases hf : mvcc.findKey pk σ.kvs with
  | none =>
    have hx : (linkv.absSt σ).kv pk = none := by simp [linkv.absSt, linkv.absM, hf]
    have hm := mStep_delTxn_none [] (linkv.absSt σ) pk r true hx hr
    rw [hm] at hout
    simp only [linkv.MOut.txn.injEq] at hout
    refine ⟨fun _ => hid (by rw [hm]), fun h => ?_⟩
    rw [h] at hout
    exact absurd hout.2.1 (by decide)
  | some v =>
    have hx : (linkv.absSt σ).kv pk = some (linkv.absVR v) := by
      simp [linkv.absSt, linkv.absM, hf]
    have hm := mStep_delTxn [] (linkv.absSt σ) pk r true (linkv.absVR v) hx
    by_cases hmr : v.modRev = r
    · have hmr' : (linkv.absVR v).mod = r := hmr
      rw [if_pos hmr'] at hm
      have hout' := hout
      rw [hm] at hout'
      simp only [linkv.MOut.txn.injEq] at hout'
      have hst : linkv.absSt (kvOpStep (linkv.opOf [] [] (delTxn pk r true)) σ) =
          ⟨(linkv.absSt σ).kv.del pk, (linkv.absSt σ).rev + 1⟩ := by rw [habs, hm]
      refine ⟨fun h => ?_, fun _ => ⟨v, rfl, hmr, ⟨linkv.kvOpStep_sorted _ σ, ?_⟩, ?_, ?_⟩⟩
      · rw [h] at hout'
        exact absurd hout'.2.1 (by decide)
      · rw [hst]
        exact KWf_del c.S.dec c.pfx (linkv.absSt σ) hwf.2 hb pk
      · unfold StoreCfg.abs
        rw [hst, absK_del]
        rfl
      · have := congrArg linkv.MSt.rev hst
        simp only [linkv.absSt] at this
        exact this
    · have hmr' : ¬ (linkv.absVR v).mod = r := hmr
      rw [if_neg hmr'] at hm
      rw [hm] at hout
      simp only [linkv.MOut.txn.injEq] at hout
      refine ⟨fun _ => hid (by rw [hm]), fun h => ?_⟩
      rw [h] at hout
      exact absurd hout.2.1 (by decide)

/-- **The key's key-values at its mod revision `s.rev` have `kv0`'s value** (what the store's
history `kvSeen` tells of a state). -/
def sameAt (key : GoString) (r : w64) (kv0 : EtcdKv) (σ : KVState) : Prop :=
  ∀ v ∈ σ.kvs, v.key = key → v.modRev = r → v.value = kv0.value

/-- **`deleteOnce`'s transaction is the model's `delete` when it succeeds**, and the identity when
it fails, at a state of the store where the key's key-value at the store's mod revision is the
one it read (`sameAt`) and `validateDeletion` passed on it. -/
theorem delStepOk {E : Type} (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key)
    (kv0 : EtcdKv) (s : OState Obj) (hs : stOfKv c kv0 s) (hr : s.rev ≠ W64 0)
    (pre : Obj → Nat → Bool) (validate : Obj → Nat → Option E)
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : validate s.o (uint.nat s.rev) = none) :
    ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → sameAt key s.rev kv0 σ →
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optDelTxn key s.rev true)).1 = true →
        kvWf c (kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ) ∧
        c.abs (kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ) =
          delStep key pre validate (c.abs σ)) ∧
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optDelTxn key s.rev true)).1 = false →
        kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ = σ) := by
  intro σ hwf hb hsame
  have hc := del_cases c σ hwf hb key s.rev hr
  refine ⟨fun h => ?_, hc.1⟩
  obtain ⟨v, hv, hm, hwf', habs, -⟩ := hc.2 h
  refine ⟨hwf', ?_⟩
  rw [habs]
  unfold delStep
  have hval := hsame v (mvcc.findKey_mem hv) (mvcc.findKey_key hv) hm
  rw [delete_at c σ key hpk v kv0 hv s hs hval hm pre validate hpre hok]

/-- A failed transaction's key-value of the key (`GetOnFailure`'s range) is the key's, in a
state sorted by key. -/
theorem single_filter (k : GoString) (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) :
    kubernetes.single (s.filter fun v => decide (v.key = k)) = mvcc.findKey k s := by
  cases h : mvcc.findKey k s with
  | none => rw [client.filter_key_of_findKey_none k s h]; rfl
  | some kv => rw [client.filter_key_of_findKey k s hs kv h]; rfl

/-- **The model's `delete` of a key the state lacks**: "not found" at its revision, nothing
changed. -/
theorem delete_none {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hv : mvcc.findKey key σ.kvs = none) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E) :
    (c.abs σ).delete key pre validate = (c.abs σ, .err (.notFound key σ.rev)) := by
  unfold KSt.delete
  rw [c.abs_none σ key hv]
  rfl

/-- **The model's `delete` when `validateDeletion` fails on the stored object**: its error,
nothing changed. -/
theorem delete_invalid {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (kv : EtcdKv) (hv : mvcc.findKey key σ.kvs = some kv)
    (s : OState Obj) (hs : stOfKv c kv s) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E) (hpre : pre s.o (uint.nat s.rev) = true) (e : E)
    (he : validate s.o (uint.nat s.rev) = some e) :
    (c.abs σ).delete key pre validate = (c.abs σ, .err (.user e)) := by
  obtain ⟨hrev, hfs, hdc, -⟩ := hs
  have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hfs, hdc]
  have hit := c.abs_some σ key hpk kv hv _ _ hd
  unfold KSt.delete
  rw [hit]
  simp only [← hrev, hpre, he]

/-- **The caller's `validateDeletion`** (persistent: called at each retry): on an object holding
`o` at resource version `r`, it leaves it and answers `validate o r` (`nil` for `none`). -/
def validateOk {E : Type} [KUserErr E] (c : StoreCfg GF Obj) (validate : Obj → Nat → Option E) (vf : GoFunc) :
    IProp GF :=
  iprop(□ ∀ (ctx x : GoInterface) (o : Obj) (r : w64) (Ψ : val → IProp GF),
    c.S.objAt x o (c.S.fmtRV r) -∗
    ▷ (∀ err : GoInterface, c.S.objAt x o (c.S.fmtRV r) -∗
        ⌜match validate o (uint.nat r) with
          | none => err = GoInterface.nil
          | some e => err ≠ GoInterface.nil ∧ KUserErr.is e err⌝ -∗ Ψ #err) -∗
    WP (App (App (Val #vf) (Val #ctx)) (Val #x)) {{ Ψ }})

instance validateOk_persistent {E : Type} [KUserErr E] (c : StoreCfg GF Obj) (validate : Obj → Nat → Option E)
    (vf : GoFunc) : Persistent (validateOk c validate vf) := by
  unfold validateOk; infer_instance

/-- **`Delete`'s outcome** for the prepared key `key`: an error whose outcome is unknown
(`unkErr`: the client's, the update fired at most once); or the model's `delete` at the state `σ`
the caller's update fired at as the linearization point (`Φ σ`, D30n: the write, or a read-like
answer at a state where the step is the identity). -/
def delOut {E : Type} [KUserErr E] (c : StoreCfg GF Obj) (key : GoString)
    (pre : Obj → Nat → Bool) (validate : Obj → Nat → Option E)
    (Φ : KVState → IProp GF) (err out : GoInterface) : IProp GF :=
  iprop((unkErr c err ∗ ∃ o rv, c.S.objAt out o rv) ∨
    (∃ σ, Φ σ ∗ respIs c ((c.abs σ).delete key pre validate).2 err out))

/-- **`GuaranteedUpdate`'s model step** (`ign`, `ignoreNotFound`; `z`, the zero object; `pre`,
whether the preconditions hold; `f`, the caller's `tryUpdate`). -/
def updStep {E : Type} (key : GoString) (ign : Bool) (z : Obj) (pre : Obj → Nat → Bool)
    (f : Obj → Nat → Except E Obj) (s : KSt Obj) : KSt Obj :=
  (s.update key ign z pre f).1

/-- **`updateOnce`'s transaction** (`OptimisticPut(key, v, r, GetOnFailure: true)`, `r` a mod
revision, so not `0`, `v` a value that decodes) at a state of the store: if it fails, nothing
changed; if it succeeds, the key had a key-value at mod revision `r`, and holds `v` at the next
revision, a state of the store. -/
theorem put_cases (c : StoreCfg GF Obj) (σ : KVState) (hwf : kvWf c σ)
    (hb : σ.rev + 2 < 2 ^ 63) (pk v : GoString) (r : w64) (hr : r ≠ W64 0)
    (hv : c.pfx <+: pk → (c.S.dec v).isSome) :
    ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (kubernetes.optPutTxn pk v r true)).1 =
        false → kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ = σ) ∧
    ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (kubernetes.optPutTxn pk v r true)).1 =
        true → ∃ w, mvcc.findKey pk σ.kvs = some w ∧ w.modRev = r ∧
      kvWf c (kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ) ∧
      linkv.absSt (kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ) =
        ⟨(linkv.absSt σ).kv.put ((linkv.absSt σ).rev + 1) pk v, (linkv.absSt σ).rev + 1⟩ ∧
      (kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ).rev = σ.rev + 1) := by
  have hs := hwf.1
  have habs := linkv.absSt_kvOpStep [] [] [] σ hs (putTxn pk v r true)
  have hout := linkv.mStep_txn_out [] [] [] σ hs [.mod pk r] [.put pk v] [.get pk]
  have heq : putTxn pk v r true = .txn [.mod pk r] [.put pk v] [.get pk] := rfl
  have ht : kubernetes.optPutTxn pk v r true = linkv.txnOf [.mod pk r] [.put pk v] [.get pk] := rfl
  rw [← heq] at hout
  rw [kvOpStep_optPut] at ⊢
  rw [ht]
  have hid : (linkv.mStep [] (putTxn pk v r true) (linkv.absSt σ)).1 = linkv.absSt σ →
      kvOpStep (linkv.opOf [] [] (putTxn pk v r true)) σ = σ := by
    intro h1
    have hrev := congrArg linkv.MSt.rev (habs.trans h1)
    rcases etcd_txnlin.kvOpStep_cases (linkv.opOf [] [] (putTxn pk v r true)) σ (linkv.opOf_isKV _ _ _) with h | h
    · exact h
    · simp only [linkv.absSt] at hrev
      omega
  have hm := mStep_putTxn [] (linkv.absSt σ) pk v r true
  by_cases hmr : modOf (linkv.absSt σ).kv pk = r
  · rw [if_pos hmr] at hm
    have hout' := hout
    rw [hm] at hout'
    simp only [linkv.MOut.txn.injEq] at hout'
    have hst : linkv.absSt (kvOpStep (linkv.opOf [] [] (putTxn pk v r true)) σ) =
        ⟨(linkv.absSt σ).kv.put ((linkv.absSt σ).rev + 1) pk v, (linkv.absSt σ).rev + 1⟩ := by
      rw [habs, hm]
    refine ⟨fun h => ?_, fun _ => ?_⟩
    · rw [h] at hout'
      exact absurd hout'.2.1 (by decide)
    · cases hf : mvcc.findKey pk σ.kvs with
      | none =>
        exfalso
        have : modOf (linkv.absSt σ).kv pk = W64 0 := by
          simp [modOf, linkv.absSt, linkv.absM, hf]
        exact hr (hmr.symm.trans this)
      | some w =>
        have hwm : w.modRev = r := by
          have : modOf (linkv.absSt σ).kv pk = w.modRev := by
            simp [modOf, linkv.absSt, linkv.absM, hf, linkv.absVR]
          rw [← this, hmr]
        refine ⟨w, rfl, hwm, ⟨linkv.kvOpStep_sorted _ σ, ?_⟩, hst, ?_⟩
        · rw [hst]
          exact KWf_put c.S.dec c.pfx (linkv.absSt σ) hwf.2 hb pk v hv
        · have := congrArg linkv.MSt.rev hst
          simp only [linkv.absSt] at this
          exact this
  · rw [if_neg hmr] at hm
    rw [hm] at hout
    simp only [linkv.MOut.txn.injEq] at hout
    refine ⟨fun _ => hid (by rw [hm]), fun h => ?_⟩
    rw [h] at hout
    exact absurd hout.2.1 (by decide)

/-- **The model's `update` at a state where the key's key-value is the one the store read**
(`s`, read from `kv0`; at the same mod revision, so the same value), `tryUpdate` gave `o'` on it
and the store does not skip the write (not both unchanged and canonical): the item `o'` at the
next revision, canonical. -/
theorem update_at {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (v kv0 : EtcdKv) (hv : mvcc.findKey key σ.kvs = some v)
    (s : OState Obj) (hs : stOfKv c kv0 s) (hval : v.value = kv0.value)
    (hmod : v.modRev = s.rev) (ign : Bool) (z : Obj) (pre : Obj → Nat → Bool)
    (hpre : pre s.o (uint.nat s.rev) = true) (f : Obj → Nat → Except E Obj) (o' : Obj)
    (hok : f s.o (uint.nat s.rev) = .ok o')
    (hw : (!s.stale && decide (c.S.encode o' = s.data)) = false) :
    (c.abs σ).update key ign z pre f =
      (⟨(c.abs σ).setItem key ⟨o', (c.abs σ).rv + 1, true⟩, (c.abs σ).rv + 1⟩,
        .obj o' ((c.abs σ).rv + 1)) := by
  obtain ⟨-, hfs, hdc, -⟩ := hs
  have hd : c.S.dec v.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hval, hfs, hdc]
  have hit := c.abs_some σ key hpk v hv _ _ hd
  have hn : ¬ (o' = s.o ∧ (!s.stale && decide (c.S.encode s.o = s.data)) = true) := by
    intro ⟨h1, h2⟩
    subst h1
    rw [h2] at hw
    exact absurd hw (by decide)
  unfold KSt.update KSt.current
  rw [hit]
  simp only [hmod, hpre, hok]
  rw [if_neg hn]

/-- **`updateOnce`'s transaction is the model's `update` when it succeeds**, and the identity when
it fails, at a state of the store where the key's key-value at the store's mod revision is the
one it read (`sameAt`); `v` is the store's new value for `o'` (canonical). -/
theorem updStepOk {E : Type} (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key)
    (kv0 : EtcdKv) (s : OState Obj) (hs : stOfKv c kv0 s) (hr : s.rev ≠ W64 0) (ign : Bool)
    (z : Obj) (pre : Obj → Nat → Bool) (hpre : pre s.o (uint.nat s.rev) = true)
    (f : Obj → Nat → Except E Obj) (o' : Obj) (hok : f s.o (uint.nat s.rev) = .ok o')
    (hw : (!s.stale && decide (c.S.encode o' = s.data)) = false) (v : GoString)
    (hv : c.S.dec v = some (o', true)) :
    ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → sameAt key s.rev kv0 σ →
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optPutTxn key v s.rev true)).1 = true →
        kvWf c (kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ) ∧
        c.abs (kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ) =
          updStep key ign z pre f (c.abs σ)) ∧
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optPutTxn key v s.rev true)).1 = false →
        kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ = σ) := by
  intro σ hwf hb hsame
  have hc := put_cases c σ hwf hb key v s.rev hr (fun _ => by rw [hv]; rfl)
  refine ⟨fun h => ?_, hc.1⟩
  obtain ⟨w, hw', hm, hwf', habs, -⟩ := hc.2 h
  refine ⟨hwf', ?_⟩
  unfold StoreCfg.abs
  rw [habs, absK_put c.S.dec c.pfx (linkv.absSt σ) hwf.2 key v o' hpk hv]
  unfold updStep
  have hval := hsame w (mvcc.findKey_mem hw') (mvcc.findKey_key hw') hm
  have := update_at c σ key hpk w kv0 hw' s hs hval hm ign z pre hpre f o' hok hw
  unfold StoreCfg.abs at this
  rw [this]
  rfl

/-- **The caller's `tryUpdate`** (persistent: called at each retry): on an object holding `o` at
resource version `r` (and the response metadata at `r`), it answers `f o r`: an object holding
the result (no TTL, D30d), or an error. It may keep or change the input object (it owns it). -/
def tryUpdateOk {E : Type} [KUserErr E] (c : StoreCfg GF Obj) (f : Obj → Nat → Except E Obj) (uf : GoFunc) :
    IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : Obj) (r : w64) (Ψ : val → IProp GF),
    c.S.objAt x o (c.S.fmtRV r) -∗
    ▷ (∀ (ret : GoInterface) (ttlp : Loc) (err : GoInterface),
        (match f o (uint.nat r) with
          | .ok o' => ⌜err = GoInterface.nil ∧ ttlp = null⌝ ∗ ∃ rv', c.S.objAt ret o' rv'
          | .error e => ⌜err ≠ GoInterface.nil ∧ KUserErr.is e err⌝) -∗
        Ψ (PairV (PairV #ret #ttlp) #err)) -∗
    WP (App (App (Val #uf) (Val #x))
      (Val #(k8s_io.apiserver.pkg.storage.ResponseMeta.mk (W64 0) r))) {{ Ψ }})

instance tryUpdateOk_persistent {E : Type} [KUserErr E] (c : StoreCfg GF Obj) (f : Obj → Nat → Except E Obj)
    (uf : GoFunc) : Persistent (tryUpdateOk c f uf) := by
  unfold tryUpdateOk; infer_instance

/-- **`GuaranteedUpdate`'s outcome** for the prepared key `key` (as `delOut`): an error; or the
model's `update` at the state `σ` the caller's update fired at as the linearization point (`Φ σ`:
the write, or a read-like answer: a no-op, not found, `tryUpdate`'s error). -/
def updOut {E : Type} [KUserErr E] (c : StoreCfg GF Obj) (key : GoString) (ign : Bool) (z : Obj)
    (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj) (Φ : KVState → IProp GF)
    (err out : GoInterface) : IProp GF :=
  iprop((unkErr c err ∗ ∃ o rv, c.S.objAt out o rv) ∨
    (∃ σ, Φ σ ∗ respIs c ((c.abs σ).update key ign z pre f).2 err out))

/-- **The model's `update` of a key the state lacks** (`ignoreNotFound` false): "not found",
nothing changed. -/
theorem update_none {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hv : mvcc.findKey key σ.kvs = none) (z : Obj) (pre : Obj → Nat → Bool)
    (f : Obj → Nat → Except E Obj) :
    (c.abs σ).update key false z pre f = (c.abs σ, .err (.notFound key σ.rev)) := by
  unfold KSt.update KSt.current
  rw [c.abs_none σ key hv]
  rfl

/-- **The model's `update` when `tryUpdate` fails on the stored object**: its error, nothing
changed. -/
theorem update_err {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (kv : EtcdKv) (hv : mvcc.findKey key σ.kvs = some kv)
    (s : OState Obj) (hs : stOfKv c kv s) (ign : Bool) (z : Obj) (pre : Obj → Nat → Bool)
    (hpre : pre s.o (uint.nat s.rev) = true) (f : Obj → Nat → Except E Obj) (e : E)
    (he : f s.o (uint.nat s.rev) = .error e) :
    (c.abs σ).update key ign z pre f = (c.abs σ, .err (.user e)) := by
  obtain ⟨hrev, hfs, hdc, -⟩ := hs
  have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hfs, hdc]
  have hit := c.abs_some σ key hpk kv hv _ _ hd
  unfold KSt.update KSt.current
  rw [hit]
  simp only [← hrev, hpre, he]

/-- **The model's `update` when the store skips the write** (`store.go:547`: not stale, and the
result's encoding is the stored data): the stored object at its resource version, nothing
changed (`noop_iff`: the result is the object, canonical). -/
theorem update_skip {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (kv : EtcdKv) (hv : mvcc.findKey key σ.kvs = some kv)
    (s : OState Obj) (hs : stOfKv c kv s) (ign : Bool) (z : Obj) (pre : Obj → Nat → Bool)
    (hpre : pre s.o (uint.nat s.rev) = true) (f : Obj → Nat → Except E Obj) (o' : Obj)
    (hok : f s.o (uint.nat s.rev) = .ok o')
    (hn : (!s.stale && decide (c.S.encode o' = s.data)) = true) :
    (c.abs σ).update key ign z pre f = (c.abs σ, .obj s.o (uint.nat s.rev)) := by
  obtain ⟨hrev, hfs, hdc, -⟩ := hs
  have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hfs, hdc]
  have hit := c.abs_some σ key hpk kv hv _ _ hd
  obtain ⟨heq, -⟩ := (ObjCodec.noop_iff c.S.toObjCodec kv.value s.data s.stale s.o o' hfs hdc).1 hn
  subst heq
  have hc : (!s.stale && decide (c.S.encode s.o = s.data)) = true := hn
  unfold KSt.update KSt.current
  rw [hit]
  simp only [← hrev, hpre, hok]
  simp [hc]

/-! ## Where the store hands the caller's token at a read (D30n) -/

open Classical in
/-- **The store hands the token at a read** exactly where the model's step is the identity. -/
noncomputable def stepHand (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj) (σ : KVState) : Bool :=
  decide (step (c.abs σ) = c.abs σ)

/-- A write moves the resource version, so it is not the identity. -/
theorem KSt.ne_of_rv {s : KSt Obj} {items : GoString → Option (KItem Obj)} :
    (⟨items, s.rv + 1⟩ : KSt Obj) ≠ s := fun h => by
  have := congrArg KSt.rv h
  simp at this

/-- Whether `delete` is the identity depends on the key's item only. -/
theorem delStep_loc {E : Type} (key : GoString) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E) (s1 s2 : KSt Obj) (hi : s1.items key = s2.items key) :
    delStep key pre validate s1 = s1 ↔ delStep key pre validate s2 = s2 := by
  unfold delStep KSt.delete
  rw [hi]
  cases s2.items key with
  | none => simp
  | some it =>
    simp only
    cases pre it.obj it.rv with
    | false => simp
    | true =>
      simp only
      cases validate it.obj it.rv with
      | some _ => simp
      | none => exact ⟨fun h => absurd h KSt.ne_of_rv, fun h => absurd h KSt.ne_of_rv⟩

/-- Whether `update` is the identity depends on the key's item only. -/
theorem updStep_loc {E : Type} (key : GoString) (ign : Bool) (z : Obj) (pre : Obj → Nat → Bool)
    (f : Obj → Nat → Except E Obj) (s1 s2 : KSt Obj) (hi : s1.items key = s2.items key) :
    updStep key ign z pre f s1 = s1 ↔ updStep key ign z pre f s2 = s2 := by
  unfold updStep KSt.update KSt.current
  rw [hi]
  cases h2 : s2.items key with
  | none =>
    cases ign with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      cases pre z 0 with
      | false => simp
      | true =>
        simp only
        cases f z 0 with
        | error _ => simp
        | ok o' => exact ⟨fun h => absurd h KSt.ne_of_rv, fun h => absurd h KSt.ne_of_rv⟩
  | some it =>
    simp only
    cases pre it.obj it.rv with
    | false => simp
    | true =>
      simp only
      cases f it.obj it.rv with
      | error _ => simp
      | ok o' =>
        simp only
        split
        · simp
        · exact ⟨fun h => absurd h KSt.ne_of_rv, fun h => absurd h KSt.ne_of_rv⟩

/-- **`Delete`'s handing** (`HandOk`). -/
theorem handOk_del {E : Type} (c : StoreCfg GF Obj) (key : GoString) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E) :
    HandOk c key (delStep key pre validate) (stepHand c (delStep key pre validate)) where
  id σ _ h := by simpa [stepHand] using h
  loc σ1 σ2 hi _ := by
    simp only [stepHand]
    exact decide_eq_decide.2 (delStep_loc key pre validate _ _ hi)

/-- **`GuaranteedUpdate`'s handing** (`HandOk`). -/
theorem handOk_upd {E : Type} (c : StoreCfg GF Obj) (key : GoString) (ign : Bool) (z : Obj)
    (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj) :
    HandOk c key (updStep key ign z pre f) (stepHand c (updStep key ign z pre f)) where
  id σ _ h := by simpa [stepHand] using h
  loc σ1 σ2 hi _ := by
    simp only [stepHand]
    exact decide_eq_decide.2 (updStep_loc key ign z pre f _ _ hi)

/-- `delete`'s answer depends on the key's item and the resource version only. -/
theorem delete_local {E : Type} (key : GoString) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E)
    (s1 s2 : KSt Obj) (hi : s1.items key = s2.items key) (hr : s1.rv = s2.rv) :
    (s1.delete key pre validate).2 = (s2.delete key pre validate).2 := by
  unfold KSt.delete
  rw [hi, hr]
  cases s2.items key with
  | none => rfl
  | some it =>
    simp only
    cases pre it.obj it.rv with
    | false => rfl
    | true =>
      simp only
      cases validate it.obj it.rv <;> rfl

/-- `update`'s answer depends on the key's item and the resource version only. -/
theorem update_local {E : Type} (key : GoString) (ign : Bool) (z : Obj) (pre : Obj → Nat → Bool)
    (f : Obj → Nat → Except E Obj) (s1 s2 : KSt Obj) (hi : s1.items key = s2.items key)
    (hr : s1.rv = s2.rv) :
    (s1.update key ign z pre f).2 = (s2.update key ign z pre f).2 := by
  unfold KSt.update KSt.current
  rw [hi, hr]
  cases s2.items key with
  | none =>
    cases ign with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      cases pre z 0 with
      | false => rfl
      | true =>
        simp only
        cases f z 0 <;> rfl
  | some it =>
    simp only
    cases pre it.obj it.rv with
    | false => rfl
    | true =>
      simp only
      cases f it.obj it.rv with
      | error _ => rfl
      | ok o' =>
        simp only
        split <;> rfl

/-- The model's state of a store state, its resource version: the state's revision. -/
theorem abs_rv (c : StoreCfg GF Obj) (σ : KVState) : (c.abs σ).rv = σ.rev := rfl

theorem hand_true (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj) (σ : KVState)
    (h : step (c.abs σ) = c.abs σ) : stepHand c step σ = true := by
  simp [stepHand, h]

theorem hand_false (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj) (σ : KVState)
    (h : step (c.abs σ) ≠ c.abs σ) : stepHand c step σ = false := by
  simp [stepHand, h]

/-! ## The cached object (stage 7b) -/

/-- **The key held `o` at mod revision `r`** (persistent; the cached object's witness): every
state seen in the caller's history whose key is at mod revision `r` has the item `o` there. A
caller makes it from a `kvSeen` entry for an object it was answered, or from a deletion's `none`
entry (no state has the key at that revision). -/
def versionAt (c : StoreCfg GF Obj) (key : GoString) (r : w64) (o : Obj) : IProp GF :=
  iprop(□ ∀ σ, kvSeen c.γh σ -∗ ⌜kubernetes.modAt key σ = r →
    ∃ b, (c.abs σ).items key = some ⟨o, uint.nat r, b⟩⌝)

instance versionAt_persistent (c : StoreCfg GF Obj) (key : GoString) (r : w64) (o : Obj) :
    Persistent (versionAt c key r o) := by
  unfold versionAt; infer_instance

/-- **The `cachedExistingObject` argument `x`** for the prepared key `key`: `nil` (none), or (`ca =
some (o, r)`) an object holding `o` at resource version `r ≠ 0`, owned (the store keeps it), that
the key held at `r`. -/
def cachedOk (c : StoreCfg GF Obj) (key : GoString) (x : GoInterface) :
    Option (Obj × w64) → IProp GF
  | none => iprop(⌜x = GoInterface.nil⌝)
  | some (o, r) => iprop(⌜r ≠ W64 0⌝ ∗ c.S.objAt x o (c.S.fmtRV r) ∗ versionAt c key r o)

/-- **Where the state `s` came from** (persistent): a read at `σ0` of the key's key-value, a read
at `σ0` of the absent key with `ignoreNotFound` (the zero state), or the cached object
(`getStateFromObject`: not current, not stale, its data the object's encoding). -/
def stFrom (c : StoreCfg GF Obj) (key : GoString) (s : OState Obj) : IProp GF :=
  iprop((∃ σ0 kv0, rdFacts c σ0 ∗ ⌜mvcc.findKey key σ0.kvs = some kv0 ∧ stOfKv c kv0 s⌝) ∨
    (∃ σ0, rdFacts c σ0 ∗ ⌜mvcc.findKey key σ0.kvs = none ∧ s = zeroSt c⌝) ∨
    (⌜s.current = false ∧ s.stale = false ∧ s.data = c.S.encode s.o ∧ s.rev ≠ W64 0⌝ ∗
      versionAt c key s.rev s.o))

instance stFrom_persistent (c : StoreCfg GF Obj) (key : GoString) (s : OState Obj) :
    Persistent (stFrom c key s) := by
  unfold stFrom; infer_instance

/-- **What a state tells of a state seen in the history**, where the key is at the state's mod
revision: for a state with a revision, the item is the state's object at it, canonical only if the
store's no-op test on the state's data says so; for the zero state, no item. -/
theorem stFrom_item (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key) (s : OState Obj)
    (σ : KVState) (hwf : kvWf c σ) :
    stFrom c key s ∗ kvSeen c.γh σ ⊢ ⌜kubernetes.modAt key σ = s.rev →
      (s.rev = W64 0 ∧ (c.abs σ).items key = none) ∨
      (s.rev ≠ W64 0 ∧ c.S.decode s.data = some s.o ∧ ∃ b, (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩ ∧
        (b = true → (!s.stale && decide (c.S.encode s.o = s.data)) = true))⌝ := by
  have hpos : ∀ (σ : KVState), kvWf c σ → ∀ v, mvcc.findKey key σ.kvs = some v →
      0 < uint.nat v.modRev := by
    intro σ hw v hv
    have := (hw.2.2.1 key (linkv.absVR v) (by simp [linkv.absSt, linkv.absM, hv])).1
    simpa [linkv.absVR] using this
  unfold stFrom rdFacts
  iintro ⟨#Hf, #Hs⟩
  icases Hf with (⟨%σ0, %kv0, ⟨%Hw0, #Hs0⟩, %Hk0⟩ | ⟨%σ0, -, %Hz⟩ | ⟨%Hc, #Hv⟩)
  · -- a read of the key-value `kv0`
    obtain ⟨hf0, hr0, hfs, hdec, -⟩ := Hk0
    have hk0 : kv0.key = key := by simpa using List.find?_some hf0
    ihave %Hval := kvSeen_same c.γh σ0 σ kv0 (List.mem_of_find?_eq_some hf0) $$ [Hs0 Hs]
    · iframe Hs0 Hs
    ipureintro
    intro hm
    have hm0 : kubernetes.modAt key σ0 = kv0.modRev := by simp [kubernetes.modAt, hf0]
    have hp0 := hpos σ0 Hw0.1 kv0 hf0
    have hne : s.rev ≠ W64 0 := by
      rw [hr0]; intro h; rw [h] at hp0; exact absurd hp0 (by decide)
    have heq : (c.abs σ).items key = (c.abs σ0).items key := by
      apply abs_items_eq c key σ σ0 hwf Hw0.1 (hm.trans (hr0.trans hm0.symm))
      intro v1 v2 h1 h2
      rw [hf0] at h2
      cases h2
      have hk1 : v1.key = key := by simpa using List.find?_some h1
      have hm1 : v1.modRev = kv0.modRev := by
        have := hm.trans hr0
        simpa [kubernetes.modAt, h1] using this
      exact Hval v1 (List.mem_of_find?_eq_some h1) (hk1.trans hk0.symm) hm1
    right
    refine ⟨hne, hdec, !s.stale && decide (c.S.encode s.o = s.data), ?_, fun h => h⟩
    rw [heq, hr0]
    apply StoreCfg.abs_some c σ0 key hpk kv0 hf0
    simp [ObjCodec.dec, hfs, hdec]
  · -- the absent key's zero state
    obtain ⟨-, rfl⟩ := Hz
    ipureintro
    intro hm
    left
    refine ⟨rfl, StoreCfg.abs_none c σ key ?_⟩
    cases hf : mvcc.findKey key σ.kvs with
    | none => rfl
    | some v =>
      have := hpos σ hwf v hf
      simp [kubernetes.modAt, hf, zeroSt] at hm
      rw [hm] at this
      exact absurd this (by decide)
  · -- the cached object
    obtain ⟨-, hstl, hdat, hr⟩ := Hc
    unfold versionAt
    ihave %H := Hv $$ %σ Hs
    ipureintro
    intro hm
    obtain ⟨b, hb⟩ := H hm
    right
    refine ⟨hr, by rw [hdat]; exact c.S.decode_encode _, b, hb, fun _ => by simp [hstl, hdat]⟩

/-- **A state with a revision is the key's item at it** in every state of the store seen in the
history where the key is at that mod revision (what the store's loops carry through their
transactions, from `stFrom`). -/
def itemAt (c : StoreCfg GF Obj) (key : GoString) (s : OState Obj) (σ : KVState) : Prop :=
  kvWf c σ → kubernetes.modAt key σ = s.rev →
    ∃ b, (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩

theorem stFrom_itemAt (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key) (s : OState Obj)
    (hr : s.rev ≠ W64 0) :
    stFrom c key s ⊢ □ ∀ σ, kvSeen c.γh σ -∗ ⌜itemAt c key s σ⌝ := by
  iintro #Hf !> %σ #Hs
  by_cases hwf : kvWf c σ
  · ihave %H := stFrom_item c key hpk s σ hwf $$ [Hf Hs]
    · isplitl
      · iexact Hf
      · iexact Hs
    ipureintro
    intro _ hm
    rcases H hm with ⟨h, -⟩ | ⟨-, -, b, hb, -⟩
    · exact absurd h hr
    · exact ⟨b, hb⟩
  · ipureintro
    intro h
    exact absurd h hwf

/-- `delete_at` on the item (`itemAt`) in place of the read's key-value. -/
theorem delete_item {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (s : OState Obj) (b : Bool) (hit : (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩)
    (pre : Obj → Nat → Bool) (validate : Obj → Nat → Option E)
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : validate s.o (uint.nat s.rev) = none) :
    (c.abs σ).delete key pre validate =
      (⟨(c.abs σ).delItem key, (c.abs σ).rv + 1⟩, .obj s.o (σ.rev + 1)) := by
  unfold KSt.delete
  rw [hit]
  simp only [hpre, hok]
  rfl

/-- `delStepOk` on the item (`itemAt`, from `stFrom`) in place of the read's key-value. -/
theorem delStepOk_item {E : Type} (c : StoreCfg GF Obj) (key : GoString) (s : OState Obj)
    (hr : s.rev ≠ W64 0) (pre : Obj → Nat → Bool) (validate : Obj → Nat → Option E)
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : validate s.o (uint.nat s.rev) = none) :
    ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → itemAt c key s σ →
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optDelTxn key s.rev true)).1 = true →
        kvWf c (kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ) ∧
        c.abs (kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ) =
          delStep key pre validate (c.abs σ)) ∧
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optDelTxn key s.rev true)).1 = false →
        kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ = σ) := by
  intro σ hwf hb hit
  have hc := del_cases c σ hwf hb key s.rev hr
  refine ⟨fun h => ?_, hc.1⟩
  obtain ⟨v, hv, hm, hwf', habs, -⟩ := hc.2 h
  refine ⟨hwf', ?_⟩
  rw [habs]
  unfold delStep
  obtain ⟨b, hb'⟩ := hit hwf (by simp [kubernetes.modAt, hv, hm])
  rw [delete_item c σ key s b hb' pre validate hpre hok]

/-- `delete` of an item whose preconditions fail: their error, nothing changed. -/
theorem delete_item_pre {E : Type} (st : KSt Obj) (key : GoString) (o : Obj) (r : Nat) (b : Bool)
    (hit : st.items key = some ⟨o, r, b⟩) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E) (hpre : pre o r = false) :
    st.delete key pre validate = (st, .err (.invalidObj key)) := by
  unfold KSt.delete
  rw [hit]
  simp only [hpre]

/-- `delete` of an item that `validateDeletion` rejects: its error, nothing changed. -/
theorem delete_item_val {E : Type} (st : KSt Obj) (key : GoString) (o : Obj) (r : Nat) (b : Bool)
    (hit : st.items key = some ⟨o, r, b⟩) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E) (hpre : pre o r = true) (e : E) (he : validate o r = some e) :
    st.delete key pre validate = (st, .err (.user e)) := by
  unfold KSt.delete
  rw [hit]
  simp only [hpre, he]

/-- **A read's state is where it came from** (`stFrom`'s first case), at a mod revision (a stored
key-value's, so not `0`). -/
theorem stFrom_read (c : StoreCfg GF Obj) (key : GoString) (σ : KVState) (kv : EtcdKv)
    (s : OState Obj) (hf : mvcc.findKey key σ.kvs = some kv) (hs : stOfKv c kv s) :
    rdFacts c σ ⊢ stFrom c key s ∗ ⌜s.rev ≠ W64 0⌝ := by
  iintro #Hfs
  ihave #Hfs' := Hfs
  iunfold rdFacts at Hfs'
  icases Hfs' with ⟨%Hw, -⟩
  isplitl
  · unfold stFrom
    ileft
    iexists σ, kv
    iframe Hfs
    ipureintro; exact ⟨hf, hs⟩
  · ipureintro
    have hx : (linkv.absSt σ).kv key = some (linkv.absVR kv) := by
      simp [linkv.absSt, linkv.absM, hf]
    have h0 := (Hw.1.2.2.1 key _ hx).1
    rw [hs.1]
    intro h
    simp only [linkv.absVR, h] at h0
    exact absurd h0 (by decide)

/-- **The item at a state read where the key is at the state's mod revision** (`stFrom_item`). -/
theorem stFrom_rd_item (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key) (s : OState Obj)
    (hr : s.rev ≠ W64 0) (σ : KVState) (hm : kubernetes.modAt key σ = s.rev) :
    stFrom c key s ∗ rdFacts c σ ⊢ ⌜∃ b, (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩⌝ := by
  iintro ⟨#Hf, #Hfs⟩
  iunfold rdFacts at Hfs
  icases Hfs with ⟨%Hw, #Hs⟩
  ihave %H := stFrom_item c key hpk s σ Hw.1 $$ [Hf Hs]
  · iframe Hf Hs
  ipureintro
  rcases H hm with ⟨h, -⟩ | ⟨-, -, b, hb, -⟩
  · exact absurd h hr
  · exact ⟨b, hb⟩

/-- **A read's state that `deleteOnce` will delete does not hand** (its delete writes). -/
theorem del_read_hand {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (kv : EtcdKv) (hv : mvcc.findKey key σ.kvs = some kv) (s : OState Obj)
    (hs : stOfKv c kv s) (pre : Obj → Nat → Bool) (validate : Obj → Nat → Option E)
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : validate s.o (uint.nat s.rev) = none) :
    stepHand c (delStep key pre validate) σ = false := by
  apply hand_false
  simp only [delStep, delete_at c σ key hpk kv kv hv s hs rfl hs.1.symm pre validate hpre hok]
  exact KSt.ne_of_rv

/-- `modOf` of etcd's state, read as linkv's model, is `modAt`. -/
theorem modOf_absSt (σ : KVState) (k : GoString) :
    modOf (linkv.absSt σ).kv k = kubernetes.modAt k σ := by
  cases hf : mvcc.findKey k σ.kvs with
  | none => simp [modOf, linkv.absSt, linkv.absM, kubernetes.modAt, hf]
  | some w => simp [modOf, linkv.absSt, linkv.absM, kubernetes.modAt, hf, linkv.absVR]

/-- **`updateOnce`'s transaction at any mod revision `r`** (`put_cases` without `r ≠ 0`: at `0`,
the zero state's create): if it fails, nothing changed; if it succeeds, the key was at mod
revision `r`, and holds `v` at the next revision, a state of the store. -/
theorem put_cases' (c : StoreCfg GF Obj) (σ : KVState) (hwf : kvWf c σ)
    (hb : σ.rev + 2 < 2 ^ 63) (pk v : GoString) (r : w64)
    (hv : c.pfx <+: pk → (c.S.dec v).isSome) :
    ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (kubernetes.optPutTxn pk v r true)).1 =
        false → kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ = σ) ∧
    ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (kubernetes.optPutTxn pk v r true)).1 =
        true → kubernetes.modAt pk σ = r ∧
      kvWf c (kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ) ∧
      linkv.absSt (kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ) =
        ⟨(linkv.absSt σ).kv.put ((linkv.absSt σ).rev + 1) pk v, (linkv.absSt σ).rev + 1⟩ ∧
      (kvOpStep (.txn (kubernetes.optPutTxn pk v r true)) σ).rev = σ.rev + 1) := by
  have hs := hwf.1
  have habs := linkv.absSt_kvOpStep [] [] [] σ hs (putTxn pk v r true)
  have hout := linkv.mStep_txn_out [] [] [] σ hs [.mod pk r] [.put pk v] [.get pk]
  have heq : putTxn pk v r true = .txn [.mod pk r] [.put pk v] [.get pk] := rfl
  have ht : kubernetes.optPutTxn pk v r true = linkv.txnOf [.mod pk r] [.put pk v] [.get pk] := rfl
  rw [← heq] at hout
  rw [kvOpStep_optPut] at ⊢
  rw [ht]
  have hid : (linkv.mStep [] (putTxn pk v r true) (linkv.absSt σ)).1 = linkv.absSt σ →
      kvOpStep (linkv.opOf [] [] (putTxn pk v r true)) σ = σ := by
    intro h1
    have hrev := congrArg linkv.MSt.rev (habs.trans h1)
    rcases etcd_txnlin.kvOpStep_cases (linkv.opOf [] [] (putTxn pk v r true)) σ (linkv.opOf_isKV _ _ _) with h | h
    · exact h
    · simp only [linkv.absSt] at hrev
      omega
  have hm := mStep_putTxn [] (linkv.absSt σ) pk v r true
  by_cases hmr : modOf (linkv.absSt σ).kv pk = r
  · rw [if_pos hmr] at hm
    have hout' := hout
    rw [hm] at hout'
    simp only [linkv.MOut.txn.injEq] at hout'
    have hst : linkv.absSt (kvOpStep (linkv.opOf [] [] (putTxn pk v r true)) σ) =
        ⟨(linkv.absSt σ).kv.put ((linkv.absSt σ).rev + 1) pk v, (linkv.absSt σ).rev + 1⟩ := by
      rw [habs, hm]
    refine ⟨fun h => ?_, fun _ => ⟨(modOf_absSt σ pk).symm.trans hmr,
      ⟨linkv.kvOpStep_sorted _ σ, ?_⟩, hst, ?_⟩⟩
    · rw [h] at hout'
      exact absurd hout'.2.1 (by decide)
    · rw [hst]
      exact KWf_put c.S.dec c.pfx (linkv.absSt σ) hwf.2 hb pk v hv
    · have := congrArg linkv.MSt.rev hst
      simp only [linkv.absSt] at this
      exact this
  · rw [if_neg hmr] at hm
    rw [hm] at hout
    simp only [linkv.MOut.txn.injEq] at hout
    refine ⟨fun _ => hid (by rw [hm]), fun h => ?_⟩
    rw [h] at hout
    exact absurd hout.2.1 (by decide)

/-- **What `stFrom_item` tells of a state** where the key is at the state's revision. -/
def stItem (c : StoreCfg GF Obj) (key : GoString) (s : OState Obj) (σ : KVState) : Prop :=
  kubernetes.modAt key σ = s.rev →
    (s.rev = W64 0 ∧ (c.abs σ).items key = none) ∨
    (s.rev ≠ W64 0 ∧ c.S.decode s.data = some s.o ∧ ∃ b, (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩ ∧
      (b = true → (!s.stale && decide (c.S.encode s.o = s.data)) = true))

theorem stFrom_stItem (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key) (s : OState Obj) :
    stFrom c key s ⊢ □ ∀ σ, kvSeen c.γh σ -∗ ⌜kvWf c σ → stItem c key s σ⌝ := by
  iintro #Hf !> %σ #Hs
  by_cases hwf : kvWf c σ
  · ihave %H := stFrom_item c key hpk s σ hwf $$ [Hf Hs]
    · iframe Hf Hs
    ipureintro
    exact fun _ => H
  · ipureintro
    intro h
    exact absurd h hwf

/-- **A state at revision `0` is the zero state** (`stFrom`: a read's state is at a stored mod
revision, the cached object's at its own). -/
theorem stFrom_zero (c : StoreCfg GF Obj) (key : GoString) (s : OState Obj) :
    stFrom c key s ⊢ ⌜s.rev = W64 0 → s = zeroSt c⌝ := by
  unfold stFrom rdFacts
  iintro #Hf
  icases Hf with (⟨%σ0, %kv0, ⟨%Hw0, -⟩, %Hk0⟩ | ⟨%σ0, -, %Hz⟩ | ⟨%Hc, -⟩)
  · ipureintro
    intro h
    exfalso
    have hx : (linkv.absSt σ0).kv key = some (linkv.absVR kv0) := by
      simp [linkv.absSt, linkv.absM, Hk0.1]
    have h0 := (Hw0.1.2.2.1 key _ hx).1
    have hm : kv0.modRev = W64 0 := Hk0.2.1.symm.trans h
    simp only [linkv.absVR, hm] at h0
    exact absurd h0 (by decide)
  · ipureintro
    exact fun _ => Hz.2
  · ipureintro
    intro h
    exact absurd h Hc.2.2.2

/-- **The model's `update` writing `o'`** at a state where the key's item is the state's (or, at
revision `0`, there is none, with `ignoreNotFound` and the zero object), `tryUpdate` gave `o'` and
the store does not skip the write. -/
theorem update_item {E : Type} (c : StoreCfg GF Obj) (st : KSt Obj) (key : GoString) (s : OState Obj)
    (ign : Bool) (z : Obj) (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj) (o' : Obj)
    (hcase : (s.rev = W64 0 ∧ st.items key = none ∧ ign = true ∧ s.o = z) ∨
      (∃ b, st.items key = some ⟨s.o, uint.nat s.rev, b⟩ ∧
        (b = true → (!s.stale && decide (c.S.encode s.o = s.data)) = true)))
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : f s.o (uint.nat s.rev) = .ok o')
    (hw : (!s.stale && decide (c.S.encode o' = s.data)) = false) :
    st.update key ign z pre f =
      (⟨st.setItem key ⟨o', st.rv + 1, true⟩, st.rv + 1⟩, .obj o' (st.rv + 1)) := by
  rcases hcase with ⟨hr, hn, hi, ho⟩ | ⟨b, hb, hc⟩
  · have h0 : uint.nat s.rev = 0 := by rw [hr]; rfl
    rw [h0, ho] at hpre hok
    unfold KSt.update KSt.current
    rw [hn, hi]
    simp only [↓reduceIte, hpre, hok]
  · have hn : ¬ (o' = s.o ∧ b = true) := by
      intro ⟨h1, h2⟩
      subst h1
      rw [hc h2] at hw
      exact absurd hw (by decide)
    unfold KSt.update KSt.current
    rw [hb]
    simp only [hpre, hok]
    rw [if_neg hn]

/-- **`updateOnce`'s transaction is the model's `update` when it succeeds** (`updStepOk` on what
`stFrom` tells, `stItem`, in place of the read's key-value; at revision `0` the zero state's
create), and the identity when it fails. -/
theorem updStepOk_item {E : Type} (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key)
    (s : OState Obj) (ign : Bool) (z : Obj) (hz : s.rev = W64 0 → ign = true ∧ s.o = z)
    (pre : Obj → Nat → Bool) (hpre : pre s.o (uint.nat s.rev) = true)
    (f : Obj → Nat → Except E Obj) (o' : Obj) (hok : f s.o (uint.nat s.rev) = .ok o')
    (hw : (!s.stale && decide (c.S.encode o' = s.data)) = false) (v : GoString)
    (hv : c.S.dec v = some (o', true)) :
    ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → (kvWf c σ → stItem c key s σ) →
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optPutTxn key v s.rev true)).1 = true →
        kvWf c (kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ) ∧
        c.abs (kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ) =
          updStep key ign z pre f (c.abs σ)) ∧
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optPutTxn key v s.rev true)).1 = false →
        kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ = σ) := by
  intro σ hwf hb hA
  have hc := put_cases' c σ hwf hb key v s.rev (fun _ => by rw [hv]; rfl)
  refine ⟨fun h => ?_, hc.1⟩
  obtain ⟨hm, hwf', habs, -⟩ := hc.2 h
  refine ⟨hwf', ?_⟩
  unfold StoreCfg.abs
  rw [habs, absK_put c.S.dec c.pfx (linkv.absSt σ) hwf.2 key v o' hpk hv]
  unfold updStep
  have hcase : (s.rev = W64 0 ∧ (c.abs σ).items key = none ∧ ign = true ∧ s.o = z) ∨
      (∃ b, (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩ ∧
        (b = true → (!s.stale && decide (c.S.encode s.o = s.data)) = true)) := by
    rcases hA hwf hm with ⟨h0, hn⟩ | ⟨-, -, b, hb', hc'⟩
    · exact .inl ⟨h0, hn, (hz h0).1, (hz h0).2⟩
    · exact .inr ⟨b, hb', hc'⟩
  have := update_item c (c.abs σ) key s ign z pre f o' hcase hpre hok hw
  unfold StoreCfg.abs at this
  rw [this]
  rfl

/-! ## `GuaranteedUpdate`'s loop (stage 7b) -/

/-- **What a read at `σ` gave of the key**: its key-value's state, or (`ignoreNotFound`, the key
absent) the zero state. -/
def rdOf (c : StoreCfg GF Obj) (key : GoString) (ign : Bool) (σ : KVState) (s : OState Obj) : Prop :=
  (∃ kv, mvcc.findKey key σ.kvs = some kv ∧ stOfKv c kv s) ∨
  (mvcc.findKey key σ.kvs = none ∧ ign = true ∧ s = zeroSt c)

/-- The model's current object at a read's state is the state's. -/
theorem rd_current (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key) (ign : Bool)
    (σ : KVState) (s : OState Obj) (h : rdOf c key ign σ s) :
    (c.abs σ).current key ign c.S.zero = some (s.o, uint.nat s.rev) := by
  rcases h with ⟨kv, hf, hs⟩ | ⟨hf, hi, rfl⟩
  · have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
      simp [ObjCodec.dec, hs.2.1, hs.2.2.1]
    have hit := c.abs_some σ key hpk kv hf _ _ hd
    unfold KSt.current
    rw [hit, hs.1]
  · unfold KSt.current
    rw [c.abs_none σ key hf, hi]
    rfl

theorem current_of_item (st : KSt Obj) (key : GoString) (ign : Bool) (z o : Obj) (r : Nat) (b : Bool)
    (h : st.items key = some ⟨o, r, b⟩) : st.current key ign z = some (o, r) := by
  unfold KSt.current
  rw [h]

/-- `update` when the preconditions fail on the current object. -/
theorem update_cur_pre {E : Type} (st : KSt Obj) (key : GoString) (ign : Bool) (z : Obj)
    (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj) (o : Obj) (r : Nat)
    (hc : st.current key ign z = some (o, r)) (hp : pre o r = false) :
    st.update key ign z pre f = (st, .err (.invalidObj key)) := by
  unfold KSt.update
  rw [hc]
  simp only [hp]

/-- `update` when `tryUpdate` fails on the current object. -/
theorem update_cur_err {E : Type} (st : KSt Obj) (key : GoString) (ign : Bool) (z : Obj)
    (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj) (o : Obj) (r : Nat)
    (hc : st.current key ign z = some (o, r)) (hp : pre o r = true) (e : E)
    (he : f o r = .error e) :
    st.update key ign z pre f = (st, .err (.user e)) := by
  unfold KSt.update
  rw [hc]
  simp only [hp, he]

/-- **A read's state that `updateOnce` will write does not hand**. -/
theorem rd_hand_upd {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (s : OState Obj) (ign : Bool) (hrd : rdOf c key ign σ s)
    (pre : Obj → Nat → Bool) (f : Obj → Nat → Except E Obj) (o' : Obj)
    (hpre : pre s.o (uint.nat s.rev) = true) (hok : f s.o (uint.nat s.rev) = .ok o')
    (hw : (!s.stale && decide (c.S.encode o' = s.data)) = false) :
    stepHand c (updStep key ign c.S.zero pre f) σ = false := by
  apply hand_false
  have hcase : (s.rev = W64 0 ∧ (c.abs σ).items key = none ∧ ign = true ∧ s.o = c.S.zero) ∨
      (∃ b, (c.abs σ).items key = some ⟨s.o, uint.nat s.rev, b⟩ ∧
        (b = true → (!s.stale && decide (c.S.encode s.o = s.data)) = true)) := by
    rcases hrd with ⟨kv, hf, hs⟩ | ⟨hf, hi, rfl⟩
    · have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
        simp [ObjCodec.dec, hs.2.1, hs.2.2.1]
      have hit := c.abs_some σ key hpk kv hf _ _ hd
      rw [← hs.1] at hit
      exact .inr ⟨_, hit, fun h => h⟩
    · exact .inl ⟨rfl, c.abs_none σ key hf, hi, rfl⟩
  simp only [updStep, update_item c (c.abs σ) key s ign c.S.zero pre f o' hcase hpre hok hw]
  exact KSt.ne_of_rv

/-- **The cached object's state** (`stFrom`'s third case, the only one not current). -/
theorem stFrom_cached (c : StoreCfg GF Obj) (key : GoString) (s : OState Obj) :
    stFrom c key s ⊢ ⌜s.current = false → s.stale = false ∧ s.data = c.S.encode s.o ∧ s.rev ≠ W64 0⌝ := by
  unfold stFrom
  iintro #Hf
  icases Hf with (⟨%σ0, %kv0, -, %Hk0⟩ | ⟨%σ0, -, %Hz⟩ | ⟨%Hc, -⟩)
  · ipureintro
    intro h
    rw [Hk0.2.2.2.2] at h
    exact absurd h (by decide)
  · ipureintro
    intro h
    rw [Hz.2] at h
    cases h
  · ipureintro
    exact fun _ => Hc.2

/-- **A read's state is where it came from**, current, at revision `0` only with
`ignoreNotFound`. -/
theorem stFrom_rdOf (c : StoreCfg GF Obj) (key : GoString) (ign : Bool) (σ : KVState) (s : OState Obj)
    (h : rdOf c key ign σ s) :
    rdFacts c σ ⊢ stFrom c key s ∗ ⌜(s.rev = W64 0 → ign = true) ∧ s.current = true⌝ := by
  iintro #Hfs
  rcases h with ⟨kv, hf, hs⟩ | ⟨hf, hi, rfl⟩
  · ihave Hr := (stFrom_read c key σ kv s hf hs) $$ Hfs
    icases Hr with ⟨#Hfr, %Hr⟩
    iframe Hfr
    ipureintro
    exact ⟨fun h => absurd h Hr, hs.2.2.2⟩
  · isplitl
    · unfold stFrom
      iright
      ileft
      iexists σ
      iframe Hfs
      ipureintro; exact ⟨hf, rfl⟩
    · ipureintro
      exact ⟨fun _ => hi, rfl⟩

/-- The preconditions without a resource version do not depend on it (D1). -/
theorem preOk_rv_none (c : StoreCfg GF Obj) (pr : KPre) (h : pr.rv = none) (o : Obj) (n m : Nat) :
    c.S.preOk pr o n = c.S.preOk pr o m := by
  unfold ObjCodec.preOk KPre.ok
  simp [h]

end steps

end k8s
end EtcdGrove
end Perennial
