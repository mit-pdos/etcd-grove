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

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Updates
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.State
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.TxnModelKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Enc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section steps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  · exact linkv.kvOpStep_sorted _ σ hs
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

/-- **`Delete`'s model step** (no preconditions for now; `validate`, the caller's
`validateDeletion`). -/
def delStep {E : Type} (key : GoString) (validate : Obj → Nat → Option E) (s : KSt Obj) : KSt Obj :=
  (s.delete key (fun _ _ => none) validate).1

/-- **The model's `delete` at a state where the key's key-value is the one the store read**
(`s`, read from `kv0`; at the same mod revision, so the same value) and `validateDeletion`
passed on it: the item goes, answered with the store's object at the next revision. -/
theorem delete_at {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (v kv0 : EtcdKv) (hv : mvcc.findKey key σ.kvs = some v)
    (s : OState Obj) (hs : stOfKv c kv0 s) (hval : v.value = kv0.value)
    (hmod : v.modRev = s.rev) (validate : Obj → Nat → Option E)
    (hok : validate s.o (uint.nat s.rev) = none) :
    (c.abs σ).delete key (fun _ _ => none) validate =
      (⟨(c.abs σ).delItem key, (c.abs σ).rv + 1⟩, .obj s.o (σ.rev + 1)) := by
  obtain ⟨-, hfs, hdc, -⟩ := hs
  have hd : c.S.dec v.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hval, hfs, hdc]
  have hit := c.abs_some σ key hpk v hv _ _ hd
  unfold KSt.delete
  rw [hit]
  simp only [hmod, hok]
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
    rcases linkvtxn.kvOpStep_cases (linkv.opOf [] [] (delTxn pk r true)) σ with h | h
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
      refine ⟨fun h => ?_, fun _ => ⟨v, rfl, hmr, ⟨linkv.kvOpStep_sorted _ σ hs, ?_⟩, ?_, ?_⟩⟩
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
    (validate : Obj → Nat → Option E) (hok : validate s.o (uint.nat s.rev) = none) :
    ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → sameAt key s.rev kv0 σ →
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optDelTxn key s.rev true)).1 = true →
        kvWf c (kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ) ∧
        c.abs (kvOpStep (.txn (kubernetes.optDelTxn key s.rev true)) σ) =
          delStep key validate (c.abs σ)) ∧
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
  rw [delete_at c σ key hpk v kv0 hv s hs hval hm validate hok]

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
    (hv : mvcc.findKey key σ.kvs = none) (pre validate : Obj → Nat → Option E) :
    (c.abs σ).delete key pre validate = (c.abs σ, .err (.notFound key σ.rev)) := by
  unfold KSt.delete
  rw [c.abs_none σ key hv]
  rfl

/-- **The model's `delete` when `validateDeletion` fails on the stored object**: its error,
nothing changed. -/
theorem delete_invalid {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (kv : EtcdKv) (hv : mvcc.findKey key σ.kvs = some kv)
    (s : OState Obj) (hs : stOfKv c kv s) (validate : Obj → Nat → Option E) (e : E)
    (he : validate s.o (uint.nat s.rev) = some e) :
    (c.abs σ).delete key (fun _ _ => none) validate = (c.abs σ, .err (.user e)) := by
  obtain ⟨hrev, hfs, hdc, -⟩ := hs
  have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hfs, hdc]
  have hit := c.abs_some σ key hpk kv hv _ _ hd
  unfold KSt.delete
  rw [hit]
  simp only [← hrev, he]

/-- **The caller's `validateDeletion`** (persistent: called at each retry): on an object holding
`o` at resource version `r`, it leaves it and answers `validate o r` (`nil` for `none`). -/
def validateOk {E : Type} (c : StoreCfg GF Obj) (validate : Obj → Nat → Option E) (vf : GoFunc) :
    IProp GF :=
  iprop(□ ∀ (ctx x : GoInterface) (o : Obj) (r : w64) (Ψ : val → IProp GF),
    c.S.objAt x o (c.S.fmtRV r) -∗
    ▷ (∀ err : GoInterface, c.S.objAt x o (c.S.fmtRV r) -∗
        ⌜match validate o (uint.nat r) with
          | none => err = GoInterface.nil
          | some _ => err ≠ GoInterface.nil⌝ -∗ Ψ #err) -∗
    WP (App (App (Val #vf) (Val #ctx)) (Val #x)) {{ Ψ }})

instance validateOk_persistent {E : Type} (c : StoreCfg GF Obj) (validate : Obj → Nat → Option E)
    (vf : GoFunc) : Persistent (validateOk c validate vf) := by
  unfold validateOk; infer_instance

/-- **`Delete`'s outcome** for the prepared key `key`: an error (of the client, the update fired
at most once); the model's `delete` as the write at `σ` (`Φ σ`); or a read-like answer at `σ`
(`□ Q σ`, nothing changed, `W` back). -/
def delOut {E : Type} (c : StoreCfg GF Obj) (key : GoString) (validate : Obj → Nat → Option E)
    (W : IProp GF) (Q Φ : KVState → IProp GF) (err out : GoInterface) : IProp GF :=
  iprop((⌜err ≠ GoInterface.nil⌝ ∗ ∃ o rv, c.S.objAt out o rv) ∨
    (∃ σ, Φ σ ∗ respIs c ((c.abs σ).delete key (fun _ _ => none) validate).2 err out) ∨
    (∃ σ, □ Q σ ∗ W ∗ ⌜((c.abs σ).delete key (fun _ _ => none) validate).1 = c.abs σ⌝ ∗
      respIs c ((c.abs σ).delete key (fun _ _ => none) validate).2 err out))

/-- **`GuaranteedUpdate`'s model step** (no preconditions for now; the key must exist,
`ignoreNotFound` false; `f`, the caller's `tryUpdate`). -/
def updStep {E : Type} (key : GoString) (z : Obj) (f : Obj → Nat → Except E Obj) (s : KSt Obj) :
    KSt Obj :=
  (s.update key false z (fun _ _ => none) f).1

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
    rcases linkvtxn.kvOpStep_cases (linkv.opOf [] [] (putTxn pk v r true)) σ with h | h
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
        refine ⟨w, rfl, hwm, ⟨linkv.kvOpStep_sorted _ σ hs, ?_⟩, hst, ?_⟩
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
    (hmod : v.modRev = s.rev) (z : Obj) (f : Obj → Nat → Except E Obj) (o' : Obj)
    (hok : f s.o (uint.nat s.rev) = .ok o')
    (hw : (!s.stale && decide (c.S.encode o' = s.data)) = false) :
    (c.abs σ).update key false z (fun _ _ => none) f =
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
  simp only [hmod, hok]
  rw [if_neg hn]

/-- **`updateOnce`'s transaction is the model's `update` when it succeeds**, and the identity when
it fails, at a state of the store where the key's key-value at the store's mod revision is the
one it read (`sameAt`); `v` is the store's new value for `o'` (canonical). -/
theorem updStepOk {E : Type} (c : StoreCfg GF Obj) (key : GoString) (hpk : c.pfx <+: key)
    (kv0 : EtcdKv) (s : OState Obj) (hs : stOfKv c kv0 s) (hr : s.rev ≠ W64 0) (z : Obj)
    (f : Obj → Nat → Except E Obj) (o' : Obj) (hok : f s.o (uint.nat s.rev) = .ok o')
    (hw : (!s.stale && decide (c.S.encode o' = s.data)) = false) (v : GoString)
    (hv : c.S.dec v = some (o', true)) :
    ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → sameAt key s.rev kv0 σ →
      ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (kubernetes.optPutTxn key v s.rev true)).1 = true →
        kvWf c (kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ) ∧
        c.abs (kvOpStep (.txn (kubernetes.optPutTxn key v s.rev true)) σ) =
          updStep key z f (c.abs σ)) ∧
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
  have := update_at c σ key hpk w kv0 hw' s hs hval hm z f o' hok hw
  unfold StoreCfg.abs at this
  rw [this]
  rfl

/-- **The caller's `tryUpdate`** (persistent: called at each retry): on an object holding `o` at
resource version `r` (and the response metadata at `r`), it answers `f o r`: an object holding
the result (no TTL, D30d), or an error. It may keep or change the input object (it owns it). -/
def tryUpdateOk {E : Type} (c : StoreCfg GF Obj) (f : Obj → Nat → Except E Obj) (uf : GoFunc) :
    IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : Obj) (r : w64) (Ψ : val → IProp GF),
    c.S.objAt x o (c.S.fmtRV r) -∗
    ▷ (∀ (ret : GoInterface) (ttlp : Loc) (err : GoInterface),
        (match f o (uint.nat r) with
          | .ok o' => ⌜err = GoInterface.nil ∧ ttlp = null⌝ ∗ ∃ rv', c.S.objAt ret o' rv'
          | .error _ => ⌜err ≠ GoInterface.nil⌝) -∗
        Ψ (PairV (PairV #ret #ttlp) #err)) -∗
    WP (App (App (Val #uf) (Val #x))
      (Val #(k8s_io.apiserver.pkg.storage.ResponseMeta.mk (W64 0) r))) {{ Ψ }})

instance tryUpdateOk_persistent {E : Type} (c : StoreCfg GF Obj) (f : Obj → Nat → Except E Obj)
    (uf : GoFunc) : Persistent (tryUpdateOk c f uf) := by
  unfold tryUpdateOk; infer_instance

/-- **`GuaranteedUpdate`'s outcome** for the prepared key `key` (as `delOut`): an error; the
model's `update` as the write at `σ` (`Φ σ`); or a read-like answer at `σ` (`□ Q σ`, nothing
changed, `W` back: a no-op, not found, `tryUpdate`'s error). -/
def updOut {E : Type} (c : StoreCfg GF Obj) (key : GoString) (z : Obj)
    (f : Obj → Nat → Except E Obj) (W : IProp GF) (Q Φ : KVState → IProp GF)
    (err out : GoInterface) : IProp GF :=
  iprop((⌜err ≠ GoInterface.nil⌝ ∗ ∃ o rv, c.S.objAt out o rv) ∨
    (∃ σ, Φ σ ∗ respIs c ((c.abs σ).update key false z (fun _ _ => none) f).2 err out) ∨
    (∃ σ, □ Q σ ∗ W ∗ ⌜((c.abs σ).update key false z (fun _ _ => none) f).1 = c.abs σ⌝ ∗
      respIs c ((c.abs σ).update key false z (fun _ _ => none) f).2 err out))

/-- **The model's `update` of a key the state lacks** (`ignoreNotFound` false): "not found",
nothing changed. -/
theorem update_none {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hv : mvcc.findKey key σ.kvs = none) (z : Obj) (pre : Obj → Nat → Option E)
    (f : Obj → Nat → Except E Obj) :
    (c.abs σ).update key false z pre f = (c.abs σ, .err (.notFound key σ.rev)) := by
  unfold KSt.update KSt.current
  rw [c.abs_none σ key hv]
  rfl

/-- **The model's `update` when `tryUpdate` fails on the stored object**: its error, nothing
changed. -/
theorem update_err {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (kv : EtcdKv) (hv : mvcc.findKey key σ.kvs = some kv)
    (s : OState Obj) (hs : stOfKv c kv s) (z : Obj) (f : Obj → Nat → Except E Obj) (e : E)
    (he : f s.o (uint.nat s.rev) = .error e) :
    (c.abs σ).update key false z (fun _ _ => none) f = (c.abs σ, .err (.user e)) := by
  obtain ⟨hrev, hfs, hdc, -⟩ := hs
  have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hfs, hdc]
  have hit := c.abs_some σ key hpk kv hv _ _ hd
  unfold KSt.update KSt.current
  rw [hit]
  simp only [← hrev, he]

/-- **The model's `update` when the store skips the write** (`store.go:547`: not stale, and the
result's encoding is the stored data): the stored object at its resource version, nothing
changed (`noop_iff`: the result is the object, canonical). -/
theorem update_skip {E : Type} (c : StoreCfg GF Obj) (σ : KVState) (key : GoString)
    (hpk : c.pfx <+: key) (kv : EtcdKv) (hv : mvcc.findKey key σ.kvs = some kv)
    (s : OState Obj) (hs : stOfKv c kv s) (z : Obj) (f : Obj → Nat → Except E Obj) (o' : Obj)
    (hok : f s.o (uint.nat s.rev) = .ok o')
    (hn : (!s.stale && decide (c.S.encode o' = s.data)) = true) :
    (c.abs σ).update key false z (fun _ _ => none) f = (c.abs σ, .obj s.o (uint.nat s.rev)) := by
  obtain ⟨hrev, hfs, hdc, -⟩ := hs
  have hd : c.S.dec kv.value = some (s.o, !s.stale && decide (c.S.encode s.o = s.data)) := by
    simp [ObjCodec.dec, hfs, hdc]
  have hit := c.abs_some σ key hpk kv hv _ _ hd
  obtain ⟨heq, -⟩ := (ObjCodec.noop_iff c.S.toObjCodec kv.value s.data s.stale s.o o' hfs hdc).1 hn
  subst heq
  have hc : (!s.stale && decide (c.S.encode s.o = s.data)) = true := hn
  unfold KSt.update KSt.current
  rw [hit]
  simp only [← hrev, hok]
  simp [hc]

end steps

end k8s
end EtcdGrove
end Perennial
