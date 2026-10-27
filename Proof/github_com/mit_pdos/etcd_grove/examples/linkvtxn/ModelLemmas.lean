/-
Lean-first (no Rocq counterpart).

# linkvtxn: the Go model's pure form, against the robustness model (linkv-txn stage E)

`examples/linkvtxn/linkvtxn.go`'s `Model()` computes on Go values: a state is a list of
configurations (`mcfg`), each a store (`store`: a list of `entry`s sorted by key, and the
revision) and the pending failed writes (a list of `Input`s). Here are the pure functions its
helpers compute, as their specs state them (`Spec/.../linkvtxn/<fn>.lean`), and how they abstract
to `linkvtxn/TxnModel.lean`'s model (`txnSpec`, as `linkvtxn/PendModel.lean`'s `pSeq`):

- the store's helpers: `lookupL`, `setKeyL` (`setR`), `delKeyL`, `putL`, `holdsL`, `runOpsL`;
  the input's and output's fields as lists (`cmpsOfL`, `thenOfL`, `elseOfL`, `resOfL`,
  `kvsOfL`, `withResL`, `withKVsL`); `mstepL` (`mstep`); `isWriteL`; the equalities
  (`outEqualL`, the configurations' `=`);
- the abstraction: `absSt` (a key's value its first entry's, `absVR`; the revision as a
  number), the decoders `decIn` (an input `Gen` may produce, `ValidIn`) and `decOut` (an output,
  by its input's kind), and the store's invariant `GoodSt` (sorted, the workload's keys, a
  revision far from overflow);
- **`mstepL_abs`**: `mstep` is the model's `mStep` on good stores, and keeps them good.

This file has the definitions and the store-level lemmas; `Steps.lean` has the configurations'.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.TxnModel
public import Code.github_com.mit_pdos.etcd_grove.examples.linkvtxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open github_com.mit_pdos.etcd_grove.examples.linkvtxn
open Classical

section go
variable [GooseExts]

/-! ## Decidable equality of the Go records -/

instance VR_decEq : DecidableEq VR := fun a b =>
  decidable_of_iff (a.Val' = b.Val' ∧ a.Mod' = b.Mod' ∧ a.Ver' = b.Ver')
    (by cases a; cases b; simp)

instance entry_decEq : DecidableEq entry := fun a b =>
  decidable_of_iff (a.key' = b.key' ∧ a.r' = b.r') (by cases a; cases b; simp)

instance Cmp_decEq : DecidableEq Cmp := fun a b =>
  decidable_of_iff (a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val' ∧ a.Num' = b.Num')
    (by cases a; cases b; simp)

instance TOp_decEq : DecidableEq TOp := fun a b =>
  decidable_of_iff (a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val')
    (by cases a; cases b; simp)

instance Input_decEq : DecidableEq Input := fun a b =>
  decidable_of_iff (a.Kind' = b.Kind' ∧ a.Key' = b.Key' ∧ a.Val' = b.Val' ∧ a.NCmps' = b.NCmps' ∧
      a.Cmp0' = b.Cmp0' ∧ a.NThen' = b.NThen' ∧ a.Then0' = b.Then0' ∧ a.Then1' = b.Then1' ∧
      a.Then2' = b.Then2' ∧ a.NElse' = b.NElse' ∧ a.Else0' = b.Else0')
    (by cases a; cases b; simp)

/-! ## The store's helpers -/

/-- The zero `VR` (`VR{}`). -/
def zVR : VR := ⟨[], W64 0, W64 0⟩

/-- `lookup(kvs, k)`: `k`'s first entry's value. -/
def lookupL (es : List entry) (k : GoString) : VR × Bool :=
  match es.find? (fun e => decide (e.key' = k)) with
  | some e => (e.r', true)
  | none => (zVR, false)

/-- One iteration of `setKey`'s loop on `(out, done)`. -/
def setStep (k : GoString) (r : VR) (st : List entry × Bool) (e : entry) : List entry × Bool :=
  if st.2 = false ∧ go.GoStringLe k e.key' then
    if e.key' = k then (st.1 ++ [⟨k, r⟩], true) else (st.1 ++ [⟨k, r⟩, e], true)
  else (st.1 ++ [e], st.2)

/-- The end of `setKey`: `k ↦ r` appended if not yet written. -/
def setFin (k : GoString) (r : VR) (st : List entry × Bool) : List entry :=
  if st.2 then st.1 else st.1 ++ [⟨k, r⟩]

/-- `setKey(kvs, k, r)`. -/
def setKeyL (es : List entry) (k : GoString) (r : VR) : List entry :=
  setFin k r (es.foldl (setStep k r) ([], false))

/-- `setKey`, recursively. -/
def setR (k : GoString) (r : VR) : List entry → List entry
  | [] => [⟨k, r⟩]
  | e :: es =>
    if go.GoStringLe k e.key' then (if e.key' = k then ⟨k, r⟩ :: es else ⟨k, r⟩ :: e :: es)
    else e :: setR k r es

/-- `delKey(kvs, k)`. -/
def delKeyL (es : List entry) (k : GoString) : List entry := es.filter (fun e => !decide (e.key' = k))

/-- `put(kvs, r, k, v)`: the key's version one more (`1` for a new key). -/
def putL (es : List entry) (r : w64) (k v : GoString) : List entry :=
  setKeyL es k ⟨v, r, if (lookupL es k).2 then (lookupL es k).1.Ver' + W64 1 else W64 1⟩

/-- `holds(kvs, c)`. -/
def holdsL (es : List entry) (c : Cmp) : Bool :=
  if c.Kind' = W64 0 then (lookupL es c.Key').2 && decide ((lookupL es c.Key').1.Val' = c.Val')
  else if c.Kind' = W64 1 then decide ((lookupL es c.Key').1.Ver' = c.Num')
  else decide ((lookupL es c.Key').1.Mod' = c.Num')

/-- A get's result (`TRes{Kind: TGet, Found: ok, R: v}`). -/
def getRes (p : VR × Bool) : TRes := ⟨W64 0, p.2, p.1, W64 0⟩

/-- A put's result (`TRes{Kind: TPut}`). -/
def putRes : TRes := ⟨W64 1, false, zVR, W64 0⟩

/-- A delete's result (`TRes{Kind: TDel, N: n}`). -/
def delRes (n : w64) : TRes := ⟨W64 2, false, zVR, n⟩

/-- One iteration of `runOps`'s loop on `(kvs, res, changed)`. -/
def runStep (r : w64) (acc : List entry × List TRes × Bool) (op : TOp) :
    List entry × List TRes × Bool :=
  if op.Kind' = W64 0 then (acc.1, acc.2.1 ++ [getRes (lookupL acc.1 op.Key')], acc.2.2)
  else if op.Kind' = W64 1 then (putL acc.1 r op.Key' op.Val', acc.2.1 ++ [putRes], true)
  else if (lookupL acc.1 op.Key').2 then (delKeyL acc.1 op.Key', acc.2.1 ++ [delRes (W64 1)], true)
  else (acc.1, acc.2.1 ++ [delRes (W64 0)], acc.2.2)

/-- `runOps(kvs, r, ops)`. -/
def runOpsL (es : List entry) (r : w64) (ops : List TOp) : List entry × List TRes × Bool :=
  ops.foldl (runStep r) (es, [], false)

/-! ## The input's and output's fields as lists -/

/-- `cmpsOf(in)`. -/
def cmpsOfL (x : Input) : List Cmp := if 0 < sint.Z x.NCmps' then [x.Cmp0'] else []

/-- `thenOf(in)`. -/
def thenOfL (x : Input) : List TOp :=
  (if 0 < sint.Z x.NThen' then [x.Then0'] else []) ++
  (if 1 < sint.Z x.NThen' then [x.Then1'] else []) ++
  (if 2 < sint.Z x.NThen' then [x.Then2'] else [])

/-- `elseOf(in)`. -/
def elseOfL (x : Input) : List TOp := if 0 < sint.Z x.NElse' then [x.Else0'] else []

/-- `resOf(o)`. -/
def resOfL (o : Output) : List TRes :=
  (if 0 < sint.Z o.NRes' then [o.Res0'] else []) ++
  (if 1 < sint.Z o.NRes' then [o.Res1'] else []) ++
  (if 2 < sint.Z o.NRes' then [o.Res2'] else [])

/-- `kvsOf(o)`. -/
def kvsOfL (o : Output) : List KV :=
  (if 0 < sint.Z o.NKVs' then [o.KV0'] else []) ++
  (if 1 < sint.Z o.NKVs' then [o.KV1'] else []) ++
  (if 2 < sint.Z o.NKVs' then [o.KV2'] else [])

/-- `withRes(o, rs)`. -/
def withResL (o : Output) (rs : List TRes) : Output :=
  { o with NRes' := W64 (rs.length : Int), Res0' := rs.getD 0 o.Res0', Res1' := rs.getD 1 o.Res1',
           Res2' := rs.getD 2 o.Res2' }

/-- `withKVs(o, kvs)`. -/
def withKVsL (o : Output) (kvs : List KV) : Output :=
  { o with NKVs' := W64 (kvs.length : Int), KV0' := kvs.getD 0 o.KV0', KV1' := kvs.getD 1 o.KV1',
           KV2' := kvs.getD 2 o.KV2' }

/-- The zero `Output` (`Output{}`). -/
def zOut : Output := ⟨false, W64 0, false, zVR, W64 0, false, W64 0, putRes0, putRes0, putRes0, W64 0,
    kv0, kv0, kv0⟩
where
  putRes0 : TRes := ⟨W64 0, false, zVR, W64 0⟩
  kv0 : KV := ⟨[], zVR⟩

/-! ## One operation -/

/-- A store's contents: its entries and revision. -/
structure GSt where
  kvs : List entry
  rev : w64

instance GSt_decEq : DecidableEq GSt := fun a b =>
  decidable_of_iff (a.kvs = b.kvs ∧ a.rev = b.rev) (by cases a; cases b; simp)

/-- The verdict of a transaction's comparisons (`mstep`'s loop). -/
def cmpsOk (es : List entry) (cs : List Cmp) : Bool := cs.all (holdsL es)

/-- `mstep(in, st)`. -/
def mstepL (x : Input) (st : GSt) : GSt × Output :=
  if x.Kind' = W64 0 then
    (st, { zOut with Rev' := st.rev, Found' := (lookupL st.kvs x.Key').2,
                     R' := (lookupL st.kvs x.Key').1 })
  else if x.Kind' = W64 1 then
    (st, withKVsL { zOut with Rev' := st.rev } (st.kvs.map fun e => ⟨e.key', e.r'⟩))
  else if x.Kind' = W64 2 then
    (⟨putL st.kvs (st.rev + W64 1) x.Key' x.Val', st.rev + W64 1⟩,
      { zOut with Rev' := st.rev + W64 1 })
  else if x.Kind' = W64 3 then
    if (lookupL st.kvs x.Key').2 then
      (⟨delKeyL st.kvs x.Key', st.rev + W64 1⟩, { zOut with Rev' := st.rev + W64 1, N' := W64 1 })
    else (st, { zOut with Rev' := st.rev, N' := W64 0 })
  else
    let ok := cmpsOk st.kvs (cmpsOfL x)
    let q := runOpsL st.kvs (st.rev + W64 1) (if ok then thenOfL x else elseOfL x)
    let rev := if q.2.2 then st.rev + W64 1 else st.rev
    (⟨q.1, rev⟩, withResL { zOut with Rev' := rev, Ok' := ok } q.2.1)

/-- `isWrite(in)`. -/
def isWriteL (x : Input) : Bool :=
  if x.Kind' = W64 2 ∨ x.Kind' = W64 3 then true
  else if x.Kind' ≠ W64 4 then false
  else (thenOfL x).any (fun op => decide (op.Kind' ≠ W64 0)) ||
    (elseOfL x).any (fun op => decide (op.Kind' ≠ W64 0))

/-- `resEqual(x, y)`. -/
def resEqualL (x y : TRes) : Bool :=
  if x.Kind' ≠ y.Kind' then false
  else if x.Kind' = W64 0 then decide (x.Found' = y.Found') && (!x.Found' || decide (x.R' = y.R'))
  else if x.Kind' = W64 2 then decide (x.N' = y.N')
  else true

/-- `outEqual(kind, a, b)`. -/
def outEqualL (kind : w64) (a b : Output) : Bool :=
  if a.Err' || b.Err' || decide (a.Rev' ≠ b.Rev') then false
  else if kind = W64 0 then decide (a.Found' = b.Found') && (!a.Found' || decide (a.R' = b.R'))
  else if kind = W64 1 then
    if a.NKVs' ≠ b.NKVs' ∨ 3 < sint.Z a.NKVs' then false
    else ((kvsOfL a).zip (kvsOfL b)).all fun p => decide (p.1.Key' = p.2.Key' ∧ p.1.R' = p.2.R')
  else if kind = W64 2 then true
  else if kind = W64 3 then decide (a.N' = b.N')
  else if a.Ok' ≠ b.Ok' ∨ a.NRes' ≠ b.NRes' ∨ 3 < sint.Z a.NRes' then false
  else ((resOfL a).zip (resOfL b)).all fun p => resEqualL p.1 p.2

end go

end linkvtxn
end EtcdGrove
end Perennial
