/-
What the server's `Put` and `DeleteRange` do (unit 1, `put.go`, `delete.go`), in the client
model's terms, and what their proofs share. Lean-first; `notes/STATUS.md`, "Unit 1".

**The put.** A put request `o` (`putRequestIs`) at a state whose key has the key-value `pv`
(`findKey`, `getPrevKV`'s answer) writes `putChangeOf o pv`: the request's value, or (`IgnoreValue`)
the previous one; the request's lease, or (`IgnoreLease`) the previous one. That is the client's
`applyTxnOp` of `putTxnOp o` (`applyChange_putChangeOf`). With an ignore flag and no previous
key-value the server fails (`ErrKeyNotFound`, `putKeyMissing`).

**The delete** of a request `o` (`deleteRangeRequestIs`) deletes the keys of `rangeIn st o`
(`delChanges`), the client's filter (`stateAfter_commit_delete`).

**A transaction's reads** (`kindState k`, `KindOk k`, over mvcc's API's `MTxn`, strict M1,
2026-11-05): the state a transaction reads, and the facts of its read log that relate mvcc's
index answers (`rangeOutcome`) to that state (`prevKvIs_of_outcome`, `rangeOutcome_sel`). Until
M1 the internals' `isTxn` gave `KindOk` (`isTxn_kindOk`); the API gives none of it (the gap in
`notes/mvcc-migration/txn.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode mvcc

/-! ## The put -/

/-- Whether a put needs the previous key-value (`checkAndGetPrevKV`: `ErrKeyNotFound`). -/
def needsPrev (o : OpFull) : Bool := o.ignoreValue || o.ignoreLease

/-- Whether a put reads the previous key-value (`getPrevKV`). -/
def readsPrev (o : OpFull) : Bool := needsPrev o || o.base.prevKV

/-- The value a put writes, the previous key-value being `pv`. -/
def putValOf (o : OpFull) (pv : Option EtcdKv) : GoString :=
  if o.ignoreValue then (pv.map EtcdKv.value).getD [] else o.val

/-- The lease a put writes, the previous key-value being `pv`. -/
def putLeaseOf (o : OpFull) (pv : Option EtcdKv) : w64 :=
  if o.ignoreLease then (pv.map EtcdKv.lease).getD (W64 0) else o.leaseID

/-- The change a put writes, the previous key-value being `pv`. -/
def putChangeOf (o : OpFull) (pv : Option EtcdKv) : Change :=
  .put o.key (putValOf o pv) (putLeaseOf o pv)

/-- **The server's put is the client's** (`putTxnOp`, with `IgnoreValue`/`IgnoreLease`). -/
theorem applyChange_putChangeOf (r : w64) (s : List EtcdKv) (o : OpFull) :
    applyChange r s (putChangeOf o (findKey o.key s)) = (applyTxnOp r s (putTxnOp o)).1 := by
  unfold putChangeOf putValOf putLeaseOf putTxnOp findKey
  rw [applyChange_put]
  cases o.ignoreValue <;> cases o.ignoreLease <;> rfl

/-- The committed state of a put at the end of `ilog`: the client's. -/
theorem stateAfter_put (ilog : Log) (o : OpFull) :
    stateAfter (ilog ++ [[putChangeOf o (findKey o.key (stateAfter ilog))]]) =
      (applyTxnOp (W64 ilog.length) (stateAfter ilog) (putTxnOp o)).1 := by
  rw [stateAfter_snoc]
  exact applyChange_putChangeOf _ _ _

/-- The state a write transaction at the committed log `ilog` with the pending changes `pend`
reads: the pending changes applied (`kindState_write`). -/
def pendState (ilog : Log) (pend : List Change) : List EtcdKv :=
  applyChanges (W64 ilog.length) (stateAfter ilog) pend

theorem pendState_nil (ilog : Log) : pendState ilog [] = stateAfter ilog := rfl

/-! ## The delete -/

/-- The changes a delete of `o` writes at the state `st`: its range's keys, deleted. -/
def delChanges (st : List EtcdKv) (o : OpFull) : List Change :=
  (rangeIn st o).map fun v => .del v.key

/-- `deleteRange`'s keys (`delKeys`, mvcc's) for the client's `o`: its range's. -/
theorem delKeys_client (ilog : Log) (pend : List Change) (hok : LogOk (ilog ++ [pend]))
    (hne : ilog ≠ []) (o : OpFull) :
    (delKeys ilog pend (srvEnd o.base.rangeEnd).1 o.key (srvEnd o.base.rangeEnd).2).map .del =
      delChanges (applyChanges (W64 ilog.length) (stateAfter ilog) pend) o := by
  rw [delKeys_eq ilog pend hok hne, srvSel_srvEnd, delChanges, List.map_map]
  rfl

/-- **The server's delete is the client's** (the committed state of a delete transaction). -/
theorem stateAfter_commit_delete (ilog : Log) (o : OpFull) :
    stateAfter (commitLog ilog (delChanges (stateAfter ilog) o)) =
      (applyTxnOp (W64 ilog.length) (stateAfter ilog) (.delete o)).1 := by
  have hm : (rangeIn (stateAfter ilog) o).map (fun v => Change.del v.key) =
      ((rangeIn (stateAfter ilog) o).map EtcdKv.key).map Change.del := by
    rw [List.map_map]; rfl
  rw [stateAfter_commitLog, delChanges, hm, rangeIn, applyChanges_dels_sel]
  rfl

/-! ## The range end -/

/-- **`mkGteRange` turns the request's range end into the server's** (`srvEnd` of its
`rangeEndOf`): `r` is `mkGteRange(sl)`'s result, `sl` holding `e` (a `nil` slice holds
nothing). -/
theorem srvEnd_mkGte (sl r : GoSlice) (e : GoString) (hnil : sl = slice.nil → e = [])
    (hr : if e = [W8 0] then r ≠ slice.nil else r = sl) :
    (decide (r = slice.nil), if e = [W8 0] then [] else e) = srvEnd (rangeEndOf sl e) := by
  unfold rangeEndOf srvEnd
  by_cases h0 : e = [W8 0]
  · subst h0
    simp only [↓reduceIte] at hr ⊢
    have hsl : sl ≠ slice.nil := fun h => by have := hnil h; simp at this
    simp [hr, hsl]
  · simp only [h0, ↓reduceIte] at hr ⊢
    subst hr
    by_cases hs : r = slice.nil
    · have := hnil hs; subst this; simp [hs]
    · by_cases he : e = []
      · subst he; simp [hs]
      · simp [hs, he]; exact h0

/-! ## A transaction's reads -/

/-- The state a transaction reads (`MTxn.readLog` at `readRev`). -/
def kindState (k : mvcc.api.MTxn) : List EtcdKv := stateAt k.readLog (sint.nat k.readRev)

/-- What relates mvcc's index answers to the state a transaction reads: its read log well formed
and small (`LogOk`), the revision in it. -/
def KindOk (k : mvcc.api.MTxn) : Prop :=
  LogOk k.readLog ∧ 0 ≤ sint.Z k.readRev ∧ sint.Z k.readRev < k.readLog.length

/-- A write transaction reads the state after its pending changes. -/
theorem kindState_write (σ : mvcc.api.MvccState) (pend : List Change)
    (hne : σ.log ≠ []) (hlen : σ.log.length + 1 < 2 ^ 63) :
    kindState (.write σ pend) = pendState σ.log pend := by
  unfold kindState pendState mvcc.api.MTxn.readLog mvcc.api.MTxn.readRev
  have := writeRev_lt σ.log pend hne
  simp only [List.length_append, List.length_singleton] at this
  have hz : sint.Z (W64 ((writeRev σ.log pend : Nat) : Int)) = writeRev σ.log pend := by word
  have hn : sint.nat (W64 ((writeRev σ.log pend : Nat) : Int)) = writeRev σ.log pend := by
    unfold sint.nat; unfold sint.Z at hz; rw [hz]; rfl
  rw [hn, stateAt_writeRev σ.log pend hne]

/-- A range read of one key (`end` is `nil`) answers the key's key-value if it has one. -/
theorem rangeAnswers_one (log : Log) (hok : LogOk log) (k e : GoString) (r : Nat)
    (hr : r < 2 ^ 63) :
    List.Forall₂ (AnsKv log (stateAt log r)) (rangeAnswers log true k e (W64 r))
      (findKey k (stateAt log r)).toList := by
  have h := rangeAnswers_stateAt log hok true k e r hr
  have hs : srvSel (stateAt log r) true k e = (findKey k (stateAt log r)).toList := by
    unfold srvSel srvInRange
    simp only [↓reduceIte]
    exact filter_key_eq k (stateAt_sorted log r)
  rwa [hs] at h

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `err` is the error of the package variable `g` (a fixed non-nil error: `txnInit`). -/
def errVarIs (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)

instance errVarIs_persistent (g : GoString) (err : GoInterface) :
    Persistent (errVarIs (GF := GF) g err) := by
  unfold errVarIs; infer_instance

/-- A lease a put may attach (mvcc's `Put`): none, or one of the live set `L` (the lease owner's:
`lease.leaseOwn`; 2026-10-13, unit 8 of the backend: a lease is live relative to the owner's
half of the lessor's live set, not for good: it was the persistent `leaseKnown`). -/
def leaseOk (L : List w64) (id : w64) : IProp GF := iprop(⌜id = W64 0 ∨ id ∈ L⌝)

instance leaseOk_persistent (L : List w64) (id : w64) : Persistent (leaseOk (GF := GF) L id) := by
  unfold leaseOk; infer_instance

/-- **`getPrevKV`'s answer** `r` at the state `st`: a `RangeResult` (not `nil`) whose key-values
(`KVs`, the one field read) are the key `k`'s key-value, if it has one (fresh, owned). -/
def prevKvIs (r : Loc) (st : List EtcdKv) (k : GoString) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ ∃ (kvs : GoSlice) (ps : List Loc),
    r.[go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult, go!"KVs"] ↦ kvs ∗ kvs ↦* ps ∗
    match findKey k st with
    | none => iprop(⌜ps = []⌝)
    | some kv => iprop(∃ pk : Loc, ⌜ps = [pk]⌝ ∗ kvPtrIs true pk kv))

/-- A fresh key-value, made read-only: `kvIs`. -/
theorem kvPtrIs_kvIs (p : Loc) (kv : EtcdKv) : kvPtrIs (GF := GF) true p kv ⊢ |==> kvIs p kv := by
  unfold kvPtrIs kvIs
  simp only [↓reduceIte]
  iintro ⟨%ks, %st, %uf, %sc, #Hk, %vs, #Hv, Hp⟩
  ipersist Hp
  iStructNamed Hp
  imodintro
  iexists ks, vs
  iframe #

/-- A fresh key-value's pointer is not `nil`. -/
theorem kvPtrIs_not_null (full : Bool) (p : Loc) (kv : EtcdKv) :
    kvPtrIs (GF := GF) full p kv ⊢ ⌜p ≠ null⌝ := by
  unfold kvPtrIs
  iintro ⟨%ks, %st, %uf, %sc, -, H⟩
  cases full
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply typedPointsto_not_null $$ H
  · simp only [↓reduceIte]
    icases H with ⟨%vs, -, H⟩
    iapply typedPointsto_not_null $$ H

/-- **`getPrevKV`'s answer from the range read** of one key (`end` is `nil`, the options
`RangeOptions{}`), at a transaction's log and revision, not `nil` (`context.TODO()`): no error,
and the key's key-value at the state read. -/
theorem prevKvIs_of_outcome (r : Loc) (err : GoInterface) (kind : mvcc.api.MTxn) (k e : GoString)
    (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (hok : KindOk kind)
    (hro : ro.Rev' = W64 0 ∧ ro.Limit' = W64 0 ∧ ro.CountOnly' = false ∧ ro.FastKeysOnly' = false)
    (hr : r ≠ null) :
    rangeOutcome (GF := GF) r err kind.readLog kind.readRev true k e ro ⊢
      ⌜err = GoInterface.nil⌝ ∗ prevKvIs r (kindState kind) k := by
  obtain ⟨hok, h0, hlt⟩ := hok
  obtain ⟨hrev, hlim, hco, hfk⟩ := hro
  have h00 : sint.Z (W64 0 : w64) = 0 := by decide
  have hRR : rangeRev kind.readRev ro.Rev' = kind.readRev := by
    unfold rangeRev; rw [hrev, h00]; simp
  have hlog := hok.len
  have hans := rangeAnswers_one kind.readLog hok k e (sint.nat kind.readRev)
    (by show (sint.Z kind.readRev).toNat < 2 ^ 63; omega)
  rw [W64_sint_nat _ h0] at hans
  unfold rangeOutcome
  iintro (⟨%Hlt, -, -⟩ | ⟨-, -, %Hn, -⟩ | ⟨-, %Herr, H⟩)
  · rw [hrev, h00] at Hlt; omega
  · exact absurd Hn hr
  rw [hco, hfk, hRR]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  icases H with ⟨%kvs, Hr, Hkvs⟩
  unfold rangeKvs rangeTaken
  simp only [↓reduceIte]
  icases Hkvs with ⟨%ps, Hps, %Hlen, Hzip⟩
  isplitl []
  · ipureintro; exact Herr
  unfold prevKvIs kindState
  iStructNamed Hr
  isplitl []
  · ipureintro; exact hr
  iexists kvs, ps
  iframe KVs Hps
  generalize hA : rangeAnswers kind.readLog true k e kind.readRev = A at hans Hlen
  cases hf : findKey k (stateAt kind.readLog (sint.nat kind.readRev)) with
  | none =>
    rw [hf] at hans
    simp only [Option.toList_none] at hans
    cases hans
    simp only [List.length_nil, List.length_eq_zero_iff] at Hlen
    ipureintro; exact Hlen
  | some kv =>
    rw [hf] at hans
    simp only [Option.toList_some] at hans
    obtain ⟨a, A', hAK, hnil, rfl⟩ : ∃ a A', AnsKv kind.readLog
        (stateAt kind.readLog (sint.nat kind.readRev)) a kv ∧ A' = [] ∧ A = a :: A' := by
      cases hans with
      | cons h t => cases t; exact ⟨_, _, h, rfl, rfl⟩
    subst hnil
    match ps, Hlen with
    | [pk], _ =>
      simp only [List.zip_cons_cons, List.zip_nil_left]
      iexists pk
      isplitl []
      · ipureintro; rfl
      icases BigSepL.bigSepL_singleton.1 $$ Hzip with ⟨%kv', %Hkv', Hp⟩
      have : kv' = kv := by
        have := hAK.1; rw [Hkv'] at this; exact Option.some.inj this
      subst this
      iexact Hp

/-- No key-values. -/
theorem kvsIs_nil : ⊢ kvsIs (GF := GF) [] [] := by
  unfold kvsIs
  isplitl []
  · ipureintro; rfl
  imodintro
  iintro %i %q %w %Hq
  simp at Hq

/-- The fresh key-values of a range read, one per answer, made read-only: the selection the
answers stand for (`AnsKv`). -/
theorem zip_kvsIs (log : Log) (st : List EtcdKv) :
    ∀ (ps : List Loc) (answers : List (GoString × Rev × w64 × w64)) (sel : List EtcdKv),
    List.Forall₂ (AnsKv log st) answers sel → ps.length = answers.length →
    ([∗list] pa ∈ ps.zip answers, ∃ kv : EtcdKv, ⌜findKey pa.2.1 st = some kv⌝ ∗
        kvPtrIs (GF := GF) true pa.1 kv) ⊢ |==> kvsIs ps sel
  | [], _, _, .nil, _ => by
    iintro -
    imodintro
    unfold kvsIs
    isplitl []
    · ipureintro; rfl
    imodintro
    iintro %i %q %w %Hq
    simp at Hq
  | p :: ps, a :: ans, v :: vs, .cons hav t, hlen => by
    have ih := zip_kvsIs log st ps ans vs t (by simpa using hlen)
    simp only [List.zip_cons_cons]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%kv, %Hkv, Hp⟩, Ht⟩
    have hkv : kv = v := by have := hav.1; rw [Hkv] at this; exact Option.some.inj this
    subst hkv
    imod kvPtrIs_kvIs p kv $$ Hp with #Hp
    imod ih $$ Ht with Ht
    unfold kvsIs
    icases Ht with ⟨%Hl, #Ht⟩
    imodintro
    isplitl []
    · ipureintro; simp [Hl]
    imodintro
    iintro %i %q %w %Hq %Hw
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hq Hw
      subst Hq Hw
      iexact Hp
    | succ i =>
      simp only [List.getElem?_cons_succ] at Hq Hw
      iapply Ht $$ %i %q %w %Hq %Hw
  | [], _ :: _, _, .cons _ _, hlen => by simp at hlen
  | _ :: _, [], _, .nil, hlen => by simp at hlen

/-- **A full range read** (`RangeOptions{}`) at a transaction's log and revision: a context
error, or the selection of the state read in the range, read-only (`kvsIs`). -/
theorem rangeOutcome_sel (r : Loc) (err : GoInterface) (kind : mvcc.api.MTxn) (endNil : Bool)
    (k e : GoString) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (hok : KindOk kind)
    (hro : ro.Rev' = W64 0 ∧ ro.Limit' = W64 0 ∧ ro.CountOnly' = false ∧ ro.FastKeysOnly' = false) :
    rangeOutcome (GF := GF) r err kind.readLog kind.readRev endNil k e ro ⊢ |==>
      (⌜r = null ∧ err ≠ GoInterface.nil⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (kvs : GoSlice) (rev cnt : w64) (ps : List Loc),
          r ↦ ({ KVs' := kvs, Rev' := rev, Count' := cnt } :
            go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult) ∗ kvs ↦* ps ∗
          kvsIs ps (srvSel (kindState kind) endNil k e))) := by
  obtain ⟨hok, h0, hlt⟩ := hok
  obtain ⟨hrev, hlim, hco, hfk⟩ := hro
  have h00 : sint.Z (W64 0 : w64) = 0 := by decide
  have hRR : rangeRev kind.readRev ro.Rev' = kind.readRev := by
    unfold rangeRev; rw [hrev, h00]; simp
  have hans := rangeAnswers_stateAt kind.readLog hok endNil k e (sint.nat kind.readRev)
    (by show (sint.Z kind.readRev).toNat < 2 ^ 63; have := hok.len; omega)
  rw [W64_sint_nat _ h0] at hans
  unfold rangeOutcome
  iintro (⟨%Hlt, -, -⟩ | ⟨-, -, %Hn, #He⟩ | ⟨-, %Herr, H⟩)
  · rw [hrev, h00] at Hlt; omega
  · ihave %He' := mvcc.errorfIs_ne_nil err $$ He
    imodintro; ileft; ipureintro; exact ⟨Hn, He'⟩
  rw [hco, hfk, hRR, hlim, rangeTaken_nonpos _ _ _ _ _ _ (by rw [h00]; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  icases H with ⟨%kvs, Hr, Hkvs⟩
  unfold rangeKvs
  icases Hkvs with ⟨%ps, Hps, %Hlen, Hzip⟩
  imod zip_kvsIs _ _ ps _ _ hans Hlen $$ Hzip with Hk
  imodintro
  iright
  isplitl []
  · ipureintro; exact Herr
  iexists kvs, kind.readRev, _, ps
  iframe Hr Hps
  unfold kindState
  iexact Hk

set_option goose.wp.unfoldSliceLiterals true in
/-- **A slice literal is not `nil`** (Perennial's `wp_slice_literal`, keeping the allocation's
`typedPointsto_not_null`): `mkGteRange`'s `[]byte{}` is the empty, non-nil slice, which mvcc
reads as no upper bound. -/
theorem wp_slice_literal_nn {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {st t : go.GoType}
    [IntoValTyped (GF := GF) V t] [st ↓u go.SliceType t]
    (l : List V) (kvs : List keyed_element) (Φ : val → IProp GF) :
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType (go.arrayLiteralSize kvs) t))))
          (Val (LiteralValueV kvs)))
      {{ v, ⌜v = #(array.mk (go.arrayLiteralSize kvs) l)⌝ ∗
        (∀ sl_ptr : Loc, ⌜sl_ptr ≠ null⌝ -∗
          (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)) ↦* l ∗
            ownSliceCap V (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs))
              (W64 (go.arrayLiteralSize kvs))) (DFrac.own 1)) -∗
          Φ #(slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)))) }} ⊢
    WP (App (Val (GoInstruction (CompositeLiteral st))) (Val (LiteralValueV kvs))) {{ Φ }} := by
  iintro HΦ
  wp_pures
  by_cases hlen : go.arrayLiteralSize kvs < 2 ^ 63
  · rw [ite_eq_left hlen]
    wp_pures
    wp_alloc_auto
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.ArrayType _ t)))) (Val (LiteralValueV kvs)))
    wp_apply_core wp_wand $$ HΦ
    iintro %v ⟨%Hv, HΦ⟩
    subst Hv
    wp_auto
    have h0 : 0 ≤ go.arrayLiteralSize kvs := by
      unfold go.arrayLiteralSize; split; omega
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    have hz : W64 (go.arrayLiteralSize kvs) - W64 0 = W64 (go.arrayLiteralSize kvs) := by word
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, hz]
    wp_pures
    ihave %Hlen := array_len _ _ _ _ $$ tmp
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ tmp
    iapply HΦ $$ %tmp_ptr %Hnn
    isplitl [tmp]
    · iapply slice_array tmp_ptr _ (array.mk (go.arrayLiteralSize kvs) l) (by simp only; omega)
      iexact tmp
    · iapply ownSliceCap_empty _ rfl (by simp only; word)
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

end iris

section todo
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A context descriptor for `context.TODO()`'s context, which `rangeCtx true` ignores. -/
def todoCd : context.ContextDesc (IProp GF) :=
  { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }

end todo

end txn
end EtcdGrove
end Perennial
