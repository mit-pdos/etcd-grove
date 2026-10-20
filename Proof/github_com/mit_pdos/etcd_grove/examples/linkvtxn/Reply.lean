/-
Lean-first (no Rocq counterpart).

# linkvtxn: `call`'s output from a reply (linkv-txn stage F)

The `Output` `call` builds from a successful reply, as a function of the reply's fields
(`getOut`, `listOut`, `delOut`, `txnOut` with `tresOf` per response), and, for a reply whose fields
are the server's at a good state `σ` (what the client's reply lemmas say,
`client/v3/ReplyValues.lean`), that it is the model's answer at `σ` (`outAt`): `getOut_eq`,
`listOut_eq`, `putOut_eq`, `delOut_eq`, `txnOut_eq`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Inv
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Client
public import Proof.go_etcd_io.etcd.client.v3.ReplyValues

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open github_com.mit_pdos.etcd_grove.examples.linkvtxn
open mvcc

section reply
variable [ext : FfiSyntax]

/-- A key-value's `VR`, as `vrOf` builds it. -/
def kvVR (kv : EtcdKv) : VR := ⟨kv.value, kv.modRev, kv.version⟩

theorem kvVR_eq (kv : EtcdKv) : kvVR kv = encVR (linkv.absVR kv) := rfl

/-- **A get's output**: the header revision, the first key-value if any. -/
def getOut (rev : w64) : List EtcdKv → Output
  | [] => { zOut with Rev' := rev }
  | kv :: _ => { zOut with Rev' := rev, Found' := true, R' := kvVR kv }

/-- **A list's output**: the header revision, every key-value. -/
def listOut (rev : w64) (kvs : List EtcdKv) : Output :=
  withKVsL { zOut with Rev' := rev } (kvs.map fun kv => (⟨kv.key, kvVR kv⟩ : KV))

/-- **A delete's output**: the header revision and the count. -/
def delOut (rev n : w64) : Output := { zOut with Rev' := rev, N' := n }

/-- **A transaction operation's result**, from its operation's kind and its response. -/
def tresOf (op : TOp) (m : OpRespM) : TRes :=
  if op.Kind' = W64 0 then
    match m with
    | .range _ (kv :: _) _ _ => getRes (kvVR kv, true)
    | _ => getRes (zVR, false)
  else if op.Kind' = W64 1 then putRes
  else
    match m with
    | .delete _ n _ => delRes n
    | _ => delRes (W64 0)

/-- **A transaction's output**: the header revision, the verdict, each response's result. -/
def txnOut (rev : w64) (ok : Bool) (ops : List TOp) (ms : List OpRespM) : Output :=
  withResL { zOut with Rev' := rev, Ok' := ok } (List.zipWith tresOf ops ms)

/-! ## Against the model -/

theorem getOut_eq (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess) (k : GoString) :
    getOut (W64 (σ.rev : Int)) (σ.kvs.filter fun v => decide (v.key = k)) = outAt (.get k) σ := by
  unfold outAt
  simp only [linkv.mStep, linkv.absSt, linkv.absM]
  cases hf : findKey k σ.kvs with
  | none =>
    rw [client.filter_key_of_findKey_none k σ.kvs hf]
    rfl
  | some kv =>
    rw [client.filter_key_of_findKey k σ.kvs hs kv hf]
    rfl

theorem listOut_eq (σ : KVState) (h : GoodKV σ) :
    listOut (W64 (σ.rev : Int)) (σ.kvs.filter fun v => inRange listFrom listTo v.key) =
      outAt .list σ := by
  unfold outAt
  rw [linkv.mStep_list_out wks wks_sorted listFrom listTo wks_inRange σ h.1 h.2]
  simp only [listOut, outOf, List.map_map]
  rfl

theorem putOut_eq (σ : KVState) (k v : GoString) :
    ({ zOut with Rev' := W64 ((σ.rev + 1 : Nat) : Int) } : Output) = outAt (.put k v) σ := by
  unfold outAt
  rw [linkv.mStep_put_out]
  rfl

theorem delOut_eq (σ : KVState) (h : GoodKV σ) (k : GoString) :
    delOut (W64 ((kvOpStep (.deleteRange (linkv.delOp k)) σ).rev : Int))
        (W64 ((rangeIn σ.kvs (linkv.delOp k)).length : Int)) = outAt (.del k) σ := by
  unfold outAt
  rw [linkv.mStep_del_out wks listFrom listTo σ h.1 k]
  rfl

/-- A plain get's answer is its selection. -/
theorem rangeKvsOk_getOp (k : GoString) (sel kvs : List EtcdKv)
    (h : rangeKvsOk (linkv.getOp k) sel kvs) : kvs = sel := by
  obtain ⟨l, -, h0, -, -, hk⟩ := h
  have hord : (linkv.getOp k).effSortOrder = W64 0 := by simp [OpFull.effSortOrder]
  rw [h0 hord] at hk
  rw [hk]
  simp [txn.rangeOpOf, OpFull.newOp, OpModel.zero]

/-- A transaction operation's result, against the model's. -/
theorem tresOf_eq (op : TOp) (mop : linkv.MOp GoString GoString) (hop : decTOp op = some mop)
    (res : TxnOpResult) (m : OpRespM) (h : client.opRespRel false (linkv.tOpOf mop) res m) :
    tresOf op m = encRes (linkv.resOf res) := by
  unfold decTOp at hop
  by_cases h0 : op.Kind' = W64 0
  · rw [if_pos h0] at hop
    cases hop
    simp only [linkv.tOpOf] at h
    match res, m, h with
    | .range sel n, .range _ kvs more count, h =>
      simp only [client.opRespRel, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨-, kvs', hk, rfl⟩ := h
      rw [rangeKvsOk_getOp _ _ _ hk]
      have hl : txn.leaseZ (txn.fastKeysOnly (linkv.getOp op.Key')) = id := by
        funext v; simp [txn.leaseZ, txn.fastKeysOnly, txn.rangeOpOf, OpFull.newOp]
      rw [hl, List.map_id]
      simp only [tresOf, if_pos h0, linkv.resOf]
      cases sel <;> rfl
  · rw [if_neg h0] at hop
    by_cases h1 : op.Kind' = W64 1
    · rw [if_pos h1] at hop
      cases hop
      simp only [linkv.tOpOf] at h
      match res, m, h with
      | .put, .put _ _, _ => simp only [tresOf, if_neg h0, if_pos h1]; rfl
    · rw [if_neg h1] at hop
      have h2 : op.Kind' = W64 2 := by
        by_cases e : op.Kind' = W64 2
        · exact e
        · rw [if_neg e] at hop; cases hop
      rw [if_pos h2] at hop
      cases hop
      simp only [linkv.tOpOf] at h
      match res, m, h with
      | .delete n, .delete _ d _, h =>
        simp only [client.opRespRel] at h
        subst h
        simp only [tresOf, if_neg h0, if_neg h1]
        rfl

theorem tresOf_zip (ops : List TOp) (mops : List (linkv.MOp GoString GoString))
    (hops : decAll decTOp ops = some mops) :
    ∀ (rs : List TxnOpResult) (ms : List OpRespM),
      client.opRespsRel false (mops.map linkv.tOpOf) rs ms →
      List.zipWith tresOf ops ms = (rs.map linkv.resOf).map encRes := by
  induction ops generalizing mops with
  | nil =>
    simp only [decAll, Option.some.injEq] at hops
    subst hops
    intro rs ms h
    match rs, ms, h with
    | [], [], _ => rfl
    | [], _ :: _, h => simp [client.opRespsRel] at h
    | _ :: _, _, h => simp [client.opRespsRel] at h
  | cons op ops ih =>
    simp only [decAll] at hops
    cases hf : decTOp op with
    | none => rw [hf] at hops; cases hops
    | some mop =>
      rw [hf] at hops
      cases hr : decAll decTOp ops with
      | none => rw [hr] at hops; cases hops
      | some mops' =>
        rw [hr] at hops
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hops
        subst hops
        intro rs ms h
        match rs, ms, h with
        | [], _, h => simp [client.opRespsRel] at h
        | _ :: _, [], h => simp [client.opRespsRel] at h
        | r :: rs, m :: ms, h =>
          simp only [List.map_cons, client.opRespsRel] at h
          simp only [List.zipWith_cons_cons, List.map_cons]
          rw [tresOf_eq op mop hf r m h.1, ih mops' hr rs ms h.2]

/-- **A transaction's output**, against the model's: its Go operations decode to the model's
`t` and `e`, its responses are the server's run of the branch at `σ`, its verdict the run's, its
revision the state's after the run. -/
theorem txnOut_eq (σ : KVState) (h : GoodKV σ) (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (tops eops : List TOp)
    (ht : decAll decTOp tops = some t) (he : decAll decTOp eops = some e)
    (ok : Bool) (ms : List OpRespM)
    (hok : ok = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).1)
    (hrel : client.opRespsRel false ((linkv.txnOf cs t e).branch ok)
      (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).2.2 ms) :
    txnOut (W64 ((kvOpStep (opIn (.txn cs t e)) σ).rev : Int)) ok (if ok then tops else eops) ms =
      outAt (.txn cs t e) σ := by
  unfold outAt
  rw [linkv.mStep_txn_out wks listFrom listTo σ h.1 cs t e, ← hok]
  simp only [txnOut, outOf]
  congr 1
  have hb : (linkv.txnOf cs t e).branch ok = (if ok then t else e).map linkv.tOpOf := by
    unfold linkv.txnOf TxnModel.branch
    cases ok <;> rfl
  rw [hb] at hrel
  cases ok
  · exact tresOf_zip eops e he _ ms hrel
  · exact tresOf_zip tops t ht _ ms hrel

end reply

end linkvtxn
end EtcdGrove
end Perennial
