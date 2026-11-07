/-
**Per-type prototype: `TxnRequest`'s request model is satisfiable** (stage A, CP1; the Scope's V
for `ProtoMsg`, `[v5]`'s `pbTxnRequest`): `pbTxnRequestT`, today's `pbTxnRequest` (`InvKVConn.lean`)
with its normalizing store `txnReqTree`, and `pbTxnRequestT_reqSat : pbTxnRequestT.ReqSat`.

- **The store** is a mutual tree over the transaction model: the request's comparisons
  (`cmpTree`: `Result`, `Target`, `Key`, `RangeEnd` `nil` if empty, the operand's oneof wrapper of
  the target's kind, always allocated), its `Success` and `Failure` operations (`reqOpTree`: a
  `RequestOp` whose oneof wraps a fresh `RangeRequest`, `PutRequest`, `DeleteRangeRequest` or, for a
  nested transaction, a fresh `TxnRequest` built the same way, recursively), each slice `nil` if
  empty. A put is stored from the model's `TxnOp` (`putOfOp`: the request `putTxnOp` maps back to
  it, without `PrevKv`, which the model forgets); a get and a delete from their `OpFull`, read
  back (`getStrct`, `delStrct`).
- **What the sender gives the store** (pure, `OpsOk`): each get's `OpFull` is a range request's
  (`rangeReqAt`'s `rangeOpOf`), each delete's a delete request's, and, from the request's `wireLen`
  premise (`txnWireLen t < grpcMsgMax`), every key shorter than `2 ^ 32` (the decoded copy's
  `sint.Z len < 2 ^ 63 - 1`) and the deletes of each branch fewer than `2 ^ 63` (`txnWireOk`'s
  `delCountT` bound: `delCountT_le`, each delete counted in `txnWireLen`).
- **The decoded copy** is `txn.txnRequestIs` (every operation's `requestOpIs`, its put's size cache
  in an invariant allocated at mask `⊤`) and `txnWireOk` (every delete's `RangeEnd` `nil` or not
  empty, at every depth, read through the stored points-tos' agreement).
- The instance sets `wireLen := txnWireLen` explicitly, and `pbTxnRequestT_wireLen_ok` proves
  `∃ m, wireLen m < grpcMsgMax` (`[v6a]` item 5).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## What the sender gives the store (pure) -/

/-- A get's `OpFull` is a range request's (`rangeReqAt`'s). -/
def GetOk (o : OpFull) : Prop :=
  ∃ (k e : GoString) (rev limit : w64) (order target : w32) (ser ko co : Bool)
    (minM maxM minC maxC : w64), o = txn.rangeOpOf k e rev limit order target ser ko co minM maxM minC maxC

/-- A delete's `OpFull` is a delete request's (`deleteReqAt`'s). -/
def DelOk (o : OpFull) : Prop := ∃ (k e : GoString) (pk : Bool), o = txn.deleteOpOf k e pk

/-- A put's key (the put requests' only bounded field). -/
def putKey : TxnOp → GoString
  | .put k _ _ => k
  | .putKeep k _ => k
  | .putIgnVal k _ => k
  | _ => []

mutual
/-- **An operation the store can build**: a get's and a delete's `OpFull` a request's, every key
shorter than `2 ^ 32`, at every depth. -/
def OpOk : TxnOp → Prop
  | .get o => GetOk o ∧ o.key.length < 2 ^ 32
  | .delete o => DelOk o ∧ o.key.length < 2 ^ 32
  | .txn cs ts es => (∀ c ∈ cs, c.key.length < 2 ^ 32) ∧ OpsOk ts ∧ OpsOk es
  | op => (putKey op).length < 2 ^ 32
/-- Each operation's `OpOk`. -/
def OpsOk : List TxnOp → Prop
  | [] => True
  | op :: ops => OpOk op ∧ OpsOk ops
end

theorem sum_lt_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp; omega

/-- **The deletes are counted in the request's bound** (each at least `wireSlack` bytes). -/
theorem delCountT_le : ∀ ops : List TxnOp, delCountT ops ≤ (ops.map TxnOp.wireLen).sum
  | [] => by simp [delCountT]
  | .delete o :: us => by
    have := delCountT_le us
    simp only [delCountT, List.map_cons, List.sum_cons, TxnOp.wireLen, opWireLen, wireSlack]
    omega
  | .txn cs ts es :: us => by
    have h1 := delCountT_le ts
    have h2 := delCountT_le es
    have h3 := delCountT_le us
    simp only [delCountT, List.map_cons, List.sum_cons, TxnOp.wireLen]
    omega
  | .get o :: us => by
    have := delCountT_le us
    simp only [delCountT, List.map_cons, List.sum_cons]; omega
  | .put _ _ _ :: us => by
    have := delCountT_le us
    simp only [delCountT, List.map_cons, List.sum_cons]; omega
  | .putKeep _ _ :: us => by
    have := delCountT_le us
    simp only [delCountT, List.map_cons, List.sum_cons]; omega
  | .putIgnVal _ _ :: us => by
    have := delCountT_le us
    simp only [delCountT, List.map_cons, List.sum_cons]; omega


section send
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem rangeReqAt_ok (r : Loc) (o : OpFull) : rangeReqAt (GF := GF) r o ⊢ ⌜GetOk o⌝ := by
  unfold rangeReqAt
  iintro ⟨-, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM,
    %minC, %maxC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %Ho⟩
  ipureintro; exact ⟨k, e, rev, limit, order, target, ser, ko, co, minM, maxM, minC, maxC, Ho⟩

theorem deleteReqAt_ok (d : Loc) (o : OpFull) : deleteReqAt (GF := GF) d o ⊢ ⌜DelOk o⌝ := by
  unfold deleteReqAt
  iintro ⟨-, %ksl, %esl, %k, %e, %pk, -, -, -, -, -, %Ho⟩
  ipureintro; exact ⟨k, e, pk, Ho⟩

theorem sum_map_lt {α : Type} (f : α → Nat) {l : List α} {a : α} (h : a ∈ l) (hs : (l.map f).sum < 2 ^ 32) :
    f a < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (sum_lt_of_mem (List.mem_map_of_mem h)) hs

mutual
/-- **The sender's operation is one the store can build**, given the request's bound. -/
theorem reqOpAt_ok : ∀ (p : Loc) (op : TxnOp),
    reqOpAt (GF := GF) p op ⊢ ⌜op.wireLen < 2 ^ 32 → OpOk op⌝
  | p, .get o => by
    unfold reqOpAt
    iintro ⟨-, %w, %r, -, -, Hr⟩
    ihave %H := rangeReqAt_ok r o $$ Hr
    ipureintro; intro hw
    simp only [OpOk]
    refine ⟨H, ?_⟩
    simp only [TxnOp.wireLen, opWireLen] at hw; omega
  | p, .delete o => by
    unfold reqOpAt
    iintro ⟨-, %w, %r, -, -, Hr⟩
    ihave %H := deleteReqAt_ok r o $$ Hr
    ipureintro; intro hw
    simp only [OpOk]
    refine ⟨H, ?_⟩
    simp only [TxnOp.wireLen, opWireLen] at hw; omega
  | p, .put k v l => by
    iintro -; ipureintro; intro hw
    simp only [OpOk, putKey]; simp only [TxnOp.wireLen] at hw; omega
  | p, .putKeep k v => by
    iintro -; ipureintro; intro hw
    simp only [OpOk, putKey]; simp only [TxnOp.wireLen] at hw; omega
  | p, .putIgnVal k l => by
    iintro -; ipureintro; intro hw
    simp only [OpOk, putKey]; simp only [TxnOp.wireLen] at hw; omega
  | p, .txn cs ts es => by
    unfold reqOpAt
    iintro ⟨-, %w, %r, %csl, %ssl, %fsl, %cps, %sps, %fps, -, -, -, -, -, -, -, -, #Hs, -, -, #Hf⟩
    ihave %H1 := reqOpsAt_ok sps ts $$ Hs
    ihave %H2 := reqOpsAt_ok fps es $$ Hf
    ipureintro; intro hw
    simp only [TxnOp.wireLen] at hw
    simp only [OpOk]
    refine ⟨fun c hc => ?_, H1 (by omega), H2 (by omega)⟩
    have := sum_map_lt cmpWireLen hc (by omega)
    simp only [cmpWireLen] at this; omega
theorem reqOpsAt_ok : ∀ (ps : List Loc) (ops : List TxnOp),
    reqOpsAt (GF := GF) ps ops ⊢ ⌜(ops.map TxnOp.wireLen).sum < 2 ^ 32 → OpsOk ops⌝
  | [], [] => by iintro -; ipureintro; intro; simp [OpsOk]
  | p :: ps, op :: ops => by
    unfold reqOpsAt
    iintro ⟨#H1, #H2⟩
    ihave %h1 := reqOpAt_ok p op $$ H1
    ihave %h2 := reqOpsAt_ok ps ops $$ H2
    ipureintro; intro hw
    simp only [List.map_cons, List.sum_cons] at hw
    exact ⟨h1 (by omega), h2 (by omega)⟩
  | [], _ :: _ => by unfold reqOpsAt; iintro %H; cases H
  | _ :: _, [] => by unfold reqOpsAt; iintro %H; cases H
end

end send


/-! ## The store -/

section trees
variable [GooseExts] [GoGlobalContext]

/-- The type of a comparison's operand wrapper (`TargetUnion`'s dynamic type). -/
def unionTy : CmpTarget → go.GoType
  | .value => go.GoType.PointerType etcdserverpb.Compare_Value.ty
  | .version => go.GoType.PointerType etcdserverpb.Compare_Version.ty
  | .create => go.GoType.PointerType etcdserverpb.Compare_CreateRevision.ty
  | .mod => go.GoType.PointerType etcdserverpb.Compare_ModRevision.ty
  | .lease => go.GoType.PointerType etcdserverpb.Compare_Lease.ty

/-- **The store of a comparison's operand**: the target's wrapper, always allocated. -/
def unionTree (c : CmpModel) : VTree :=
  match c.target with
  | .value => .ptr etcdserverpb.Compare_Value.ty (.strct etcdserverpb.Compare_Value.ty
      [(go!"Value", go.GoType.SliceType go.byte)] [bytesTree go.byte c.val])
  | .version => .ptr etcdserverpb.Compare_Version.ty (.strct etcdserverpb.Compare_Version.ty
      [(go!"Version", go.int64)] [.leaf #c.num])
  | .create => .ptr etcdserverpb.Compare_CreateRevision.ty
      (.strct etcdserverpb.Compare_CreateRevision.ty [(go!"CreateRevision", go.int64)] [.leaf #c.num])
  | .mod => .ptr etcdserverpb.Compare_ModRevision.ty
      (.strct etcdserverpb.Compare_ModRevision.ty [(go!"ModRevision", go.int64)] [.leaf #c.num])
  | .lease => .ptr etcdserverpb.Compare_Lease.ty (.strct etcdserverpb.Compare_Lease.ty
      [(go!"Lease", go.int64)] [.leaf #c.num])

/-- **The store of a comparison** (its key and range end `nil` if empty). -/
def cmpTree (c : CmpModel) : VTree :=
  .ptr etcdserverpb.Compare.ty (.strct etcdserverpb.Compare.ty
    [(go!"Result", etcdserverpb.Compare_CompareResult.ty),
     (go!"Target", etcdserverpb.Compare_CompareTarget.ty),
     (go!"Key", go.GoType.SliceType go.byte), (go!"TargetUnion", unionTy c.target),
     (go!"RangeEnd", go.GoType.SliceType go.byte)]
    [.leaf #c.op.code, .leaf #c.target.code, bytesTree go.byte c.key, unionTree c,
     bytesTree go.byte c.rangeEnd])

/-- **The store of a get's request** (its fields read back from the get's `OpFull`). -/
def getStrct (o : OpFull) : VTree :=
  .strct etcdserverpb.RangeRequest.ty
    [(go!"Key", go.GoType.SliceType go.byte), (go!"RangeEnd", go.GoType.SliceType go.byte),
     (go!"Limit", go.int64), (go!"Revision", go.int64),
     (go!"SortOrder", etcdserverpb.RangeRequest_SortOrder.ty),
     (go!"SortTarget", etcdserverpb.RangeRequest_SortTarget.ty),
     (go!"Serializable", go.bool), (go!"KeysOnly", go.bool), (go!"CountOnly", go.bool),
     (go!"MinModRevision", go.int64), (go!"MaxModRevision", go.int64),
     (go!"MinCreateRevision", go.int64), (go!"MaxCreateRevision", go.int64)]
    [bytesTree go.byte o.key, bytesTree go.byte o.base.rangeEnd, .leaf #o.base.limit,
     .leaf #o.base.rev, .leaf #(W32 (uint.Z o.sortOrder)), .leaf #(W32 (uint.Z o.sortTarget)),
     .leaf #o.base.serializable, .leaf #o.keysOnly, .leaf #o.base.countOnly,
     .leaf #o.base.minModRev, .leaf #o.base.maxModRev, .leaf #o.base.minCreateRev,
     .leaf #o.base.maxCreateRev]

/-- **The store of a delete's request.** -/
def delStrct (o : OpFull) : VTree :=
  .strct etcdserverpb.DeleteRangeRequest.ty
    [(go!"Key", go.GoType.SliceType go.byte), (go!"RangeEnd", go.GoType.SliceType go.byte),
     (go!"PrevKv", go.bool)]
    [bytesTree go.byte o.key, bytesTree go.byte o.base.rangeEnd, .leaf #o.base.prevKV]

/-- **A put's request from the model's operation** (`putTxnOp` maps it back: `putTxnOp_putOfOp`). -/
def putOfOp : TxnOp → OpFull
  | .put k v l => txn.putOpOf k v l false false false
  | .putKeep k v => txn.putOpOf k v (W64 0) false false true
  | .putIgnVal k none => txn.putOpOf k [] (W64 0) false true true
  | .putIgnVal k (some l) => txn.putOpOf k [] l false true false
  | _ => txn.putOpOf [] [] (W64 0) false false false

/-- **A `RequestOp` whose oneof wraps (`wty`, its field `fname`) a fresh request.** -/
def wrapTree (wty : go.GoType) (fname : GoString) (innerTy : go.GoType) (inner : VTree) : VTree :=
  .ptr etcdserverpb.RequestOp.ty (.strct etcdserverpb.RequestOp.ty
    [(go!"Request", go.GoType.PointerType wty)]
    [.ptr wty (.strct wty [(fname, go.GoType.PointerType innerTy)] [inner])])

/-- **A transaction request's fields**: its comparisons, its branches' stores `tsT`, `esT`. -/
def txnStrct (cs : List CmpModel) (tsT esT : VTree) : VTree :=
  .strct etcdserverpb.TxnRequest.ty
    [(go!"Compare", go.GoType.SliceType (go.GoType.PointerType etcdserverpb.Compare.ty)),
     (go!"Success", go.GoType.SliceType (go.GoType.PointerType etcdserverpb.RequestOp.ty)),
     (go!"Failure", go.GoType.SliceType (go.GoType.PointerType etcdserverpb.RequestOp.ty))]
    [sliceTree (go.GoType.PointerType etcdserverpb.Compare.ty) (cs.map cmpTree), tsT, esT]

mutual
/-- **The store of an operation** (a nested transaction's recursively). -/
def reqOpTree : TxnOp → VTree
  | .get o => wrapTree etcdserverpb.RequestOp_RequestRange.ty go!"RequestRange"
      etcdserverpb.RangeRequest.ty (.ptr etcdserverpb.RangeRequest.ty (getStrct o))
  | .delete o => wrapTree etcdserverpb.RequestOp_RequestDeleteRange.ty go!"RequestDeleteRange"
      etcdserverpb.DeleteRangeRequest.ty (.ptr etcdserverpb.DeleteRangeRequest.ty (delStrct o))
  | .txn cs ts es => wrapTree etcdserverpb.RequestOp_RequestTxn.ty go!"RequestTxn"
      etcdserverpb.TxnRequest.ty (.ptr etcdserverpb.TxnRequest.ty (txnStrct cs
        (sliceTree (go.GoType.PointerType etcdserverpb.RequestOp.ty) (reqOpsTree ts))
        (sliceTree (go.GoType.PointerType etcdserverpb.RequestOp.ty) (reqOpsTree es))))
  | op => wrapTree etcdserverpb.RequestOp_RequestPut.ty go!"RequestPut"
      etcdserverpb.PutRequest.ty (.ptr etcdserverpb.PutRequest.ty (putReqTree (putOfOp op)))
/-- The stores of operations, in order. -/
def reqOpsTree : List TxnOp → List VTree
  | [] => []
  | op :: ops => reqOpTree op :: reqOpsTree ops
end

/-- **The store of a transaction request.** -/
def txnReqTree (t : TxnModel) : VTree :=
  txnStrct t.cmps (sliceTree (go.GoType.PointerType etcdserverpb.RequestOp.ty) (reqOpsTree t.thenOps))
    (sliceTree (go.GoType.PointerType etcdserverpb.RequestOp.ty) (reqOpsTree t.elseOps))

theorem reqOpsTree_length : ∀ ops : List TxnOp, (reqOpsTree ops).length = ops.length
  | [] => rfl
  | _ :: ops => by simp only [reqOpsTree, List.length_cons, reqOpsTree_length ops]

end trees

theorem w32_of_w64_sext (x : w32) : W32 (uint.Z (W64 (sint.Z x))) = x := by
  word

/-- A get the sender holds is read back by its request's fields. -/
theorem getOk_eq {o : OpFull} (h : GetOk o) :
    o = txn.rangeOpOf o.key o.base.rangeEnd o.base.rev o.base.limit (W32 (uint.Z o.sortOrder))
      (W32 (uint.Z o.sortTarget)) o.base.serializable o.keysOnly o.base.countOnly o.base.minModRev
      o.base.maxModRev o.base.minCreateRev o.base.maxCreateRev := by
  obtain ⟨k, e, rev, limit, order, target, ser, ko, co, minM, maxM, minC, maxC, rfl⟩ := h
  simp only [txn.rangeOpOf, w32_of_w64_sext]
  rfl

/-- A delete the sender holds is read back by its request's fields. -/
theorem delOk_eq {o : OpFull} (h : DelOk o) : o = txn.deleteOpOf o.key o.base.rangeEnd o.base.prevKV := by
  obtain ⟨k, e, pk, rfl⟩ := h
  simp only [txn.deleteOpOf]
  rfl

/-- `putTxnOp` maps a put's stored request back to it. -/
theorem putTxnOp_putOfOp (op : TxnOp) (h1 : ∀ o, op ≠ .get o) (h2 : ∀ o, op ≠ .delete o)
    (h3 : ∀ cs ts es, op ≠ .txn cs ts es) : txn.putTxnOp (putOfOp op) = op := by
  cases op with
  | get o => exact absurd rfl (h1 o)
  | delete o => exact absurd rfl (h2 o)
  | txn cs ts es => exact absurd rfl (h3 cs ts es)
  | put k v l => simp [putOfOp, txn.putTxnOp, txn.putOpOf]
  | putKeep k v => simp [putOfOp, txn.putTxnOp, txn.putOpOf]
  | putIgnVal k l => cases l <;> simp [putOfOp, txn.putTxnOp, txn.putOpOf]

/-- What `rangeEndOf` reads of a stored range end (`nil` if empty). -/
theorem rangeEndOf_stored (sl : GoSlice) (e : GoString) (hnil : e = [] → sl = slice.nil)
    (hlen : e.length = sint.nat sl.len) : txn.rangeEndOf sl e = e ∧ (sl = slice.nil ∨ sl.len ≠ W64 0) := by
  by_cases he : e = []
  · subst he
    have := hnil rfl
    subst this
    simp [txn.rangeEndOf]
  · have hne : sl ≠ slice.nil := by
      intro h; subst h
      apply he; apply List.eq_nil_of_length_eq_zero; rw [hlen]; rfl
    refine ⟨by simp [txn.rangeEndOf, hne, he], Or.inr ?_⟩
    intro h0
    apply he; apply List.eq_nil_of_length_eq_zero; rw [hlen, h0]; rfl

/-- A stored key's length bound (`requestOpIs`'s `sint.Z len < 2 ^ 63 - 1`). -/
theorem len_bound (sl : GoSlice) (e : GoString) (hk : e.length < 2 ^ 32)
    (hlen : e.length = sint.nat sl.len) : sint.Z sl.len < 2 ^ 63 - 1 := by
  have e1 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
  rw [e1] at hlen
  generalize sint.Z sl.len = n at hlen ⊢
  omega


/-! ## The store's WPs -/

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- A stored `bytes` field, frozen, read back. -/
theorem bytes_freeze (sl : GoSlice) (e : GoString) (hnil : e = [] → sl = slice.nil) :
    (sl ↦* e : IProp GF) ⊢ |={⊤}=> sl ↦*□ e ∗
      ⌜txn.rangeEndOf sl e = e ∧ (sl = slice.nil ∨ sl.len ≠ W64 0) ∧ e.length = sint.nat sl.len ∧
        0 ≤ sint.Z sl.len⌝ := by
  iintro H
  ihave %Hl := ownSlice_len _ _ _ $$ H
  imod ownSlice_persist _ _ _ $$ H with #H
  imodintro
  iframe H
  ipureintro
  exact ⟨(rangeEndOf_stored sl e hnil Hl.1).1, (rangeEndOf_stored sl e hnil Hl.1).2, Hl.1, Hl.2⟩

theorem treeWp_union (c : CmpModel) (Φ : val → IProp GF) :
    (∀ w : Loc, ⌜w ≠ null⌝ -∗ compareUnionAt (interface.mkOk (unionTy c.target) #w) c -∗ Φ #w) ⊢
      treeWp (unionTree c) Φ := by
  iintro H
  rcases c with ⟨key, re, target, op, num, val⟩
  cases target with
  | value =>
    simp only [unionTree]
    iapply (treeWp_ptr_fupd (V := etcdserverpb.Compare_Value))
    simp only [treeWp, treeWpL]
    iapply treeWp_bytes
    iintro %vsl %Hv Hvs -
    isplitr
    · ipureintro; exact isPanic_intoVal vsl
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    ihave %Hnn := typedPointsto_not_null $$ Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HV, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ vsl).dfractional_persist _ $$ HV with #HV
    imod ownSlice_persist _ _ _ $$ Hvs with #Hvs
    imodintro
    iapply H $$ %w %Hnn
    unfold compareUnionAt
    iright
    iexists w, vsl
    iframe HV Hvs
    ipureintro; rfl
  | version =>
    simp only [unionTree]
    iapply (treeWp_ptr_fupd (V := etcdserverpb.Compare_Version))
    simp only [treeWp, treeWpL, isPanic_intoVal]
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    ihave %Hnn := typedPointsto_not_null $$ Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HV, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ num).dfractional_persist _ $$ HV with #HV
    imodintro
    iapply H $$ %w %Hnn
    unfold compareUnionAt
    iright
    iexists w
    iframe HV
    ipureintro; rfl
  | create =>
    simp only [unionTree]
    iapply (treeWp_ptr_fupd (V := etcdserverpb.Compare_CreateRevision))
    simp only [treeWp, treeWpL, isPanic_intoVal]
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    ihave %Hnn := typedPointsto_not_null $$ Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HV, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ num).dfractional_persist _ $$ HV with #HV
    imodintro
    iapply H $$ %w %Hnn
    unfold compareUnionAt
    iright
    iexists w
    iframe HV
    ipureintro; rfl
  | mod =>
    simp only [unionTree]
    iapply (treeWp_ptr_fupd (V := etcdserverpb.Compare_ModRevision))
    simp only [treeWp, treeWpL, isPanic_intoVal]
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    ihave %Hnn := typedPointsto_not_null $$ Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HV, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ num).dfractional_persist _ $$ HV with #HV
    imodintro
    iapply H $$ %w %Hnn
    unfold compareUnionAt
    iright
    iexists w
    iframe HV
    ipureintro; rfl
  | lease =>
    simp only [unionTree]
    iapply (treeWp_ptr_fupd (V := etcdserverpb.Compare_Lease))
    simp only [treeWp, treeWpL, isPanic_intoVal]
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    ihave %Hnn := typedPointsto_not_null $$ Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HV, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ num).dfractional_persist _ $$ HV with #HV
    imodintro
    iapply H $$ %w %Hnn
    unfold compareUnionAt
    iright
    iexists w
    iframe HV
    ipureintro; rfl

theorem treeWp_cmp (c : CmpModel) (hk : c.key.length < 2 ^ 32) (Φ : val → IProp GF) :
    (∀ p : Loc, txn.compareIs p c -∗ Φ #p) ⊢ treeWp (cmpTree c) Φ := by
  iintro H
  unfold cmpTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.Compare))
  simp only [treeWp, treeWpL]
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_bytes
  iintro %ksl %Hk Hks -
  isplitr
  · ipureintro; exact isPanic_intoVal ksl
  iapply treeWp_union
  iintro %w %Hw Hu
  isplitr
  · ipureintro; exact isPanic_intoVal w
  iapply treeWp_bytes
  iintro %esl %He Hes -
  isplitr
  · ipureintro; exact isPanic_intoVal esl
  generalize ht : c.target = t
  cases t <;>
  · simp [unionTy, litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %p Hp
    ihave %Hnn := typedPointsto_not_null $$ Hp
    icases typedPointsto_split _ _ _ $$ Hp with Hp
    simp only [TypedPointsto.typedPointstoDef]
    icases Hp with ⟨-, HR, HT, HK, HTU, HRE, -, -, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ c.op.code).dfractional_persist _ $$ HR with #HR
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
    imod (typedPointsto_dfractional (GF := GF) _ ksl).dfractional_persist _ $$ HK with #HK
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HTU with #HTU
    imod (typedPointsto_dfractional (GF := GF) _ esl).dfractional_persist _ $$ HRE with #HRE
    imod bytes_freeze ksl c.key Hk.2 $$ Hks with ⟨#Hks, %Hk'⟩
    imod bytes_freeze esl c.rangeEnd He.2 $$ Hes with ⟨#Hes, %He'⟩
    imodintro
    iapply H
    unfold txn.compareIs
    simp only [ht]
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, esl, c.rangeEnd, _
    iframe HR HT HK Hks HRE Hes HTU Hu
    isplitr
    · ipureintro; exact He'.1.symm
    isplitr
    · ipureintro
      intro t w' h
      rw [interface_mkOk_inj] at h
      obtain ⟨-, h2⟩ := h
      cases go.IntoValInj.intoVal_inj (V := Loc) h2
      exact Hw
    · ipureintro; exact len_bound ksl c.key hk Hk'.2.2.1


/-- **A get's request, stored.** -/
theorem treeWp_get (o : OpFull) (hg : GetOk o) (hk : o.key.length < 2 ^ 32) (Φ : val → IProp GF) :
    (∀ r : Loc, txn.rangeRequestIs r o -∗ Φ #r) ⊢
      treeWp (.ptr etcdserverpb.RangeRequest.ty (getStrct o)) Φ := by
  iintro H
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RangeRequest))
  simp only [getStrct, treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hk Hks -
  isplitr
  · ipureintro; exact isPanic_intoVal ksl
  iapply treeWp_bytes
  iintro %esl %He Hes -
  isplitr
  · ipureintro; exact isPanic_intoVal esl
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HK, HE, HL, HR, HSO, HST, HS, HKO, HCO, H1, H2, H3, H4, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ ksl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ esl).dfractional_persist _ $$ HE with #HE
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HL with #HL
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HR with #HR
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HSO with #HSO
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HST with #HST
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HS with #HS
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HKO with #HKO
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HCO with #HCO
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ H1 with #H1
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ H2 with #H2
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ H3 with #H3
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ H4 with #H4
  imod bytes_freeze ksl o.key Hk.2 $$ Hks with ⟨#Hks, %Hk'⟩
  imod bytes_freeze esl o.base.rangeEnd He.2 $$ Hes with ⟨#Hes, %He'⟩
  imodintro
  iapply H
  unfold txn.rangeRequestIs
  isplitr
  · ipureintro; exact Hnn
  iexists ksl, esl, o.key, o.base.rangeEnd, o.base.rev, o.base.limit, _, _, o.base.serializable, o.keysOnly, o.base.countOnly, o.base.minModRev,
    o.base.maxModRev, o.base.minCreateRev, o.base.maxCreateRev
  iframe HK Hks HE Hes HL HR HSO HST HS HKO HCO H1 H2 H3 H4
  isplitr
  · ipureintro; rw [He'.1]; refine (getOk_eq hg).trans ?_; simp
  · ipureintro; exact len_bound ksl o.key hk Hk'.2.2.1


/-- **A delete's request, stored**, with its range end as decoded (`nil` or not empty) through any
points-to of the field. -/
theorem treeWp_del (o : OpFull) (hd : DelOk o) (hk : o.key.length < 2 ^ 32) (Φ : val → IProp GF) :
    (∀ d : Loc, txn.deleteRangeRequestIs d o -∗
      □ (∀ esl' : GoSlice, structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" d ↦□ esl' -∗
        ⌜esl' = slice.nil ∨ esl'.len ≠ W64 0⌝) -∗ Φ #d) ⊢
      treeWp (.ptr etcdserverpb.DeleteRangeRequest.ty (delStrct o)) Φ := by
  iintro H
  iapply (treeWp_ptr_fupd (V := etcdserverpb.DeleteRangeRequest))
  simp only [delStrct, treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hk Hks -
  isplitr
  · ipureintro; exact isPanic_intoVal ksl
  iapply treeWp_bytes
  iintro %esl %He Hes -
  isplitr
  · ipureintro; exact isPanic_intoVal esl
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HK, HE, HP, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ ksl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ esl).dfractional_persist _ $$ HE with #HE
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HP with #HP
  imod bytes_freeze ksl o.key Hk.2 $$ Hks with ⟨#Hks, %Hk'⟩
  imod bytes_freeze esl o.base.rangeEnd He.2 $$ Hes with ⟨#Hes, %He'⟩
  imodintro
  iapply H
  · unfold txn.deleteRangeRequestIs
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, esl, o.key, o.base.rangeEnd, _
    iframe HK Hks HE Hes HP
    isplitr
    · ipureintro; rw [He'.1]; refine (delOk_eq hd).trans ?_; simp
    · ipureintro; exact len_bound ksl o.key hk Hk'.2.2.1
  · imodintro
    iintro %esl' HE'
    ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ HE HE'
    subst Hag
    ipureintro; exact He'.2.1

/-- A put's stored request is read back by its fields. -/
theorem putOfOp_eq (op : TxnOp) :
    putOfOp op = txn.putOpOf (putOfOp op).key (putOfOp op).val (putOfOp op).leaseID
      (putOfOp op).base.prevKV (putOfOp op).ignoreValue (putOfOp op).ignoreLease := by
  unfold putOfOp
  split <;> rfl

/-- **A put's request, stored** (its size cache in an invariant, allocated at mask `⊤`). -/
theorem treeWp_put (op : TxnOp) (hk : (putOfOp op).key.length < 2 ^ 32) (Φ : val → IProp GF) :
    (∀ r : Loc, txn.putRequestIs r (putOfOp op) -∗ Φ #r) ⊢
      treeWp (.ptr etcdserverpb.PutRequest.ty (putReqTree (putOfOp op))) Φ := by
  iintro H
  iapply (treeWp_ptr_fupd (V := etcdserverpb.PutRequest))
  simp only [putReqTree, treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hk Hks -
  isplitr
  · ipureintro; exact isPanic_intoVal ksl
  iapply treeWp_bytes
  iintro %vsl %Hv Hvs -
  isplitr
  · ipureintro; exact isPanic_intoVal vsl
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HK, HV, HL, HP, HIV, HIL, -, HSC, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ ksl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ vsl).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HL with #HL
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HP with #HP
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HIV with #HIV
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HIL with #HIL
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hvs with #Hvs
  ihave Hinv : |={⊤}=> inv (nroot .@ "txn.putSizeCache")
      (∃ sc : w32, structFieldRef etcdserverpb.PutRequest go!"sizeCache" p ↦ sc) $$ [HSC]
  · iapply inv_alloc
    inext
    iexists _
    iexact HSC
  imod Hinv with #Hinv
  imodintro
  iapply H
  unfold txn.putRequestIs
  isplitr
  · ipureintro; exact Hnn
  iexists ksl, vsl, (putOfOp op).key, (putOfOp op).val, _, _, _, _
  iframe HK Hks HV Hvs HL HP HIV HIL Hinv
  isplitr
  · ipureintro; refine (putOfOp_eq op).trans ?_; simp
  · ipureintro; exact len_bound ksl _ hk Hkl.1


/-- **A `RequestOp` wrapping a fresh `RequestRange`** (its request's store `inner`, giving `Q`). -/
theorem treeWp_wrapRequestRange (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (wrapTree etcdserverpb.RequestOp_RequestRange.ty go!"RequestRange" etcdserverpb.RangeRequest.ty inner) Φ := by
  iintro H
  unfold wrapTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp_RequestRange))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply hin
  iintro %r Hr
  isplitr
  · ipureintro; exact isPanic_intoVal r
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %w Hw
  icases typedPointsto_split _ _ _ $$ Hw with Hw
  simp only [TypedPointsto.typedPointstoDef]
  icases Hw with ⟨HW, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ r).dfractional_persist _ $$ HW with #HW
  imodintro
  repeat (isplitr; · ipureintro; first | trivial | exact isPanic_intoVal w)
  try simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HR, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HR with #HR
  imodintro
  iapply H $$ %p %w %r %Hnn HR HW Hr

/-- **A `RequestOp` wrapping a fresh `RequestPut`** (its request's store `inner`, giving `Q`). -/
theorem treeWp_wrapRequestPut (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (wrapTree etcdserverpb.RequestOp_RequestPut.ty go!"RequestPut" etcdserverpb.PutRequest.ty inner) Φ := by
  iintro H
  unfold wrapTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp_RequestPut))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply hin
  iintro %r Hr
  isplitr
  · ipureintro; exact isPanic_intoVal r
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %w Hw
  icases typedPointsto_split _ _ _ $$ Hw with Hw
  simp only [TypedPointsto.typedPointstoDef]
  icases Hw with ⟨HW, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ r).dfractional_persist _ $$ HW with #HW
  imodintro
  repeat (isplitr; · ipureintro; first | trivial | exact isPanic_intoVal w)
  try simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HR, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HR with #HR
  imodintro
  iapply H $$ %p %w %r %Hnn HR HW Hr

/-- **A `RequestOp` wrapping a fresh `RequestDeleteRange`** (its request's store `inner`, giving `Q`). -/
theorem treeWp_wrapRequestDeleteRange (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (wrapTree etcdserverpb.RequestOp_RequestDeleteRange.ty go!"RequestDeleteRange" etcdserverpb.DeleteRangeRequest.ty inner) Φ := by
  iintro H
  unfold wrapTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp_RequestDeleteRange))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply hin
  iintro %r Hr
  isplitr
  · ipureintro; exact isPanic_intoVal r
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %w Hw
  icases typedPointsto_split _ _ _ $$ Hw with Hw
  simp only [TypedPointsto.typedPointstoDef]
  icases Hw with ⟨HW, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ r).dfractional_persist _ $$ HW with #HW
  imodintro
  repeat (isplitr; · ipureintro; first | trivial | exact isPanic_intoVal w)
  try simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HR, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HR with #HR
  imodintro
  iapply H $$ %p %w %r %Hnn HR HW Hr

/-- **A `RequestOp` wrapping a fresh `RequestTxn`** (its request's store `inner`, giving `Q`). -/
theorem treeWp_wrapRequestTxn (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (wrapTree etcdserverpb.RequestOp_RequestTxn.ty go!"RequestTxn" etcdserverpb.TxnRequest.ty inner) Φ := by
  iintro H
  unfold wrapTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RequestOp_RequestTxn))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply hin
  iintro %r Hr
  isplitr
  · ipureintro; exact isPanic_intoVal r
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %w Hw
  icases typedPointsto_split _ _ _ $$ Hw with Hw
  simp only [TypedPointsto.typedPointstoDef]
  icases Hw with ⟨HW, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ r).dfractional_persist _ $$ HW with #HW
  imodintro
  repeat (isplitr; · ipureintro; first | trivial | exact isPanic_intoVal w)
  try simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HR, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HR with #HR
  imodintro
  iapply H $$ %p %w %r %Hnn HR HW Hr


/-! ### Repeated fields with a precondition, a transaction's fields -/

/-- `delWireAtT` is persistent (as `Results.lean`'s, which this module does not import). -/
instance delWireAtT_persistent' (p : Loc) (op : TxnOp) :
    Persistent (delWireAtT (GF := GF) p op) := by
  cases op <;> unfold delWireAtT <;> infer_instance

instance delWiresAtT_persistent' (ps : List Loc) (ops : List TxnOp) :
    Persistent (delWiresAtT (GF := GF) ps ops) := by
  induction ops generalizing ps with
  | nil => cases ps <;> unfold delWiresAtT <;> infer_instance
  | cons op ops ih => cases ps <;> unfold delWiresAtT <;> infer_instance

/-- **What an operation's store gives**: its request read back, and its deletes as decoded. -/
def opR (op : TxnOp) (x : Loc) : IProp GF := iprop(txn.requestOpIs x op ∗ delWireAtT x op)

instance opR_persistent (op : TxnOp) (x : Loc) : Persistent (opR (GF := GF) op x) := by
  unfold opR; infer_instance

/-- **Trees of typed results, one per element satisfying `P`.** -/
theorem treeWpL_mapP {A V : Type} (f : A → VTree) (Q : A → V → IProp GF) (P : A → Prop)
    (hf : ∀ a, P a → ∀ Φ : val → IProp GF, (∀ x : V, Q a x -∗ Φ #x) ⊢ treeWp (f a) Φ) :
    ∀ (ys : List A), (∀ a ∈ ys, P a) → ∀ (acc : List val) (Ψ : List val → IProp GF),
    (∀ xs : List V, ([∗list] a;x ∈ ys;xs, Q a x) -∗ Ψ (acc ++ xs.map fun x => #x)) ⊢
      treeWpL (ys.map f) acc Ψ
  | [], _, acc, Ψ => by
    simp only [List.map_nil, treeWpL]
    iintro H
    ihave H := H $$ %([] : List V)
    simp only [List.map_nil, List.append_nil]
    iapply H
    iempintro
  | a :: ys, hP, acc, Ψ => by
    simp only [List.map_cons, treeWpL]
    iintro HΨ
    iapply hf a (hP a (List.mem_cons_self ..))
    iintro %x Hx
    isplitr
    · ipureintro; exact isPanic_intoVal x
    iapply treeWpL_mapP f Q P hf ys (fun b hb => hP b (List.mem_cons_of_mem _ hb)) (acc ++ [(#x)]) Ψ
    iintro %xs Hxs
    ihave H := HΨ $$ %(x :: xs) [Hx Hxs]
    · iframe
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
    iexact H

/-- **A repeated message field of trees**, given what the trees' values satisfy, `nil` if empty. -/
theorem treeWp_sliceL {A V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V ty] (ts : List VTree) (ys : List A) (Q : A → V → IProp GF)
    (hl : ts.length = ys.length)
    (hts : ∀ Ψ : List val → IProp GF,
      (∀ xs : List V, ([∗list] a;x ∈ ys;xs, Q a x) -∗ Ψ ([] ++ xs.map fun x => #x)) ⊢ treeWpL ts [] Ψ)
    (Φ : val → IProp GF) :
    (∀ (xs : List V) (sl : GoSlice), ⌜xs.length < 2 ^ 63 ∧ (xs = [] → sl = slice.nil)⌝ -∗
        ([∗list] a;x ∈ ys;xs, Q a x) -∗ sl ↦* xs -∗ ownSliceCap V sl (DFrac.own 1) -∗ Φ #sl) ⊢
      treeWp (sliceTree ty ts) Φ := by
  unfold sliceTree
  by_cases hts0 : ts = []
  · subst hts0
    have : ys = [] := List.eq_nil_of_length_eq_zero hl.symm
    subst this
    rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    simp only [treeWp]
    iintro H
    ihave Hs := ownSlice_nil (V := V) (GF := GF) (DFrac.own 1)
    ihave Hc := ownSliceCap_nil (V := V) (GF := GF)
    iapply H $$ %([] : List V) %slice.nil %(by simp) [] Hs Hc
    iempintro
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hts0)]
    simp only [treeWp]
    iintro H
    iapply hts
    iintro %xs Hxs
    ihave %Hl := BigSepL2.bigSepL2_length $$ Hxs
    simp only [List.nil_append]
    have hl' : ts.length = xs.length := hl.trans Hl
    rw [hl']
    iapply wp_sliceLit_vals xs Φ
    iintro %sl %Hlen Hs Hc
    have hys : ys ≠ [] := fun h => hts0 (List.eq_nil_of_length_eq_zero (by rw [hl, h]; rfl))
    iapply H $$ %xs %sl %(⟨Hlen, fun h => by subst h; exact absurd (List.eq_nil_of_length_eq_zero Hl) hys⟩ :
      xs.length < 2 ^ 63 ∧ (xs = [] → sl = slice.nil)) Hxs Hs Hc

theorem comparesIs_of_sepL2 (cs : List CmpModel) (ps : List Loc) :
    ([∗list] c;p ∈ cs;ps, txn.compareIs (GF := GF) p c) ⊢ txn.comparesIs ps cs := by
  iintro #H
  ihave %Hl := BigSepL2.bigSepL2_length $$ H
  unfold txn.comparesIs
  isplitr
  · ipureintro; exact Hl.symm
  imodintro
  iintro %i %p %c %Hp %Hc
  iapply (BigSepL2.bigSepL2_lookup Hc Hp) $$ H

theorem opsR_split : ∀ (ops : List TxnOp) (ps : List Loc),
    ([∗list] op;p ∈ ops;ps, opR (GF := GF) op p) ⊢ txn.requestOpsIs ps ops ∗ delWiresAtT ps ops
  | [], [] => by
    iintro -; unfold txn.requestOpsIs delWiresAtT; isplitr <;> iempintro
  | [], _ :: _ => by
    iintro H; ihave %Hl := BigSepL2.bigSepL2_length $$ H; simp at Hl
  | _ :: _, [] => by
    iintro H; ihave %Hl := BigSepL2.bigSepL2_length $$ H; simp at Hl
  | op :: ops, p :: ps => by
    iintro ⟨H12, Hs⟩
    iunfold opR at H12
    icases H12 with ⟨#H1, #H2⟩
    icases opsR_split ops ps $$ Hs with ⟨#H3, #H4⟩
    simp only [txn.requestOpsIs, delWiresAtT]
    iframe H1 H2 H3 H4

/-- **What a stored transaction request's fields give** (`p` its address). -/
def txnQ (p : Loc) (cs : List CmpModel) (ts es : List TxnOp) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ txn.txnFieldsIs p cs ts es ∗
    □ ∀ (ssl fsl : GoSlice) (sps fps : List Loc),
      structFieldRef etcdserverpb.TxnRequest go!"Success" p ↦□ ssl -∗ ssl ↦*□ sps -∗
      structFieldRef etcdserverpb.TxnRequest go!"Failure" p ↦□ fsl -∗ fsl ↦*□ fps -∗
      delWiresAtT sps ts ∗ delWiresAtT fps es)

/-- A branch's store: its operations' slice, each operation's `opR`. -/
def BranchWp (ops : List TxnOp) (bt : VTree) : Prop :=
  ∀ Φ : val → IProp GF,
    (∀ (xs : List Loc) (sl : GoSlice), ⌜xs.length < 2 ^ 63 ∧ (xs = [] → sl = slice.nil)⌝ -∗
      ([∗list] a;x ∈ ops;xs, opR a x) -∗ sl ↦* xs -∗ ownSliceCap Loc sl (DFrac.own 1) -∗ Φ #sl) ⊢
      treeWp bt Φ

/-- **A transaction request's fields, stored.** -/
theorem treeWp_txnStrct (cs : List CmpModel) (ts es : List TxnOp) (tsT esT : VTree)
    (hcs : ∀ c ∈ cs, c.key.length < 2 ^ 32) (hT : BranchWp (GF := GF) ts tsT)
    (hE : BranchWp (GF := GF) es esT) (Φ : val → IProp GF) :
    (∀ x : etcdserverpb.TxnRequest, (∀ p : Loc, p ↦ x ={⊤}=∗ txnQ p cs ts es) -∗ Φ #x) ⊢
      treeWp (txnStrct cs tsT esT) Φ := by
  iintro H
  simp only [txnStrct, treeWp, treeWpL]
  iapply (treeWp_sliceL (V := Loc) (cs.map cmpTree) cs (fun c x => txn.compareIs (GF := GF) x c)
    (by simp) (fun Ψ => treeWpL_mapP cmpTree _ _ (fun c hc Φ => treeWp_cmp c hc Φ) cs hcs [] Ψ))
  iintro %cxs %csl %Hc Hcs Hcsl -
  isplitr
  · ipureintro; exact isPanic_intoVal csl
  iapply (hT _)
  iintro %sxs %ssl %Hs Hss Hssl -
  isplitr
  · ipureintro; exact isPanic_intoVal ssl
  iapply (hE _)
  iintro %fxs %fsl %Hf Hfs Hfsl -
  isplitr
  · ipureintro; exact isPanic_intoVal fsl
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iapply H
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HC, HS, HF, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ csl).dfractional_persist _ $$ HC with #HC
  imod (typedPointsto_dfractional (GF := GF) _ ssl).dfractional_persist _ $$ HS with #HS
  imod (typedPointsto_dfractional (GF := GF) _ fsl).dfractional_persist _ $$ HF with #HF
  imod ownSlice_persist _ _ _ $$ Hcsl with #Hcsl
  imod ownSlice_persist _ _ _ $$ Hssl with #Hssl
  imod ownSlice_persist _ _ _ $$ Hfsl with #Hfsl
  ihave #Hcs := comparesIs_of_sepL2 cs cxs $$ Hcs
  icases opsR_split ts sxs $$ Hss with ⟨#Hss, #Hsw⟩
  icases opsR_split es fxs $$ Hfs with ⟨#Hfs, #Hfw⟩
  imodintro
  unfold txnQ txn.txnFieldsIs
  isplitr
  · ipureintro; exact Hnn
  isplitr
  · iexists csl, ssl, fsl, cxs, sxs, fxs
    iframe HC Hcsl Hcs HS Hssl Hss HF Hfsl Hfs
  imodintro
  iintro %ssl' %fsl' %sps' %fps' HS' Hssl' HF' Hfsl'
  ihave %E1 := typedPointsto_agree_wand _ _ _ _ _ $$ HS HS'
  subst E1
  ihave %E2 := typedPointsto_agree_wand _ _ _ _ _ $$ HF HF'
  subst E2
  ihave %E3 := ownSlice_agree _ _ _ _ _ $$ Hssl Hssl'
  subst E3
  ihave %E4 := ownSlice_agree _ _ _ _ _ $$ Hfsl Hfsl'
  subst E4
  iframe Hsw Hfw


/-- **A put operation, stored.** -/
theorem treeWp_reqOpPut (op : TxnOp) (hk : (putOfOp op).key.length < 2 ^ 32)
    (h1 : ∀ o, op ≠ .get o) (h2 : ∀ o, op ≠ .delete o) (h3 : ∀ cs ts es, op ≠ .txn cs ts es)
    (Φ : val → IProp GF) :
    (∀ p : Loc, opR op p -∗ Φ #p) ⊢
      treeWp (wrapTree etcdserverpb.RequestOp_RequestPut.ty go!"RequestPut"
        etcdserverpb.PutRequest.ty (.ptr etcdserverpb.PutRequest.ty (putReqTree (putOfOp op)))) Φ := by
  iintro H
  iapply (treeWp_wrapRequestPut _ (fun r => txn.putRequestIs (GF := GF) r (putOfOp op))
    (fun Ψ => treeWp_put op hk Ψ))
  iintro %p %w %r %Hnn #HR #HW #Hr
  iapply H
  have hop := putTxnOp_putOfOp op h1 h2 h3
  unfold opR
  cases op with
  | get o => exact absurd rfl (h1 o)
  | delete o => exact absurd rfl (h2 o)
  | txn cs ts es => exact absurd rfl (h3 cs ts es)
  | put k v l =>
    unfold txn.requestOpIs delWireAtT
    isplitr
    · imodintro
      isplitr
      · ipureintro; exact Hnn
      iexists _, w, r, putOfOp (.put k v l)
      iframe HR
      iright; ileft
      iframe HW Hr
      ipureintro; exact ⟨rfl, hop.symm⟩
    · ipureintro; trivial
  | putKeep k v =>
    unfold txn.requestOpIs delWireAtT
    isplitr
    · imodintro
      isplitr
      · ipureintro; exact Hnn
      iexists _, w, r, putOfOp (.putKeep k v)
      iframe HR
      iright; ileft
      iframe HW Hr
      ipureintro; exact ⟨rfl, hop.symm⟩
    · ipureintro; trivial
  | putIgnVal k l =>
    unfold txn.requestOpIs delWireAtT
    isplitr
    · imodintro
      isplitr
      · ipureintro; exact Hnn
      iexists _, w, r, putOfOp (.putIgnVal k l)
      iframe HR
      iright; ileft
      iframe HW Hr
      ipureintro; exact ⟨rfl, hop.symm⟩
    · ipureintro; trivial

mutual
/-- **An operation, stored**, a nested transaction's recursively. -/
theorem treeWp_reqOp : ∀ (op : TxnOp), OpOk op → ∀ Φ : val → IProp GF,
    (∀ p : Loc, opR op p -∗ Φ #p) ⊢ treeWp (reqOpTree op) Φ
  | .get o, hok, Φ => by
    simp only [OpOk] at hok
    iintro H
    simp only [reqOpTree]
    iapply (treeWp_wrapRequestRange _ (fun r => txn.rangeRequestIs r o)
      (fun Ψ => treeWp_get o hok.1 hok.2 Ψ))
    iintro %p %w %r %Hnn #HR #HW #Hr
    iapply H
    unfold opR txn.requestOpIs delWireAtT
    isplitr
    · imodintro
      isplitr
      · ipureintro; exact Hnn
      iexists _, w, r, o
      iframe HR
      ileft
      iframe HW Hr
      ipureintro; exact ⟨rfl, rfl⟩
    · ipureintro; trivial
  | .delete o, hok, Φ => by
    simp only [OpOk] at hok
    iintro H
    simp only [reqOpTree]
    iapply (treeWp_wrapRequestDeleteRange _ (fun r => iprop(txn.deleteRangeRequestIs r o ∗
        □ (∀ esl' : GoSlice, structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" r ↦□ esl' -∗
          ⌜esl' = slice.nil ∨ esl'.len ≠ W64 0⌝)))
      (fun Ψ => by
        iintro HΨ
        iapply (treeWp_del o hok.1 hok.2 Ψ)
        iintro %d Hd Hw
        iapply HΨ
        iframe Hd Hw))
    iintro %p %w %r %Hnn #HR #HW ⟨#Hr, #Hwand⟩
    iapply H
    unfold opR txn.requestOpIs delWireAtT
    isplitr
    · imodintro
      isplitr
      · ipureintro; exact Hnn
      iexists _, w, r, o
      iframe HR
      iright; iright
      iframe HW Hr
      ipureintro; exact ⟨rfl, rfl⟩
    · imodintro
      iintro %w' %d %esl HR' HW' HE'
      ihave %E1 := typedPointsto_agree_wand _ _ _ _ _ $$ HR HR'
      cases go.IntoValInj.intoVal_inj (V := Loc) ((interface_mkOk_inj _ _ _ _).1 E1).2
      ihave %E2 := typedPointsto_agree_wand _ _ _ _ _ $$ HW HW'
      subst E2
      iapply Hwand $$ HE'
  | .txn cs ts es, hok, Φ => by
    simp only [OpOk] at hok
    obtain ⟨hcs, hts, hes⟩ := hok
    iintro H
    simp only [reqOpTree]
    iapply (treeWp_wrapRequestTxn _ (fun r => txnQ r cs ts es)
      (fun Ψ => by
        iintro HΨ
        iapply (treeWp_ptr_fupd (V := etcdserverpb.TxnRequest))
        iapply (treeWp_txnStrct cs ts es _ _ hcs
          (fun Φ' => treeWp_sliceL (reqOpsTree ts) ts opR (reqOpsTree_length ts)
            (fun Ψ' => treeWpL_reqOps ts hts [] Ψ') Φ')
          (fun Φ' => treeWp_sliceL (reqOpsTree es) es opR (reqOpsTree_length es)
            (fun Ψ' => treeWpL_reqOps es hes [] Ψ') Φ'))
        iintro %x Hx
        iexists x
        isplitr
        · ipureintro; rfl
        iintro %q Hq
        imod Hx $$ Hq with HQ
        imodintro
        iapply HΨ $$ HQ))
    iintro %p %w %r %Hnn #HR #HW HQ
    unfold txnQ txn.txnFieldsIs
    icases HQ with ⟨%Hrn, ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #HC, #Hcsl, #Hcs, #HS, #Hssl, #Hss,
      #HF, #Hfsl, #Hfs⟩, #Hwand⟩
    iapply H
    unfold opR txn.requestOpIs delWireAtT
    isplitr
    · imodintro
      isplitr
      · ipureintro; exact Hnn
      iexists w, r
      iframe HR HW
      isplitr
      · ipureintro; exact Hrn
      iexists csl, ssl, fsl, cps, sps, fps
      iframe HC Hcsl Hcs HS Hssl Hss HF Hfsl Hfs
    · imodintro
      iintro %w' %r' %ssl' %fsl' %sps' %fps' HR' HW' HS' Hssl' HF' Hfsl'
      ihave %E1 := typedPointsto_agree_wand _ _ _ _ _ $$ HR HR'
      cases go.IntoValInj.intoVal_inj (V := Loc) ((interface_mkOk_inj _ _ _ _).1 E1).2
      ihave %E2 := typedPointsto_agree_wand _ _ _ _ _ $$ HW HW'
      subst E2
      iapply Hwand $$ HS' Hssl' HF' Hfsl'
  | .put k v l, hok, Φ => by
    simp only [OpOk, putKey] at hok
    simp only [reqOpTree]
    exact treeWp_reqOpPut (.put k v l) (by simpa [putOfOp, txn.putOpOf] using hok)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ _ h => by cases h) Φ
  | .putKeep k v, hok, Φ => by
    simp only [OpOk, putKey] at hok
    simp only [reqOpTree]
    exact treeWp_reqOpPut (.putKeep k v) (by simpa [putOfOp, txn.putOpOf] using hok)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ _ h => by cases h) Φ
  | .putIgnVal k l, hok, Φ => by
    simp only [OpOk, putKey] at hok
    simp only [reqOpTree]
    exact treeWp_reqOpPut (.putIgnVal k l)
      (by cases l <;> simpa [putOfOp, txn.putOpOf] using hok)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ _ h => by cases h) Φ

/-- **Operations, stored, in order.** -/
theorem treeWpL_reqOps : ∀ (ops : List TxnOp), OpsOk ops → ∀ (acc : List val) (Ψ : List val → IProp GF),
    (∀ xs : List Loc, ([∗list] a;x ∈ ops;xs, opR a x) -∗ Ψ (acc ++ xs.map fun x => #x)) ⊢
      treeWpL (reqOpsTree ops) acc Ψ
  | [], _, acc, Ψ => by
    simp only [reqOpsTree, treeWpL]
    iintro H
    ihave H := H $$ %([] : List Loc)
    simp only [List.map_nil, List.append_nil]
    iapply H
    iempintro
  | op :: ops, hok, acc, Ψ => by
    simp only [OpsOk] at hok
    simp only [reqOpsTree, treeWpL]
    iintro HΨ
    iapply (treeWp_reqOp op hok.1)
    iintro %x Hx
    isplitr
    · ipureintro; exact isPanic_intoVal x
    iapply (treeWpL_reqOps ops hok.2 (acc ++ [(#x)]) Ψ)
    iintro %xs Hxs
    ihave H := HΨ $$ %(x :: xs) [Hx Hxs]
    · iframe
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
    iexact H
end

end wps


/-! ## The instance -/

section inst
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`pbTxnRequest` with its store**, its `wireLen` set explicitly (`[v6a]` item 5). -/
def pbTxnRequestT : ProtoMsgT GF :=
  { pbTxnRequest with wireLen := txnWireLen, tree := txnReqTree }

/-- **Some transaction's request fits** (`[v6a]` item 5: the `wireLen` premise is satisfiable). -/
theorem pbTxnRequestT_wireLen_ok : ∃ m, (pbTxnRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨TxnModel.empty, by simp [pbTxnRequestT, txnWireLen, TxnModel.empty, grpcMsgMax]⟩

/-- A branch's store from the sender's operations. -/
theorem branchWp (ops : List TxnOp) (h : OpsOk ops) :
    BranchWp (GF := GF) ops
      (sliceTree (go.GoType.PointerType etcdserverpb.RequestOp.ty) (reqOpsTree ops)) :=
  fun Φ => treeWp_sliceL (reqOpsTree ops) ops opR (reqOpsTree_length ops)
    (fun Ψ => treeWpL_reqOps ops h [] Ψ) Φ

/-- **`pbTxnRequestT`'s request model is satisfiable.** -/
theorem pbTxnRequestT_reqSat : (pbTxnRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.TxnRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.TxnRequest etcdserverpb.TxnRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.TxnRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.TxnRequest etcdserverpb.TxnRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbTxnRequestT, pbTxnRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l (m : TxnModel)
  simp only [pbTxnRequestT, pbTxnRequest]
  iintro ⟨⟨%req, Hp, #Hat, %Hu⟩, %Hw, Hl⟩
  simp only [txnWireLen, grpcMsgMax] at Hw
  ihave Hat' := Hat
  unfold txnReqAt
  icases Hat' with ⟨%cps, %sps, %fps, -, -, -, #Hs, -, #Hf⟩
  ihave %H1 := reqOpsAt_ok sps m.thenOps $$ Hs
  ihave %H2 := reqOpsAt_ok fps m.elseOps $$ Hf
  have hts : OpsOk m.thenOps := H1 (by omega)
  have hes : OpsOk m.elseOps := H2 (by omega)
  have hcs : ∀ c ∈ m.cmps, c.key.length < 2 ^ 32 := fun c hc => by
    have := sum_lt_of_mem (List.mem_map_of_mem (f := cmpWireLen) hc)
    simp only [cmpWireLen] at this; omega
  have hd1 := delCountT_le m.thenOps
  have hd2 := delCountT_le m.elseOps
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.TxnRequest) (ty := etcdserverpb.TxnRequest.ty) l
    (zero_val etcdserverpb.TxnRequest))
  simp only [txnReqTree]
  iapply (treeWp_txnStrct m.cmps m.thenOps m.elseOps _ _ hcs (branchWp m.thenOps hts)
    (branchWp m.elseOps hes))
  iintro %x Hx
  iexists x
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  imod Hx $$ Hl with HQ
  unfold txnQ
  icases HQ with ⟨%Hnn, #HF, #Hwand⟩
  imodintro
  isplitl [Hp]
  · iexists req
    iframe Hp Hat
    ipureintro; exact Hu
  isplitr
  · unfold txn.txnRequestIs txnWireOk
    isplitr
    · isplitr
      · ipureintro; exact Hnn
      iexact HF
    isplitr
    · ipureintro; constructor <;> omega
    iexact Hwand
  · ipureintro; trivial

end inst

/-- **`TxnRequest`'s registration** (prototype-only axiom; the Scope's R, `[v5]`'s split
registries: a method's request). -/
axiom pbTxnRequestT_reg {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [HeapGS HasLC.hasLC GF] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions] :
    grpcReqModelOf GF etcdserverpb.TxnRequest.ty = some (pbTxnRequestT (GF := GF))

end EtcdGrove
end Perennial
