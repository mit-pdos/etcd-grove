/-
**Per-type instances: the KV service's remaining messages** (stage A, CP3; the Scope's V for
`ProtoMsg`): each of today's `ProtoMsg`s of the KV service (`InvKVConn.lean`) not done in
`PerTypeKV.lean`/`PerTypeTxn.lean`, with its normalizing store (`tree`: what protobuf-go's decoder
leaves in a fresh message decoding the sender's bytes), its `Sat` and its registration:

- requests (`ReqSat`, `grpcReqModelOf`): `RangeRequest` (`getStrct`, its range end `nil` if
  empty), `DeleteRangeRequest` (`delStrct`), `CompactionRequest` (owned by the receiver);
- replies (`RepSat`, `grpcRepModelOf`): `PutResponse` (its `PrevKv` a fresh key-value or `nil`),
  `DeleteRangeResponse`, `CompactionResponse`, and `TxnResponse`, a mutual tree: its `Responses`
  are `ResponseOp`s whose oneof wraps a fresh `RangeResponse`, `PutResponse`,
  `DeleteRangeResponse` or (a nested transaction's) `TxnResponse`, recursively, each nested header
  holding only its revision (`OpRespM`'s model: the other header fields zero, so unset).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeKV
public import Proof.go_etcd_io.etcd.client.v3.PerTypeTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-! ## Compaction -/

/-- **The store of a compaction request**: its revision and `Physical` flag. -/
def compactReqTree (m : CompactReqM) : VTree :=
  .strct etcdserverpb.CompactionRequest.ty
    [(go!"Revision", go.int64), (go!"Physical", go.bool)]
    [.leaf #m.revision, .leaf #m.physical]

/-- **`pbCompactionRequest` with its store.** -/
def pbCompactionRequestT : ProtoMsgT GF :=
  { pbCompactionRequest with tree := compactReqTree }

theorem pbCompactionRequestT_wireLen_ok :
    ∃ m, (pbCompactionRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨⟨W64 0, false⟩, by simp [pbCompactionRequestT, pbCompactionRequest, grpcMsgMax]⟩

/-- **`pbCompactionRequestT`'s request model is satisfiable.** -/
theorem pbCompactionRequestT_reqSat : (pbCompactionRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.CompactionRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.CompactionRequest etcdserverpb.CompactionRequest.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.CompactionRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.CompactionRequest etcdserverpb.CompactionRequest.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbCompactionRequestT, pbCompactionRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbCompactionRequestT, pbCompactionRequest]
  iintro ⟨Hs, -, Hl⟩
  iapply (storeInto_wp_typed (V := etcdserverpb.CompactionRequest)
    (ty := etcdserverpb.CompactionRequest.ty) l (zero_val etcdserverpb.CompactionRequest))
  simp only [compactReqTree, treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  iframe Hs
  isplitr
  · ipureintro; trivial
  iexists _
  iframe Hl
  ipureintro; rfl

/-- **The store of a compaction response**: its header. -/
def compactRespTree (m : CompactRespM) : VTree :=
  .strct etcdserverpb.CompactionResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty)]
    [hdrTree m.hdr]

/-- **`pbCompactionResponse` with its store.** -/
def pbCompactionResponseT : ProtoMsgT GF :=
  { pbCompactionResponse with tree := compactRespTree }

/-- **`pbCompactionResponseT`'s reply model is satisfiable.** -/
theorem pbCompactionResponseT_repSat : (pbCompactionResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.CompactionResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.CompactionResponse etcdserverpb.CompactionResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.CompactionResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.CompactionResponse etcdserverpb.CompactionResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro (m : CompactRespM)
    simp only [pbCompactionResponseT, pbCompactionResponse, compactRespMsg]
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l m
  simp only [pbCompactionResponseT, pbCompactionResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.CompactionResponse)
    (ty := etcdserverpb.CompactionResponse.ty) l x0)
  simp only [compactRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  try simp only [isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HH, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imodintro
  iframe Hs
  unfold compactRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h
  iframe HH Hh

/-! ## Put and delete responses -/

/-- **The store of a previous key-value** (`nil` if none). -/
def prevKvTree : Option EtcdKv → VTree
  | none => .leaf #(null : Loc)
  | some v => kvTree v

theorem treeWp_prevKv (prev : Option EtcdKv) (Φ : val → IProp GF) :
    (∀ pk : Loc, (match prev with
      | none => iprop(⌜pk = null⌝)
      | some v => iprop(⌜pk ≠ null⌝ ∗ txn.kvIs (GF := GF) pk v)) -∗ Φ #pk) ⊢
      treeWp (prevKvTree prev) Φ := by
  cases prev with
  | none =>
    iintro H
    simp only [prevKvTree, treeWp]
    iapply H $$ %null
    ipureintro; rfl
  | some v =>
    iintro H
    simp only [prevKvTree]
    iapply treeWp_kv
    iintro %p #Hp
    iapply H $$ %p
    isplitr
    · unfold txn.kvIs
      icases Hp with ⟨%ksl, %vsl, -, -, -, -, -, -, -, -, %Hnn⟩
      ipureintro; exact Hnn
    iexact Hp

/-- **The store of a put response**: its header, its previous key-value (`nil` if none). -/
def putRespTree (m : PutRespM) : VTree :=
  .strct etcdserverpb.PutResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty),
     (go!"PrevKv", go.GoType.PointerType mvccpb.KeyValue.ty)]
    [hdrTree m.hdr, prevKvTree m.prev]

/-- **`pbPutResponse` with its store.** -/
def pbPutResponseT : ProtoMsgT GF :=
  { pbPutResponse with tree := putRespTree }

/-- **`pbPutResponseT`'s reply model is satisfiable.** -/
theorem pbPutResponseT_repSat : (pbPutResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.PutResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.PutResponse etcdserverpb.PutResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.PutResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.PutResponse etcdserverpb.PutResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro (m : PutRespM)
    simp only [pbPutResponseT, pbPutResponse, putRespMsg]
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l m
  simp only [pbPutResponseT, pbPutResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.PutResponse)
    (ty := etcdserverpb.PutResponse.ty) l x0)
  simp only [putRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  iapply treeWp_prevKv
  iintro %pk Hpk
  isplitr
  · ipureintro; exact isPanic_intoVal pk
  try simp only [isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HH, HP, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ pk).dfractional_persist _ $$ HP with #HP
  imodintro
  iframe Hs
  unfold putRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, pk
  iframe HH Hh HP Hpk

/-- **The store of a delete response**: its header, `Deleted`, its previous key-values (`nil` if
none). -/
def delRespTree (m : DelRespM) : VTree :=
  .strct etcdserverpb.DeleteRangeResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty),
     (go!"Deleted", go.int64),
     (go!"PrevKvs", go.GoType.SliceType (go.GoType.PointerType mvccpb.KeyValue.ty))]
    [hdrTree m.hdr, .leaf #m.deleted,
     sliceTree (go.GoType.PointerType mvccpb.KeyValue.ty) (m.prevs.map kvTree)]

/-- **`pbDeleteRangeResponse` with its store.** -/
def pbDeleteRangeResponseT : ProtoMsgT GF :=
  { pbDeleteRangeResponse with tree := delRespTree }

/-- **`pbDeleteRangeResponseT`'s reply model is satisfiable.** -/
theorem pbDeleteRangeResponseT_repSat : (pbDeleteRangeResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.DeleteRangeResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.DeleteRangeResponse etcdserverpb.DeleteRangeResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.DeleteRangeResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.DeleteRangeResponse etcdserverpb.DeleteRangeResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro (m : DelRespM)
    simp only [pbDeleteRangeResponseT, pbDeleteRangeResponse, delRespMsg]
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l m
  simp only [pbDeleteRangeResponseT, pbDeleteRangeResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.DeleteRangeResponse)
    (ty := etcdserverpb.DeleteRangeResponse.ty) l x0)
  simp only [delRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  isplitr
  · ipureintro; exact isPanic_intoVal _
  iapply (treeWp_sliceMap (V := Loc) kvTree (fun v p => txn.kvIs (GF := GF) p v)
    (fun a Φ => treeWp_kv a Φ))
  iintro %ps %sl %Hps Hkvs Hsl -
  isplitr
  · ipureintro; exact isPanic_intoVal sl
  try simp only [isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HH, HD, HP, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ m.deleted).dfractional_persist _ $$ HD with #HD
  imod (typedPointsto_dfractional (GF := GF) _ sl).dfractional_persist _ $$ HP with #HP
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave #Hkvs := kvsIs_of_sepL2 m.prevs ps $$ Hkvs
  imodintro
  iframe Hs
  unfold delRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, sl, ps
  iframe HH Hh HD HP Hsl Hkvs

/-! ## Range and delete requests -/

/-- **The store of a range request** (`PerTypeTxn`'s `getStrct`: its fields read back from the
get's `OpFull`, `Key` and `RangeEnd` `nil` if empty). -/
def rangeReqTree (o : OpFull) : VTree := getStrct o

/-- **`pbRangeRequest` with its store.** -/
def pbRangeRequestT : ProtoMsgT GF :=
  { pbRangeRequest with tree := rangeReqTree }

theorem pbRangeRequestT_wireLen_ok : ∃ m, (pbRangeRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨rangeReqOp (zero_val _) [] [], by
    simp [pbRangeRequestT, pbRangeRequest, opWireLen, wireSlack, grpcMsgMax, rangeReqOp,
      txn.rangeOpOf, OpFull.newOp]⟩

/-- **`pbRangeRequestT`'s request model is satisfiable.** -/
theorem pbRangeRequestT_reqSat : (pbRangeRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.RangeRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.RangeRequest etcdserverpb.RangeRequest.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.RangeRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.RangeRequest etcdserverpb.RangeRequest.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbRangeRequestT, pbRangeRequest]
    iintro ⟨%req, %k, %e, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l o
  simp only [pbRangeRequestT, pbRangeRequest]
  iintro ⟨⟨%req, %k, %e, Hp, #Hk, #He, %Hm⟩, %Hw, Hl⟩
  obtain ⟨Ho, Hu⟩ := Hm
  have hg : GetOk o := ⟨k, e, req.Revision', req.Limit', req.SortOrder', req.SortTarget',
    req.Serializable', req.KeysOnly', req.CountOnly', req.MinModRevision', req.MaxModRevision',
    req.MinCreateRevision', req.MaxCreateRevision', Ho⟩
  have hk : o.key.length < 2 ^ 32 := by
    simp only [opWireLen, grpcMsgMax] at Hw; omega
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.RangeRequest) (ty := etcdserverpb.RangeRequest.ty) l
    (zero_val etcdserverpb.RangeRequest))
  simp only [rangeReqTree, getStrct, treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hks Hks -
  isplitr
  · ipureintro; exact isPanic_intoVal ksl
  iapply treeWp_bytes
  iintro %esl %Hes Hes -
  isplitr
  · ipureintro; exact isPanic_intoVal esl
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  isplitl [Hp]
  · iexists req, k, e
    iframe Hp Hk He
    ipureintro; exact ⟨Ho, Hu⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HK, HE, HL, HR, HSO, HST, HS, HKO, HCO, H1, H2, H3, H4, -, -, -⟩
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
  imod bytes_freeze ksl o.key Hks.2 $$ Hks with ⟨#Hks, %Hk'⟩
  imod bytes_freeze esl o.base.rangeEnd Hes.2 $$ Hes with ⟨#Hes, %He'⟩
  imodintro
  isplitl
  · unfold txn.rangeRequestIs
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, esl, o.key, o.base.rangeEnd, o.base.rev, o.base.limit, _, _, o.base.serializable,
      o.keysOnly, o.base.countOnly, o.base.minModRev, o.base.maxModRev, o.base.minCreateRev,
      o.base.maxCreateRev
    iframe HK Hks HE Hes HL HR HSO HST HS HKO HCO H1 H2 H3 H4
    isplitr
    · ipureintro; rw [He'.1]; refine (getOk_eq hg).trans ?_; simp
    · ipureintro; exact len_bound ksl o.key hk Hk'.2.2.1
  · ipureintro; trivial

/-- **The store of a delete request** (`PerTypeTxn`'s `delStrct`). -/
def delReqTree (o : OpFull) : VTree := delStrct o

/-- **`pbDeleteRangeRequest` with its store.** -/
def pbDeleteRangeRequestT : ProtoMsgT GF :=
  { pbDeleteRangeRequest with tree := delReqTree }

theorem pbDeleteRangeRequestT_wireLen_ok :
    ∃ m, (pbDeleteRangeRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨txn.deleteOpOf [] [] false, by
    simp [pbDeleteRangeRequestT, pbDeleteRangeRequest, opWireLen, wireSlack, grpcMsgMax,
      txn.deleteOpOf, OpFull.newOp]⟩

/-- **`pbDeleteRangeRequestT`'s request model is satisfiable.** -/
theorem pbDeleteRangeRequestT_reqSat : (pbDeleteRangeRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.DeleteRangeRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.DeleteRangeRequest etcdserverpb.DeleteRangeRequest.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.DeleteRangeRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.DeleteRangeRequest etcdserverpb.DeleteRangeRequest.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbDeleteRangeRequestT, pbDeleteRangeRequest]
    iintro ⟨%req, %k, %e, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l o
  simp only [pbDeleteRangeRequestT, pbDeleteRangeRequest]
  iintro ⟨⟨%req, %k, %e, Hp, #Hk, #He, %Hm⟩, %Hw, Hl⟩
  obtain ⟨Ho, Hu⟩ := Hm
  have hd : DelOk o := ⟨k, e, req.PrevKv', Ho⟩
  have hk : o.key.length < 2 ^ 32 := by
    simp only [opWireLen, grpcMsgMax] at Hw; omega
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.DeleteRangeRequest)
    (ty := etcdserverpb.DeleteRangeRequest.ty) l (zero_val etcdserverpb.DeleteRangeRequest))
  simp only [delReqTree, delStrct, treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hks Hks -
  isplitr
  · ipureintro; exact isPanic_intoVal ksl
  iapply treeWp_bytes
  iintro %esl %Hes Hes -
  isplitr
  · ipureintro; exact isPanic_intoVal esl
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  isplitl [Hp]
  · iexists req, k, e
    iframe Hp Hk He
    ipureintro; exact ⟨Ho, Hu⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HK, HE, HP, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ ksl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ esl).dfractional_persist _ $$ HE with #HE
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HP with #HP
  imod bytes_freeze ksl o.key Hks.2 $$ Hks with ⟨#Hks, %Hk'⟩
  imod bytes_freeze esl o.base.rangeEnd Hes.2 $$ Hes with ⟨#Hes, %He'⟩
  imodintro
  isplitl
  · unfold txn.deleteRangeRequestIs
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, esl, o.key, o.base.rangeEnd, _
    iframe HK Hks HE Hes HP
    isplitr
    · ipureintro; rw [He'.1]; refine (delOk_eq hd).trans ?_; simp
    · ipureintro; exact len_bound ksl o.key hk Hk'.2.2.1
  · ipureintro; trivial

/-! ## Transaction responses -/

/-- **A nested response's header**: its revision only (`OpRespM`'s model; the other fields zero,
which the decoder leaves unset). -/
def revHdr (rev : w64) : HdrM :=
  { clusterId := W64 0, memberId := W64 0, revision := rev, raftTerm := W64 0, leaderId := W64 0 }

/-- **A `ResponseOp` whose oneof wraps (`wty`, its field `fname`) a fresh response.** -/
def respWrap (wty : go.GoType) (fname : GoString) (innerTy : go.GoType) (inner : VTree) : VTree :=
  .ptr etcdserverpb.ResponseOp.ty (.strct etcdserverpb.ResponseOp.ty
    [(go!"Response", go.GoType.PointerType wty)]
    [.ptr wty (.strct wty [(fname, go.GoType.PointerType innerTy)] [inner])])

/-- **A transaction response's fields**: its header, `Succeeded`, its responses' store `rsT`. -/
def txnRespStrct (hdr : HdrM) (ok : Bool) (rsT : VTree) : VTree :=
  .strct etcdserverpb.TxnResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty),
     (go!"Succeeded", go.bool),
     (go!"Responses", go.GoType.SliceType (go.GoType.PointerType etcdserverpb.ResponseOp.ty))]
    [hdrTree hdr, .leaf #ok, rsT]

mutual
/-- **The store of an operation's response** (a nested transaction's recursively). -/
def respOpTree : OpRespM → VTree
  | .range rev kvs more count => respWrap etcdserverpb.ResponseOp_ResponseRange.ty
      go!"ResponseRange" etcdserverpb.RangeResponse.ty
      (.ptr etcdserverpb.RangeResponse.ty (rangeRespTree ⟨revHdr rev, kvs, more, count⟩))
  | .put rev prev => respWrap etcdserverpb.ResponseOp_ResponsePut.ty
      go!"ResponsePut" etcdserverpb.PutResponse.ty
      (.ptr etcdserverpb.PutResponse.ty (putRespTree ⟨revHdr rev, prev⟩))
  | .delete rev n prevs => respWrap etcdserverpb.ResponseOp_ResponseDeleteRange.ty
      go!"ResponseDeleteRange" etcdserverpb.DeleteRangeResponse.ty
      (.ptr etcdserverpb.DeleteRangeResponse.ty (delRespTree ⟨revHdr rev, n, prevs⟩))
  | .txn rev ok resps => respWrap etcdserverpb.ResponseOp_ResponseTxn.ty
      go!"ResponseTxn" etcdserverpb.TxnResponse.ty
      (.ptr etcdserverpb.TxnResponse.ty (txnRespStrct (revHdr rev) ok
        (sliceTree (go.GoType.PointerType etcdserverpb.ResponseOp.ty) (respOpsTree resps))))
/-- The stores of responses, in order. -/
def respOpsTree : List OpRespM → List VTree
  | [] => []
  | m :: ms => respOpTree m :: respOpsTree ms
end

/-- **The store of a transaction response**: its header, `Succeeded`, its responses (`nil` if
none). -/
def txnRespTree (m : TxnRespM) : VTree :=
  txnRespStrct m.hdr m.succeeded
    (sliceTree (go.GoType.PointerType etcdserverpb.ResponseOp.ty) (respOpsTree m.resps))

/-- **`pbTxnResponse` with its store.** -/
def pbTxnResponseT : ProtoMsgT GF :=
  { pbTxnResponse with tree := txnRespTree }

theorem respOpsTree_length : ∀ ms : List OpRespM, (respOpsTree ms).length = ms.length
  | [] => rfl
  | _ :: ms => by simp only [respOpsTree, List.length_cons, respOpsTree_length ms]

/-! ### The inner responses, stored behind a pointer -/

theorem treeWp_rangeRespP (m : RangeRespM) (Φ : val → IProp GF) :
    (∀ r : Loc, rangeRespMsg r m -∗ Φ #r) ⊢
      treeWp (.ptr etcdserverpb.RangeResponse.ty (rangeRespTree m)) Φ := by
  iintro H
  iapply (treeWp_ptr_fupd (V := etcdserverpb.RangeResponse))
  simp only [rangeRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  iapply (treeWp_sliceMap (V := Loc) kvTree (fun v p => txn.kvIs (GF := GF) p v)
    (fun a Φ => treeWp_kv a Φ))
  iintro %ps %sl %Hps Hkvs Hsl -
  isplitr
  · ipureintro; exact isPanic_intoVal sl
  try simp only [isPanic_intoVal]
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
  icases Hp with ⟨-, HH, HK, HM, HC, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ sl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ m.more).dfractional_persist _ $$ HM with #HM
  imod (typedPointsto_dfractional (GF := GF) _ m.count).dfractional_persist _ $$ HC with #HC
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave #Hkvs := kvsIs_of_sepL2 m.kvs ps $$ Hkvs
  imodintro
  iapply H
  unfold rangeRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, sl, ps
  iframe HH Hh HK Hsl Hkvs HM HC

theorem treeWp_putRespP (m : PutRespM) (Φ : val → IProp GF) :
    (∀ r : Loc, putRespMsg r m -∗ Φ #r) ⊢
      treeWp (.ptr etcdserverpb.PutResponse.ty (putRespTree m)) Φ := by
  iintro H
  iapply (treeWp_ptr_fupd (V := etcdserverpb.PutResponse))
  simp only [putRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  iapply treeWp_prevKv
  iintro %pk Hpk
  isplitr
  · ipureintro; exact isPanic_intoVal pk
  try simp only [isPanic_intoVal]
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
  icases Hp with ⟨-, HH, HP, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ pk).dfractional_persist _ $$ HP with #HP
  imodintro
  iapply H
  unfold putRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, pk
  iframe HH Hh HP Hpk

theorem treeWp_delRespP (m : DelRespM) (Φ : val → IProp GF) :
    (∀ r : Loc, delRespMsg r m -∗ Φ #r) ⊢
      treeWp (.ptr etcdserverpb.DeleteRangeResponse.ty (delRespTree m)) Φ := by
  iintro H
  iapply (treeWp_ptr_fupd (V := etcdserverpb.DeleteRangeResponse))
  simp only [delRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  isplitr
  · ipureintro; exact isPanic_intoVal _
  iapply (treeWp_sliceMap (V := Loc) kvTree (fun v p => txn.kvIs (GF := GF) p v)
    (fun a Φ => treeWp_kv a Φ))
  iintro %ps %sl %Hps Hkvs Hsl -
  isplitr
  · ipureintro; exact isPanic_intoVal sl
  try simp only [isPanic_intoVal]
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
  icases Hp with ⟨-, HH, HD, HP, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ m.deleted).dfractional_persist _ $$ HD with #HD
  imod (typedPointsto_dfractional (GF := GF) _ sl).dfractional_persist _ $$ HP with #HP
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave #Hkvs := kvsIs_of_sepL2 m.prevs ps $$ Hkvs
  imodintro
  iapply H
  unfold delRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, sl, ps
  iframe HH Hh HD HP Hsl Hkvs

/-! ### A nested header holds its revision -/

theorem hdrFull_rev (h : Loc) (rev : w64) :
    hdrFull (GF := GF) h (revHdr rev) ⊢
      ⌜h ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev := by
  simp only [hdrFull, revHdr]
  iintro ⟨%Hn, -, -, #HR, -, -⟩
  iframe HR
  ipureintro; exact Hn

theorem rangeRespMsg_rev (r : Loc) (rev : w64) (kvs : List EtcdKv) (more : Bool) (count : w64) :
    rangeRespMsg (GF := GF) r ⟨revHdr rev, kvs, more, count⟩ ⊢
      txn.rangeResponseIs r rev kvs more count := by
  simp only [rangeRespMsg, txn.rangeResponseIs]
  iintro ⟨%Hn, %h, %sl, %ps, #HH, #Hh, #HK, #Hsl, #Hkvs, #HM, #HC⟩
  icases hdrFull_rev h rev $$ Hh with ⟨%Hhn, #HR⟩
  isplitr
  · ipureintro; exact Hn
  iexists h, sl, ps
  iframe HH HR HK Hsl Hkvs HM HC
  ipureintro; exact Hhn

theorem putRespMsg_rev (r : Loc) (rev : w64) (prev : Option EtcdKv) :
    putRespMsg (GF := GF) r ⟨revHdr rev, prev⟩ ⊢ txn.putResponseIs r rev prev := by
  simp only [putRespMsg, txn.putResponseIs]
  iintro ⟨%Hn, %h, %pk, #HH, #Hh, #HP, Hpk⟩
  icases hdrFull_rev h rev $$ Hh with ⟨%Hhn, #HR⟩
  isplitr
  · ipureintro; exact Hn
  iexists h, pk
  iframe HH HR HP Hpk
  ipureintro; exact Hhn

theorem delRespMsg_rev (r : Loc) (rev n : w64) (prevs : List EtcdKv) :
    delRespMsg (GF := GF) r ⟨revHdr rev, n, prevs⟩ ⊢
      ⌜r ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" r ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
      structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" r ↦□ n ∗
      structFieldRef etcdserverpb.DeleteRangeResponse go!"PrevKvs" r ↦□ sl ∗ sl ↦*□ ps ∗
      txn.kvsIs ps prevs := by
  simp only [delRespMsg]
  iintro ⟨%Hn, %h, %sl, %ps, #HH, #Hh, #HD, #HP, #Hsl, #Hkvs⟩
  icases hdrFull_rev h rev $$ Hh with ⟨%Hhn, #HR⟩
  isplitr
  · ipureintro; exact Hn
  iexists h, sl, ps
  iframe HH HR HD HP Hsl Hkvs
  ipureintro; exact Hhn

theorem txnRespMsg_rev (r : Loc) (rev : w64) (ok : Bool) (resps : List OpRespM) :
    txnRespMsg (GF := GF) r ⟨revHdr rev, ok, resps⟩ ⊢
      ⌜r ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.TxnResponse go!"Header" r ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" r ↦□ ok ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" r ↦□ sl ∗ sl ↦*□ ps ∗
      opRespsMsg ps resps := by
  simp only [txnRespMsg]
  iintro ⟨%Hn, %h, %sl, %ps, #HH, #Hh, #HS, #HR, #Hsl, #Hrs⟩
  icases hdrFull_rev h rev $$ Hh with ⟨%Hhn, #Hrev⟩
  isplitr
  · ipureintro; exact Hn
  iexists h, sl, ps
  iframe HH Hrev HS HR Hsl Hrs
  ipureintro; exact Hhn

/-! ### The responses' wrappers -/

/-- **A `ResponseOp` wrapping a fresh `ResponseRange`** (its response's store `inner`, giving
`Q`). -/
theorem treeWp_wrapResponseRange (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (respWrap etcdserverpb.ResponseOp_ResponseRange.ty go!"ResponseRange" etcdserverpb.RangeResponse.ty inner) Φ := by
  iintro H
  unfold respWrap
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp_ResponseRange))
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

/-- **A `ResponseOp` wrapping a fresh `ResponsePut`** (its response's store `inner`, giving
`Q`). -/
theorem treeWp_wrapResponsePut (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (respWrap etcdserverpb.ResponseOp_ResponsePut.ty go!"ResponsePut" etcdserverpb.PutResponse.ty inner) Φ := by
  iintro H
  unfold respWrap
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp_ResponsePut))
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

/-- **A `ResponseOp` wrapping a fresh `ResponseDeleteRange`** (its response's store `inner`, giving
`Q`). -/
theorem treeWp_wrapResponseDeleteRange (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (respWrap etcdserverpb.ResponseOp_ResponseDeleteRange.ty go!"ResponseDeleteRange" etcdserverpb.DeleteRangeResponse.ty inner) Φ := by
  iintro H
  unfold respWrap
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp_ResponseDeleteRange))
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

/-- **A `ResponseOp` wrapping a fresh `ResponseTxn`** (its response's store `inner`, giving
`Q`). -/
theorem treeWp_wrapResponseTxn (inner : VTree) (Q : Loc → IProp GF)
    (hin : ∀ Ψ : val → IProp GF, (∀ r : Loc, Q r -∗ Ψ #r) ⊢ treeWp inner Ψ) (Φ : val → IProp GF) :
    (∀ (p : Loc) (w : Loc) (r : Loc), ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w : GoInterface) -∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ r -∗ Q r -∗ Φ #p) ⊢
      treeWp (respWrap etcdserverpb.ResponseOp_ResponseTxn.ty go!"ResponseTxn" etcdserverpb.TxnResponse.ty inner) Φ := by
  iintro H
  unfold respWrap
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp))
  simp only [treeWp.eq_4, treeWpL.eq_2, treeWpL.eq_1]
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseOp_ResponseTxn))
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

/-! ### A transaction response's fields, and its responses -/

theorem opRespsMsg_of_sepL2 : ∀ (ms : List OpRespM) (ps : List Loc),
    ([∗list] m;p ∈ ms;ps, opRespMsg (GF := GF) p m) ⊢ opRespsMsg ps ms
  | [], [] => by
    iintro -; unfold opRespsMsg; iempintro
  | [], _ :: _ => by
    iintro H; ihave %Hl := BigSepL2.bigSepL2_length $$ H; simp at Hl
  | _ :: _, [] => by
    iintro H; ihave %Hl := BigSepL2.bigSepL2_length $$ H; simp at Hl
  | m :: ms, p :: ps => by
    iintro ⟨H1, Hs⟩
    ihave H2 := opRespsMsg_of_sepL2 ms ps $$ Hs
    simp only [opRespsMsg]
    iframe H1 H2

/-- A responses' slice store: its responses' slice, each response's `opRespMsg`. -/
def RespsWp (rs : List OpRespM) (bt : VTree) : Prop :=
  ∀ Φ : val → IProp GF,
    (∀ (xs : List Loc) (sl : GoSlice), ⌜xs.length < 2 ^ 63 ∧ (xs = [] → sl = slice.nil)⌝ -∗
      ([∗list] a;x ∈ rs;xs, opRespMsg x a) -∗ sl ↦* xs -∗ ownSliceCap Loc sl (DFrac.own 1) -∗ Φ #sl) ⊢
      treeWp bt Φ

/-- **A transaction response's fields, stored.** -/
theorem treeWp_txnRespStrct (hdr : HdrM) (ok : Bool) (rs : List OpRespM) (rsT : VTree)
    (hR : RespsWp (GF := GF) rs rsT) (Φ : val → IProp GF) :
    (∀ x : etcdserverpb.TxnResponse, (∀ p : Loc, p ↦ x ={⊤}=∗ txnRespMsg p ⟨hdr, ok, rs⟩) -∗ Φ #x) ⊢
      treeWp (txnRespStrct hdr ok rsT) Φ := by
  iintro H
  simp only [txnRespStrct, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  isplitr
  · ipureintro; exact isPanic_intoVal _
  iapply (hR _)
  iintro %xs %sl %Hs Hrs Hsl -
  isplitr
  · ipureintro; exact isPanic_intoVal sl
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iapply H
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HH, HS, HR, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ ok).dfractional_persist _ $$ HS with #HS
  imod (typedPointsto_dfractional (GF := GF) _ sl).dfractional_persist _ $$ HR with #HR
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave #Hrs := opRespsMsg_of_sepL2 rs xs $$ Hrs
  imodintro
  unfold txnRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, sl, xs
  iframe HH Hh HS HR Hsl Hrs

mutual
/-- **An operation's response, stored**, a nested transaction's recursively. -/
theorem treeWp_respOp : ∀ (m : OpRespM) (Φ : val → IProp GF),
    (∀ p : Loc, opRespMsg p m -∗ Φ #p) ⊢ treeWp (respOpTree m) Φ
  | .range rev kvs more count, Φ => by
    iintro H
    simp only [respOpTree]
    iapply (treeWp_wrapResponseRange _ (fun r => rangeRespMsg r ⟨revHdr rev, kvs, more, count⟩)
      (fun Ψ => treeWp_rangeRespP _ Ψ))
    iintro %p %w %r %Hnn #HR #HW #Hr
    iapply H
    simp only [opRespMsg]
    isplitr
    · ipureintro; exact Hnn
    iexists w, r
    iframe HR HW
    iapply rangeRespMsg_rev $$ Hr
  | .put rev prev, Φ => by
    iintro H
    simp only [respOpTree]
    iapply (treeWp_wrapResponsePut _ (fun r => putRespMsg r ⟨revHdr rev, prev⟩)
      (fun Ψ => treeWp_putRespP _ Ψ))
    iintro %p %w %r %Hnn #HR #HW #Hr
    iapply H
    simp only [opRespMsg]
    isplitr
    · ipureintro; exact Hnn
    iexists w, r
    iframe HR HW
    iapply putRespMsg_rev $$ Hr
  | .delete rev n prevs, Φ => by
    iintro H
    simp only [respOpTree]
    iapply (treeWp_wrapResponseDeleteRange _ (fun r => delRespMsg r ⟨revHdr rev, n, prevs⟩)
      (fun Ψ => treeWp_delRespP _ Ψ))
    iintro %p %w %r %Hnn #HR #HW Hr
    iapply H
    simp only [opRespMsg]
    icases delRespMsg_rev r rev n prevs $$ Hr with ⟨%Hrn, %h, %sl, %ps, #HH, %Hhn, #Hrev, #HD, #HP, #Hsl, #Hkvs⟩
    isplitr
    · ipureintro; exact Hnn
    iexists w, r
    iframe HR HW
    isplitr
    · ipureintro; exact Hrn
    iexists h, sl, ps
    iframe HH Hrev HD HP Hsl Hkvs
    ipureintro; exact Hhn
  | .txn rev ok resps, Φ => by
    iintro H
    simp only [respOpTree]
    iapply (treeWp_wrapResponseTxn _ (fun r => txnRespMsg r ⟨revHdr rev, ok, resps⟩)
      (fun Ψ => by
        iintro HΨ
        iapply (treeWp_ptr_fupd (V := etcdserverpb.TxnResponse))
        iapply (treeWp_txnRespStrct (revHdr rev) ok resps _
          (fun Φ' => treeWp_sliceL (respOpsTree resps) resps (fun a x => opRespMsg x a)
            (respOpsTree_length resps) (fun Ψ' => treeWpL_respOps resps [] Ψ') Φ'))
        iintro %x Hx
        iexists x
        isplitr
        · ipureintro; rfl
        iintro %q Hq
        imod Hx $$ Hq with HQ
        imodintro
        iapply HΨ $$ HQ))
    iintro %p %w %r %Hnn #HR #HW Hr
    iapply H
    simp only [opRespMsg]
    icases txnRespMsg_rev r rev ok resps $$ Hr with ⟨%Hrn, %h, %sl, %ps, #HH, %Hhn, #Hrev, #HS, #HRs, #Hsl, #Hrs⟩
    isplitr
    · ipureintro; exact Hnn
    iexists w, r, h, sl, ps
    iframe HR HW HH Hrev HS HRs Hsl Hrs
    isplitr
    · ipureintro; exact Hrn
    ipureintro; exact Hhn

/-- **Responses, stored, in order.** -/
theorem treeWpL_respOps : ∀ (ms : List OpRespM) (acc : List val) (Ψ : List val → IProp GF),
    (∀ xs : List Loc, ([∗list] a;x ∈ ms;xs, opRespMsg x a) -∗ Ψ (acc ++ xs.map fun x => #x)) ⊢
      treeWpL (respOpsTree ms) acc Ψ
  | [], acc, Ψ => by
    simp only [respOpsTree, treeWpL]
    iintro H
    ihave H := H $$ %([] : List Loc)
    simp only [List.map_nil, List.append_nil]
    iapply H
    iempintro
  | m :: ms, acc, Ψ => by
    simp only [respOpsTree, treeWpL]
    iintro HΨ
    iapply (treeWp_respOp m)
    iintro %x Hx
    isplitr
    · ipureintro; exact isPanic_intoVal x
    iapply (treeWpL_respOps ms (acc ++ [(#x)]) Ψ)
    iintro %xs Hxs
    ihave H := HΨ $$ %(x :: xs) [Hx Hxs]
    · iframe
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
    iexact H
end

/-- **`pbTxnResponseT`'s reply model is satisfiable.** -/
theorem pbTxnResponseT_repSat : (pbTxnResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.TxnResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.TxnResponse etcdserverpb.TxnResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.TxnResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.TxnResponse etcdserverpb.TxnResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro (m : TxnRespM)
    simp only [pbTxnResponseT, pbTxnResponse, txnRespMsg]
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l (m : TxnRespM)
  simp only [pbTxnResponseT, pbTxnResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.TxnResponse)
    (ty := etcdserverpb.TxnResponse.ty) l x0)
  simp only [txnRespTree]
  iapply (treeWp_txnRespStrct m.hdr m.succeeded m.resps _
    (fun Φ' => treeWp_sliceL (respOpsTree m.resps) m.resps (fun a x => opRespMsg x a)
      (respOpsTree_length m.resps) (fun Ψ' => treeWpL_respOps m.resps [] Ψ') Φ'))
  iintro %x Hx
  iexists x
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  imod Hx $$ Hl with HQ
  imodintro
  iframe Hs
  iexact HQ

/-! ## Registrations -/

/-- **`RangeRequest`'s registration** (stage A: the one model of the Go type `RangeRequest` as a
method's request). -/
axiom pbRangeRequestT_reg :
    grpcReqModelOf GF etcdserverpb.RangeRequest.ty = some (pbRangeRequestT (GF := GF))

/-- **`DeleteRangeRequest`'s registration** (stage A: the one model of the Go type
`DeleteRangeRequest` as a method's request). -/
axiom pbDeleteRangeRequestT_reg :
    grpcReqModelOf GF etcdserverpb.DeleteRangeRequest.ty = some (pbDeleteRangeRequestT (GF := GF))

/-- **`CompactionRequest`'s registration** (stage A: the one model of the Go type
`CompactionRequest` as a method's request). -/
axiom pbCompactionRequestT_reg :
    grpcReqModelOf GF etcdserverpb.CompactionRequest.ty = some (pbCompactionRequestT (GF := GF))

/-- **`PutResponse`'s registration** (stage A: the one model of the Go type `PutResponse` as a
method's reply). -/
axiom pbPutResponseT_reg :
    grpcRepModelOf GF etcdserverpb.PutResponse.ty = some (pbPutResponseT (GF := GF))

/-- **`DeleteRangeResponse`'s registration** (stage A: the one model of the Go type
`DeleteRangeResponse` as a method's reply). -/
axiom pbDeleteRangeResponseT_reg :
    grpcRepModelOf GF etcdserverpb.DeleteRangeResponse.ty = some (pbDeleteRangeResponseT (GF := GF))

/-- **`TxnResponse`'s registration** (stage A: the one model of the Go type `TxnResponse` as a
method's reply). -/
axiom pbTxnResponseT_reg :
    grpcRepModelOf GF etcdserverpb.TxnResponse.ty = some (pbTxnResponseT (GF := GF))

/-- **`CompactionResponse`'s registration** (stage A: the one model of the Go type
`CompactionResponse` as a method's reply). -/
axiom pbCompactionResponseT_reg :
    grpcRepModelOf GF etcdserverpb.CompactionResponse.ty = some (pbCompactionResponseT (GF := GF))

end defs


end EtcdGrove
end Perennial
