/-
**Per-type prototype: the KV service's messages at registered types** (stage A prototype; the
Scope's V for `ProtoMsg`): `PutRequest` (`ReqSat`; its `recv` holds the size cache's invariant,
allocated in the store's WP at mask `⊤`) and `RangeResponse` (`RepSat`; a repeated message field,
`Kvs`, through `treeWp_sliceTree`), with their registrations. Each instance is today's
`ProtoMsg` (`InvKVConn.lean`) with its normalizing store (`tree`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

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

/-- **The store of a put request**: its key and value (`nil` if empty, as protobuf-go decodes
them), its lease and flags. -/
def putReqTree (o : OpFull) : VTree :=
  .strct etcdserverpb.PutRequest.ty
    [(go!"Key", go.GoType.SliceType go.byte), (go!"Value", go.GoType.SliceType go.byte),
     (go!"Lease", go.int64), (go!"PrevKv", go.bool), (go!"IgnoreValue", go.bool),
     (go!"IgnoreLease", go.bool)]
    [bytesTree go.byte o.key, bytesTree go.byte o.val, .leaf #o.leaseID, .leaf #o.base.prevKV,
     .leaf #o.ignoreValue, .leaf #o.ignoreLease]

/-- **`pbPutRequest` with its store.** -/
def pbPutRequestT : ProtoMsgT GF :=
  { pbPutRequest with tree := putReqTree }

/-- **A put request fits a gRPC message** (rule 7's witness that `wireLen` is not the default). -/
theorem pbPutRequestT_wireLen_ok : ∃ m, (pbPutRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨putReqOp (zero_val _) [] [], by
    simp [pbPutRequestT, pbPutRequest, opWireLen, wireSlack, grpcMsgMax, putReqOp,
      txn.putOpOf, OpFull.newOp]⟩

/-- **`pbPutRequestT`'s request model is satisfiable.** -/
theorem pbPutRequestT_reqSat : (pbPutRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.PutRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.PutRequest etcdserverpb.PutRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.PutRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.PutRequest etcdserverpb.PutRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbPutRequestT, pbPutRequest]
    iintro ⟨%req, %k, %v, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbPutRequestT, pbPutRequest]
  iintro ⟨⟨%req, %k, %v, Hp, #Hk, #Hv, %Hm⟩, %Hw, Hl⟩
  obtain ⟨rfl, Hu⟩ := Hm
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.PutRequest) (ty := etcdserverpb.PutRequest.ty) l
    (zero_val etcdserverpb.PutRequest))
  simp only [putReqTree, treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hks Hks -
  isplitr
  · ipureintro; exact isPanic_intoVal ksl
  iapply treeWp_bytes
  iintro %vsl %Hvs Hvs -
  isplitr
  · ipureintro; exact isPanic_intoVal vsl
  simp only [isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  isplitl [Hp]
  · iexists req, k, v
    iframe Hp Hk Hv
    ipureintro; exact ⟨rfl, Hu⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HK, HV, HL, HP, HIV, HIL, -, HSC, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ ksl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ vsl).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ req.Lease').dfractional_persist _ $$ HL with #HL
  imod (typedPointsto_dfractional (GF := GF) _ req.PrevKv').dfractional_persist _ $$ HP with #HP
  imod (typedPointsto_dfractional (GF := GF) _ req.IgnoreValue').dfractional_persist _ $$ HIV with #HIV
  imod (typedPointsto_dfractional (GF := GF) _ req.IgnoreLease').dfractional_persist _ $$ HIL with #HIL
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hvs with #Hvs
  ihave Hinv : |={⊤}=> inv (nroot .@ "txn.putSizeCache")
      (∃ sc : w32, structFieldRef etcdserverpb.PutRequest go!"sizeCache" l ↦ sc) $$ [HSC]
  · iapply inv_alloc
    inext
    iexists _
    iexact HSC
  imod Hinv with #Hinv
  imodintro
  isplitl
  · unfold txn.putRequestIs
    isplitr
    · ipureintro; exact Hnn
    iexists ksl, vsl, (putReqOp req k v).key, (putReqOp req k v).val, req.Lease', req.PrevKv',
      req.IgnoreValue', req.IgnoreLease'
    iframe HK Hks HV Hvs HL HP HIV HIL Hinv
    ipureintro
    refine ⟨by simp [putReqOp, txn.putOpOf], ?_⟩
    have : (putReqOp req k v).key.length < 2 ^ 32 := by
      have := Hw; simp only [opWireLen, grpcMsgMax] at this; omega
    have hfin : sint.Z ksl.len < 2 ^ 63 - 1 := by
      obtain ⟨h1, h2⟩ := Hkl
      have e : sint.nat ksl.len = (sint.Z ksl.len).toNat := rfl
      rw [e] at h1
      generalize sint.Z ksl.len = n at h1 h2 ⊢
      omega
    exact hfin
  · ipureintro; trivial

/-- **The store of a response header** (always present: the sender's is not nil). -/
def hdrTree (h : HdrM) : VTree :=
  .ptr etcdserverpb.ResponseHeader.ty (.strct etcdserverpb.ResponseHeader.ty
    [(go!"ClusterId", go.uint64), (go!"MemberId", go.uint64), (go!"Revision", go.int64),
     (go!"RaftTerm", go.uint64), (go!"LeaderId", go.uint64)]
    [.leaf #h.clusterId, .leaf #h.memberId, .leaf #h.revision, .leaf #h.raftTerm, .leaf #h.leaderId])

/-- **The store of a key-value** (`nil` key and value if empty). -/
def kvTree (v : EtcdKv) : VTree :=
  .ptr mvccpb.KeyValue.ty (.strct mvccpb.KeyValue.ty
    [(go!"Key", go.GoType.SliceType go.byte), (go!"CreateRevision", go.int64),
     (go!"ModRevision", go.int64), (go!"Version", go.int64),
     (go!"Value", go.GoType.SliceType go.byte), (go!"Lease", go.int64)]
    [bytesTree go.byte v.key, .leaf #v.createRev, .leaf #v.modRev, .leaf #v.version,
     bytesTree go.byte v.value, .leaf #v.lease])

/-- **The store of a range response**: its header, its key-values (`nil` if none), `More`,
`Count`. -/
def rangeRespTree (m : RangeRespM) : VTree :=
  .strct etcdserverpb.RangeResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty),
     (go!"Kvs", go.GoType.SliceType (go.GoType.PointerType mvccpb.KeyValue.ty)),
     (go!"More", go.bool), (go!"Count", go.int64)]
    [hdrTree m.hdr, sliceTree (go.GoType.PointerType mvccpb.KeyValue.ty) (m.kvs.map kvTree),
     .leaf #m.more, .leaf #m.count]

/-- **`pbRangeResponse` with its store.** -/
def pbRangeResponseT : ProtoMsgT GF :=
  { pbRangeResponse with tree := rangeRespTree }

theorem treeWp_hdr (h : HdrM) (Φ : val → IProp GF) :
    (∀ p : Loc, hdrFull p h -∗ Φ #p) ⊢ treeWp (hdrTree h) Φ := by
  iintro H
  unfold hdrTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.ResponseHeader))
  simp only [treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HC, HM, HR, HT, HL, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h.clusterId).dfractional_persist _ $$ HC with #HC
  imod (typedPointsto_dfractional (GF := GF) _ h.memberId).dfractional_persist _ $$ HM with #HM
  imod (typedPointsto_dfractional (GF := GF) _ h.revision).dfractional_persist _ $$ HR with #HR
  imod (typedPointsto_dfractional (GF := GF) _ h.raftTerm).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ h.leaderId).dfractional_persist _ $$ HL with #HL
  imodintro
  iapply H
  unfold hdrFull
  iframe HC HM HR HT HL
  ipureintro; exact Hnn

theorem treeWp_kv (v : EtcdKv) (Φ : val → IProp GF) :
    (∀ p : Loc, txn.kvIs p v -∗ Φ #p) ⊢ treeWp (kvTree v) Φ := by
  iintro H
  unfold kvTree
  iapply (treeWp_ptr_fupd (V := mvccpb.KeyValue))
  simp only [treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hks Hks -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_bytes
  iintro %vsl %Hvs Hvs -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
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
  icases Hp with ⟨-, HK, HC, HM, HV, HVa, HL, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ ksl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ v.createRev).dfractional_persist _ $$ HC with #HC
  imod (typedPointsto_dfractional (GF := GF) _ v.modRev).dfractional_persist _ $$ HM with #HM
  imod (typedPointsto_dfractional (GF := GF) _ v.version).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ vsl).dfractional_persist _ $$ HVa with #HVa
  imod (typedPointsto_dfractional (GF := GF) _ v.lease).dfractional_persist _ $$ HL with #HL
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hvs with #Hvs
  imodintro
  iapply H
  unfold txn.kvIs
  iexists ksl, vsl
  iframe HK Hks HC HM HV HVa Hvs HL
  try (ipureintro; exact Hnn)

theorem kvsIs_of_sepL2 (kvs : List EtcdKv) (ps : List Loc) :
    ([∗list] v;p ∈ kvs;ps, txn.kvIs (GF := GF) p v) ⊢ txn.kvsIs ps kvs := by
  iintro #H
  ihave %Hl := BigSepL2.bigSepL2_length $$ H
  unfold txn.kvsIs
  isplitr
  · ipureintro; exact Hl.symm
  imodintro
  iintro %i %p %v %Hp %Hv
  iapply (BigSepL2.bigSepL2_lookup Hv Hp) $$ H

/-- **`pbRangeResponseT`'s reply model is satisfiable.** -/
theorem pbRangeResponseT_repSat : (pbRangeResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.RangeResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.RangeResponse etcdserverpb.RangeResponse.ty),
      fun l => .rfl⟩,
    ⟨etcdserverpb.RangeResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.RangeResponse etcdserverpb.RangeResponse.ty),
      fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbRangeResponseT, pbRangeResponse, rangeRespMsg]
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l m
  simp only [pbRangeResponseT, pbRangeResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.RangeResponse)
    (ty := etcdserverpb.RangeResponse.ty) l x0)
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
  simp only [isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; trivial
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HH, HK, HM, HC, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ sl).dfractional_persist _ $$ HK with #HK
  imod (typedPointsto_dfractional (GF := GF) _ m.more).dfractional_persist _ $$ HM with #HM
  imod (typedPointsto_dfractional (GF := GF) _ m.count).dfractional_persist _ $$ HC with #HC
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave #Hkvs := kvsIs_of_sepL2 m.kvs ps $$ Hkvs
  imodintro
  iframe Hs
  unfold rangeRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, sl, ps
  iframe HH Hh HK Hsl Hkvs HM HC

/-- **`PutRequest`'s registration** (the Scope's R, `[v5]`'s split registries: a method's request). -/
axiom pbPutRequestT_reg :
    grpcReqModelOf GF etcdserverpb.PutRequest.ty = some (pbPutRequestT (GF := GF))

/-- **`RangeResponse`'s registration** (a method's reply). -/
axiom pbRangeResponseT_reg :
    grpcRepModelOf GF etcdserverpb.RangeResponse.ty = some (pbRangeResponseT (GF := GF))

end defs

end EtcdGrove
end Perennial
