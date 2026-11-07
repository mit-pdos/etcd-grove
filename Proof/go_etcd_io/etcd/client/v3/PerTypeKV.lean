/-
**Per-type prototype: the KV service's messages at registered types** (stage A prototype; the
Scope's V for `ProtoMsg`): `PutRequest` (`ReqSat`; its `recv` holds the size cache's invariant,
allocated in the store's WP at mask `⊤`) and `RangeResponse` (`RepSat`; a repeated message field,
`Kvs`, through `treeWp_sliceTree`), with their registrations. Each instance is today's
`ProtoMsg` (`InvKVConn.lean`) with its normalizing store (`tree`).
-/
module

public import Proof.google_golang_org.grpc.PerType
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

end defs

end EtcdGrove
end Perennial
