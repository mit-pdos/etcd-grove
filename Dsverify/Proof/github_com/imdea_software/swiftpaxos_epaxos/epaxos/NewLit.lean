/-
The `Replica` composite literal of `epaxos.New` (unkeyed, 41 fields), stepped in a declaration of
its own (stepping it inside `wp_New_of` made the kernel's check of that declaration recurse too
deeply).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem wp_Replica_lit (v0 : Loc) (v1 : GoChan) (v2 : GoChan) (v3 : GoChan) (v4 : GoChan) (v5 : GoChan) (v6 : GoChan) (v7 : GoChan) (v8 : GoChan) (v9 : GoChan) (v10 : GoChan) (v11 : w8) (v12 : w8) (v13 : w8) (v14 : w8) (v15 : w8) (v16 : w8) (v17 : w8) (v18 : w8) (v19 : w8) (v20 : GoSlice) (v21 : GoSlice) (v22 : GoSlice) (v23 : GoSlice) (v25 : GoSlice) (v25a : GoSlice) (v25b : GoSlice) (v26 : GoMap) (v27 : w32) (v28 : w32) (v29 : w32) (v30 : Loc) (v31 : GoChan) (v32 : Bool) (v33 : w32) (v34 : w64) (v35 : Bool) (v36 : Loc) (v40 : w64) :
    ⊢ ∀ Φ : val → IProp GF, ▷ Φ #(epaxos.Replica.mk v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 null v25 v25a v25b v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 chan.nil chan.nil slice.nil v40) -∗
      WP (App (Val (GoInstruction (CompositeLiteral epaxos.Replica.ty))) (LiteralValue [(KeyedElement none (ElementExpression (go.GoType.PointerType replica.Replica.ty) (Val #v0))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v1))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v2))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v3))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v4))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v5))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v6))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v7))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v8))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v9))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv rpc.Serializable.ty) (Val #v10))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v11))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v12))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v13))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v14))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v15))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v16))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v17))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v18))),
        (KeyedElement none (ElementExpression go.uint8 (Val #v19))),
        (KeyedElement none (ElementExpression (go.GoType.SliceType (go.GoType.SliceType (go.GoType.PointerType epaxos.Instance.ty))) (Val #v20))),
        (KeyedElement none (ElementExpression (go.GoType.SliceType go.int32) (Val #v21))),
        (KeyedElement none (ElementExpression (go.GoType.SliceType go.int32) (Val #v22))),
        (KeyedElement none (ElementExpression (go.GoType.SliceType go.int32) (Val #v23))),
        (KeyedElement none (ElementExpression go.untypedNil (Val UntypedNil))),
        (KeyedElement none (ElementExpression (go.GoType.SliceType (go.GoType.MapType state.Key.ty (go.GoType.PointerType epaxos.InstPair.ty))) (Val #v25))),
        (KeyedElement none (ElementExpression (go.GoType.SliceType go.int32) (Val #v25a))),
        (KeyedElement none (ElementExpression (go.GoType.SliceType go.int32) (Val #v25b))),
        (KeyedElement none (ElementExpression (go.GoType.MapType state.Key.ty go.int32) (Val #v26))),
        (KeyedElement none (ElementExpression go.int32 (Val #v27))),
        (KeyedElement none (ElementExpression go.int32 (Val #v28))),
        (KeyedElement none (ElementExpression go.int32 (Val #v29))),
        (KeyedElement none (ElementExpression (go.GoType.PointerType sync.Mutex.ty) (Val #v30))),
        (KeyedElement none (ElementExpression (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.PointerType epaxos.instanceId.ty)) (Val #v31))),
        (KeyedElement none (ElementExpression go.bool (Val #v32))),
        (KeyedElement none (ElementExpression go.int32 (Val #v33))),
        (KeyedElement none (ElementExpression go.int (Val #v34))),
        (KeyedElement none (ElementExpression go.bool (Val #v35))),
        (KeyedElement none (ElementExpression (go.GoType.PointerType sync.Mutex.ty) (Val #v36))),
        (KeyedElement none (ElementExpression go.untypedNil (Val UntypedNil))),
        (KeyedElement none (ElementExpression go.untypedNil (Val UntypedNil))),
        (KeyedElement none (ElementExpression go.untypedNil (Val UntypedNil))),
        (KeyedElement none (ElementExpression go.int (Val #v40)))])) {{ Φ }} := by
  iintro %Φ HΦ
  wp_pures
  simp only [epaxos.Replica.fieldsUnsealed, List.zip, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.foldl_cons, List.foldl_nil]
  wp_auto
  iexact HΦ

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
