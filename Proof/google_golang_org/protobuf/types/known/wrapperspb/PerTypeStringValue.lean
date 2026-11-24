/-
**Per-type instances: protobuf's `wrapperspb.StringValue`** (gRPC's robustness driver,
`examples/lib/grpcdriver`, whose service carries `StringValue` as every method's request and reply,
unary and streaming, through grpc's default proto codec): its unary model `pbStringValueT`
(`ReqSat`, `wireLen_ok`, `RepSat`) and its stream model `pbStringValueST` (`ReqSat`, `RepSat`), with
their registrations in grpc's four role-split registries, in the shape of etcd's (`pb*T_reg`,
`client/v3/PerType*.lean`, `etcdserverpb/PerTypeLeaseKeepAlive.lean`).

The model of a `StringValue` is its `Value`. A sender's message holds it with no unknown fields
(translated code never sets them; `String`'s literal leaves them `nil`), so its encoding is
`Value`'s tag, length and bytes (`stringValueWireLen`). A decoded message holds the `Value` sent, and
no unknown fields: the store writes a fresh literal over the whole message, as protobuf-go's
`Unmarshal` resets it first. The unary reply's model is the request's (the same Go type, `recvOwn`
the default `True`); the stream model's received message is owned, and is a sender's message again
(a handler may send back what it received, as the driver's `Bidi` does).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import GeneratedProof.google_golang_org.protobuf.types.known.wrapperspb

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf.types.known

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- **A bound on the encoding of a `StringValue` holding `s`** with no unknown fields (protobuf-go's
`Size`): `Value`'s tag (1 byte), its length (a varint, at most 10 bytes) and its bytes; nothing for
an empty `Value` (proto3: a field at its zero value is not encoded). -/
def stringValueWireLen (s : GoString) : Nat := s.length + 11

/-- **The store of a `StringValue`**: its `Value` (the literal leaves the other fields zero). -/
def stringValueTree (s : GoString) : VTree :=
  .strct wrapperspb.StringValue.ty [(go!"Value", go.string)] [.leaf #s]

/-- **A sender's `*wrapperspb.StringValue`** holding `s`: its `Value`, and no unknown fields. -/
def stringValueSend (l : Loc) (s : GoString) : IProp GF :=
  iprop(∃ v : wrapperspb.StringValue, l ↦ v ∗ ⌜v.Value' = s ∧ v.unknownFields' = slice.nil⌝)

/-- **A `*wrapperspb.StringValue` on the wire of a unary method** (a trusted wire model): its
`Value`; received, not `null` (the generated handler decodes into its own `new(Msg)`), its `Value`
read-only. -/
def pbStringValue : ProtoMsg GF where
  ty := wrapperspb.StringValue.ty
  M := GoString
  tree := stringValueTree
  send := stringValueSend
  wireLen := stringValueWireLen
  recv r s := iprop(⌜r ≠ null⌝ ∗ structFieldRef wrapperspb.StringValue go!"Value" r ↦□ s)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val wrapperspb.StringValue))
  own l := iprop(∃ v : wrapperspb.StringValue, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **`pbStringValue` with its store.** -/
def pbStringValueT : ProtoMsgT GF :=
  { pbStringValue with }

/-- **`pbStringValueT`'s request model is satisfiable.** -/
theorem pbStringValueT_reqSat : (pbStringValueT (GF := GF)).ReqSat := by
  refine ⟨⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbStringValueT, pbStringValue, stringValueSend]
    iintro ⟨%v, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  change GoString at m
  simp only [pbStringValueT, pbStringValue]
  iintro ⟨Hs, %Hw, Hl⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := wrapperspb.StringValue)
    (ty := wrapperspb.StringValue.ty) l (zero_val wrapperspb.StringValue))
  simp only [stringValueTree, treeWp, treeWpL]
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
  icases Hl with ⟨-, HN, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m).dfractional_persist _ $$ HN with #HN
  imodintro
  iframe Hs
  isplitr
  · isplitr
    · ipureintro; exact Hnn
    iframe HN
  · ipureintro; trivial

theorem pbStringValueT_wireLen_ok :
    ∃ m, (pbStringValueT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨[], by simp [pbStringValueT, pbStringValue, stringValueWireLen, grpcMsgMax]⟩

/-- **`pbStringValueT`'s reply model is satisfiable.** -/
theorem pbStringValueT_repSat : (pbStringValueT (GF := GF)).RepSat := by
  apply ProtoMsgT.repSat_of_recvOwn_true _ (fun _ _ => rfl)
  refine ⟨⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbStringValueT, pbStringValue, stringValueSend]
    iintro ⟨%v, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  change GoString at m
  simp only [pbStringValueT, pbStringValue]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := wrapperspb.StringValue)
    (ty := wrapperspb.StringValue.ty) l x0)
  simp only [stringValueTree, treeWp, treeWpL]
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
  icases Hl with ⟨-, HN, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ m).dfractional_persist _ $$ HN with #HN
  imodintro
  iframe Hs
  isplitr
  · ipureintro; exact Hnn
  iframe HN

/-- **A `*wrapperspb.StringValue` on a stream** (a trusted wire model): its `Value`, sent with no
unknown fields; received, the whole message owned, again with no unknown fields (a sender's
message: `recv` is `send`). -/
abbrev pbStringValueS : StreamMsg GF where
  ty := wrapperspb.StringValue.ty
  M := GoString
  cnt := inferInstance
  send := stringValueSend
  wireLen := stringValueWireLen
  recv := stringValueSend
  own l := iprop(∃ v : wrapperspb.StringValue, l ↦ v)

/-- **`pbStringValueS` with its store.** -/
def pbStringValueST : StreamMsgT GF :=
  { pbStringValueS with tree := stringValueTree }

/-- **`pbStringValueST`'s store gives its decoded model** (with or without the request's bound). -/
theorem pbStringValueST_store (ls l : Loc) (m : GoString) :
    stringValueSend (GF := GF) ls m ∗ (∃ v : wrapperspb.StringValue, l ↦ v) ⊢
      WP (storeInto wrapperspb.StringValue.ty l (stringValueTree m))
        {{ _v, stringValueSend ls m ∗ stringValueSend l m }} := by
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := wrapperspb.StringValue)
    (ty := wrapperspb.StringValue.ty) l x0)
  simp only [stringValueTree, treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  imodintro
  iframe Hs
  unfold stringValueSend
  iexists _
  iframe Hl
  ipureintro; exact ⟨rfl, rfl⟩

/-- **`pbStringValueST`'s request model is satisfiable.** -/
theorem pbStringValueST_reqSat : (pbStringValueST (GF := GF)).ReqSat := by
  refine ⟨⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbStringValueST, pbStringValueS, stringValueSend]
    iintro ⟨%v, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  change GoString at m
  refine .trans ?_ (pbStringValueST_store ls l m)
  change stringValueSend ls m ∗ ⌜_⌝ ∗ (∃ v : wrapperspb.StringValue, l ↦ v) ⊢ _
  iintro ⟨Hs, -, Hl⟩
  iframe

/-- **`pbStringValueST`'s reply model is satisfiable.** -/
theorem pbStringValueST_repSat : (pbStringValueST (GF := GF)).RepSat := by
  refine ⟨⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbStringValueST, pbStringValueS, stringValueSend]
    iintro ⟨%v, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  exact pbStringValueST_store ls l m

/-! ## The registration

Interim, retired by #37's S3 (its per-type `PbCodecOk`, from which S4 derives grpc's registries). One
Go type, registered in each of grpc's four role-split registries it plays a role in. -/

/-- **`StringValue`'s registration as a unary method's request** (the one model of the Go type
`wrapperspb.StringValue` as a method's request). Interim, retired by #37's S3. -/
axiom pbStringValueT_reqReg :
    grpcReqModelOf GF wrapperspb.StringValue.ty = some (pbStringValueT (GF := GF))

/-- **`StringValue`'s registration as a unary method's reply** (the one model of the Go type
`wrapperspb.StringValue` as a method's reply). Interim, retired by #37's S3. -/
axiom pbStringValueT_repReg :
    grpcRepModelOf GF wrapperspb.StringValue.ty = some (pbStringValueT (GF := GF))

/-- **`StringValue`'s registration as a stream's request** (the one model of the Go type
`wrapperspb.StringValue` as a stream's request). Interim, retired by #37's S3. -/
axiom pbStringValueST_reqReg :
    streamReqModelOf GF wrapperspb.StringValue.ty = some (pbStringValueST (GF := GF))

/-- **`StringValue`'s registration as a stream's reply** (the one model of the Go type
`wrapperspb.StringValue` as a stream's reply). Interim, retired by #37's S3. -/
axiom pbStringValueST_repReg :
    streamRepModelOf GF wrapperspb.StringValue.ty = some (pbStringValueST (GF := GF))

end defs

end EtcdGrove
end Perennial
