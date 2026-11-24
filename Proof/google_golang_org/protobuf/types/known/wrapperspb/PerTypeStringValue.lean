/-
**Per-type instances: protobuf's `wrapperspb.StringValue`** (gRPC's robustness driver,
`examples/lib/grpcdriver`, whose service carries `StringValue` as every method's request and reply,
unary and streaming, through grpc's default proto codec): its unary request model `pbStringValueT`
(`ReqSat`, `wireLen_ok`), its unary reply model `pbStringValueRT` (`RepSat`) and its stream model
`pbStringValueST` (`ReqSat`, `RepSat`), with
their registrations in grpc's four role-split registries, in the shape of etcd's (`pb*T_reg`,
`client/v3/PerType*.lean`, `etcdserverpb/PerTypeLeaseKeepAlive.lean`).

The model of a `StringValue` is its `Value`. A sender's message holds it with no unknown fields
(translated code never sets them; `String`'s literal leaves them `nil`) and a `Value` below
`stringValueMax`, so its encoding is `Value`'s tag, length and bytes (`stringValueWireLen`), below
grpc's reply bound. A decoded message holds the `Value` sent, and
no unknown fields: the store writes a fresh literal over the whole message, as protobuf-go's
`Unmarshal` resets it first. A unary request decoded is shorter than `2 ^ 32` (its encoding is
below `grpcMsgMax`); a unary reply decoded, below `stringValueMax`; the stream model's received message is owned, and is a sender's message again
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

/-- **The longest `Value` a sender's reply or stream message holds**, below `2 ^ 30` bytes: its
encoding is then below `grpcMsgMax` (`2 ^ 32`), what lets a server that sends `StringValue`s meet
the replies' size bound without the workload premise (`grpcRepliesBounded`). -/
def stringValueMax : Nat := 2 ^ 30

/-- **The longest `Value` a unary request holds**, below `2 ^ 29` bytes: a handler answering a request
with a slightly longer value (the driver's `Echo`: `v + "#1"`) stays below `stringValueMax`. -/
def stringValueReqMax : Nat := 2 ^ 29

/-- **The store of a `StringValue`**: its `Value` (the literal leaves the other fields zero). -/
def stringValueTree (s : GoString) : VTree :=
  .strct wrapperspb.StringValue.ty [(go!"Value", go.string)] [.leaf #s]

/-- **A sender's `*wrapperspb.StringValue`** holding `s`: its `Value`, below the bound `b`, and no
unknown fields. -/
def stringValueSendB (b : Nat) (l : Loc) (s : GoString) : IProp GF :=
  iprop(∃ v : wrapperspb.StringValue, l ↦ v ∗
    ⌜v.Value' = s ∧ v.unknownFields' = slice.nil ∧ s.length < b⌝)

/-- A sender's reply or stream message (below `stringValueMax`). -/
abbrev stringValueSend : Loc → GoString → IProp GF := stringValueSendB stringValueMax

/-- **A `*wrapperspb.StringValue` as a unary method's request** (a trusted wire model): its `Value`,
below `stringValueReqMax`; received, not `null` (the generated handler decodes into its own
`new(Msg)`), its `Value` read-only, below `stringValueReqMax`. -/
def pbStringValue : ProtoMsg GF where
  ty := wrapperspb.StringValue.ty
  M := GoString
  tree := stringValueTree
  send := stringValueSendB stringValueReqMax
  wireLen := stringValueWireLen
  recv r s := iprop(⌜r ≠ null⌝ ∗ ⌜s.length < stringValueReqMax⌝ ∗
    structFieldRef wrapperspb.StringValue go!"Value" r ↦□ s)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val wrapperspb.StringValue))
  own l := iprop(∃ v : wrapperspb.StringValue, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*wrapperspb.StringValue` as a unary method's reply** (a trusted wire model): its `Value`;
received, not `null`, its `Value` read-only, below `stringValueMax`. -/
def pbStringValueR : ProtoMsg GF where
  ty := wrapperspb.StringValue.ty
  M := GoString
  tree := stringValueTree
  send := stringValueSend
  wireLen := stringValueWireLen
  recv r s := iprop(⌜r ≠ null⌝ ∗ ⌜s.length < stringValueMax⌝ ∗
    structFieldRef wrapperspb.StringValue go!"Value" r ↦□ s)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val wrapperspb.StringValue))
  own l := iprop(∃ v : wrapperspb.StringValue, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **`pbStringValue` with its store.** -/
def pbStringValueT : ProtoMsgT GF :=
  { pbStringValue with }

/-- **`pbStringValueR` with its store.** -/
def pbStringValueRT : ProtoMsgT GF :=
  { pbStringValueR with }

/-- A sender's message is not `null`. -/
theorem stringValueSend_null (b : Nat) (m : GoString) : stringValueSendB (GF := GF) b null m ⊢ False := by
  unfold stringValueSendB
  iintro ⟨%v, Hp, -⟩
  ihave %H := typedPointsto_not_null $$ Hp
  exact absurd rfl H

/-- **`pbStringValueT`'s request model is satisfiable.** -/
theorem pbStringValueT_reqSat : (pbStringValueT (GF := GF)).ReqSat := by
  refine ⟨⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    stringValueSend_null _, ?_⟩
  intro ls l m
  change GoString at m
  simp only [pbStringValueT, pbStringValue, stringValueWireLen]
  iintro ⟨Hs, %Hw, Hl⟩
  unfold stringValueSendB
  icases Hs with ⟨%v0, Hv0, %Hv0⟩
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
  isplitl [Hv0]
  · iexists v0; iframe Hv0; ipureintro; exact Hv0
  isplitr
  · isplitr
    · ipureintro; exact Hnn
    isplitr
    · ipureintro; exact Hv0.2.2
    iframe HN
  · ipureintro; trivial

theorem pbStringValueT_wireLen_ok :
    ∃ m, (pbStringValueT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨[], by simp [pbStringValueT, pbStringValue, stringValueWireLen, grpcMsgMax]⟩

/-- **`pbStringValueRT`'s reply model is satisfiable.** -/
theorem pbStringValueRT_repSat : (pbStringValueRT (GF := GF)).RepSat := by
  apply ProtoMsgT.repSat_of_recvOwn_true _ (fun _ _ => rfl)
  refine ⟨⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    ⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    stringValueSend_null _, ?_⟩
  intro ls l m
  change GoString at m
  simp only [pbStringValueRT, pbStringValueR]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  unfold stringValueSend stringValueSendB
  icases Hs with ⟨%v0, Hv0, %Hv0⟩
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
  isplitl [Hv0]
  · iexists v0; iframe Hv0; ipureintro; exact Hv0
  isplitr
  · ipureintro; exact Hnn
  isplitr
  · ipureintro; exact Hv0.2.2
  iframe HN

/-- **A `*wrapperspb.StringValue` on a stream** (a trusted wire model): its `Value`, sent below
`stringValueMax` with no unknown fields; received, the whole message owned, again with no unknown
fields (a sender's message: `recv` is `send`). -/
abbrev pbStringValueS : StreamMsg GF where
  ty := wrapperspb.StringValue.ty
  M := GoString
  cnt := inferInstance
  tree := stringValueTree
  send := stringValueSend
  wireLen := stringValueWireLen
  recv := stringValueSend
  own l := iprop(∃ v : wrapperspb.StringValue, l ↦ v)

/-- **`pbStringValueS` with its store.** -/
def pbStringValueST : StreamMsgT GF :=
  { pbStringValueS with }

/-- **`pbStringValueST`'s store gives its decoded model** (with or without the request's bound). -/
theorem pbStringValueST_store (ls l : Loc) (m : GoString) :
    stringValueSend (GF := GF) ls m ∗ (∃ v : wrapperspb.StringValue, l ↦ v) ⊢
      WP (storeInto wrapperspb.StringValue.ty l (stringValueTree m))
        {{ _v, stringValueSend ls m ∗ stringValueSend l m }} := by
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  unfold stringValueSend stringValueSendB
  icases Hs with ⟨%v0, Hv0, %Hv0⟩
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
  isplitl [Hv0]
  · iexists v0; iframe Hv0; ipureintro; exact Hv0
  iexists _
  iframe Hl
  ipureintro; exact ⟨rfl, rfl, Hv0.2.2⟩

/-- **`pbStringValueST`'s request model is satisfiable.** -/
theorem pbStringValueST_reqSat : (pbStringValueST (GF := GF)).ReqSat := by
  refine ⟨⟨wrapperspb.StringValue, inferInstance, inferInstance,
      (inferInstance : IntoValTyped wrapperspb.StringValue wrapperspb.StringValue.ty), fun l => .rfl⟩,
    stringValueSend_null _, ?_⟩
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
    stringValueSend_null _, ?_⟩
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
axiom pbStringValueRT_repReg :
    grpcRepModelOf GF wrapperspb.StringValue.ty = some (pbStringValueRT (GF := GF))

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
