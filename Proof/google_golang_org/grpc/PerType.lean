/-
**Per-type prototype: gRPC's message models at registered types** (stage A prototype; the Scope's
R and V for `ProtoMsg` and `StreamMsg`, revisions 4, 5 and 5a). Prototype only: the real stage puts
`tree` in `ProtoMsg`/`StreamMsg` themselves; here they extend them.

- **Role-split registries** (`[v5]`): `grpcReqModelOf` (a method's request) and `grpcRepModelOf` (its
  reply), and `streamMsgModelOf`; each keyed on the Go type, taking the heap's instances.
- **The `Sat` statements** (`[v5]` V): a decoded message's model is satisfiable by the generic store
  (`Store.lean`) of `T.tree m`, keeping the sender's `send`:
  - `ProtoMsgT.ReqSat`: from a `blank`, with the request's `wireLen` below `grpcMsgMax`, the store
    gives `recv` and `recvOwn`;
  - `ProtoMsgT.RepSat`: from an `own` (what a failed attempt leaves), no `wireLen` premise, the
    store gives `recv`;
  - `StreamMsgT.Sat`: the `own` form.
  Each with the laws that make its resources satisfiable: `blank` the zero struct, `own` any
  struct (`OwnAny`), `send` at `nil` false.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.google_golang_org.protobuf.proto.PerType

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A unary method's message model with its normalizing store. -/
structure ProtoMsgT (GF : BundledGFunctors) extends ProtoMsg GF where
  tree : M → VTree

/-- A stream's message model with its normalizing store. -/
structure StreamMsgT (GF : BundledGFunctors) extends StreamMsg GF where
  tree : M → VTree

/-- **`own` is any struct** of the type at some Lean representation (the one the store's type is). -/
def OwnAny (ty : go.GoType) (own : Loc → IProp GF) : Prop :=
  ∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V) (_ : IntoValTyped (GF := GF) V ty),
    ∀ l, own l ⊣⊢ ∃ v : V, l ↦ v

/-- **A request model is satisfiable** (`[v5]`). -/
def ProtoMsgT.ReqSat (T : ProtoMsgT GF) : Prop :=
  BlankZero T.ty T.blank ∧ OwnAny T.ty T.own ∧ (∀ m, T.send null m ⊢ False) ∧
  ∀ (ls l : Loc) (m : T.M),
    T.send ls m ∗ ⌜T.wireLen m < grpcMsgMax⌝ ∗ T.blank l ⊢
      WP (storeInto T.ty l (T.tree m)) {{ _v, T.send ls m ∗ T.recv l m ∗ T.recvOwn l m }}

/-- **A reply model is satisfiable** (`[v5]`): no `wireLen` premise. -/
def ProtoMsgT.RepSat (T : ProtoMsgT GF) : Prop :=
  BlankZero T.ty T.blank ∧ OwnAny T.ty T.own ∧ (∀ m, T.send null m ⊢ False) ∧
  ∀ (ls l : Loc) (m : T.M),
    T.send ls m ∗ T.own l ⊢ WP (storeInto T.ty l (T.tree m)) {{ _v, T.send ls m ∗ T.recv l m }}

/-- **A stream message model is satisfiable** (`[v5]`): the `own` form. -/
def StreamMsgT.Sat (T : StreamMsgT GF) : Prop :=
  OwnAny T.ty T.own ∧ (∀ m, T.send null m ⊢ False) ∧
  ∀ (ls l : Loc) (m : T.M),
    T.send ls m ∗ T.own l ⊢ WP (storeInto T.ty l (T.tree m)) {{ _v, T.send ls m ∗ T.recv l m }}

/-- **The registry of request models** (`[v5]`: split by role). -/
opaque grpcReqModelOf {hlc : HasLC} (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [hG : HeapGS hlc GF] [go.Semantics] : go.GoType → Option (ProtoMsgT GF)

/-- **The registry of reply models**. -/
opaque grpcRepModelOf {hlc : HasLC} (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [hG : HeapGS hlc GF] [go.Semantics] : go.GoType → Option (ProtoMsgT GF)

/-- **The registry of stream message models**. -/
opaque streamMsgModelOf {hlc : HasLC} (GF : BundledGFunctors) [GooseExts] [GooseSemantics]
    [GooseInterp] [GoGlobalContext] [hG : HeapGS hlc GF] [go.Semantics] :
    go.GoType → Option (StreamMsgT GF)

end defs

end EtcdGrove
end Perennial
