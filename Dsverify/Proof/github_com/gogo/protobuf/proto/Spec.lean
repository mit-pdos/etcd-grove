/-
gogo/protobuf's `proto` registration functions rabia's `message` package calls in its `init`s
(`message.pb.go`), as **hypotheses** (notes/dsv-rabia.md, "The hypotheses"): `proto` is translated
names only in the part (the lab replaced it by its model, `harness/rpcmodel/gogoprotobuf/proto`; no
model here), so the specs are the fields of the class `Hyps` (a `Prop`), which every theorem whose
proof initializes `rabia.internal.message` takes as an instance argument (`etc/dsv/rabia.py`'s
`vars`), up to the kit's closed statement. Until #24 they were fields of `proto`'s `InitHyp` with
precondition `True`; an `InitHyp` asserts only that the package's initializer runs without
panicking (`etc/dsv/README.md`).

What gogo/protobuf v1.3.2 does (`proto/properties.go`): each function writes a registry map of
the package (`enumValueMaps`; `protoTypedNils` and `revProtoTypes`; `protoFiles`), unsynchronized,
and returns. `RegisterEnum(typeName, ...)` panics if `typeName` was registered before;
`RegisterType` logs a duplicate and returns, and panics on a `nil` interface (`reflect.Zero(nil)`:
measured, gogo v1.3.2, go1.27.3; `notes/axiom-review/dsv-inits/github-com-gogo-protobuf-proto.md`);
`RegisterFile` overwrites. So the preconditions:
* `RegisterType`'s argument is not the `nil` interface (dsv-fix3, 2026-11-25: until then the spec
  claimed no panic for every `x`, false of Go; rabia's calls pass typed `nil` pointers);

* every call holds the program's package state `ownGoState σ` (exclusive, returned): the calls
  are made by package initializers, which Go runs one at a time, so no two registrations race
  (with precondition `True` the specs claimed concurrent calls safe);
* `RegisterEnum` is required to be **called inside `message`'s initialization**, once: it is
  stated for `message`'s name `"message.MsgType"` only and consumes the points-to of `message`'s
  variable `MsgType_value`, which only `message`'s initializer holds (it allocates the variable,
  `wp_GlobalAlloc`; `message`'s package fact holds no part of it), and only once. So the spec
  covers exactly the one registration of that name in each of rabia's programs (no other package
  of the twelve programs registers `message.MsgType`), and a second registration, which panics,
  is not covered.
-/
module

public import Dsverify.Proof.github_com.gogo.protobuf.proto.Base
public import Dsverify.Code.rabia.internal.message

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace github_com.gogo.protobuf.proto

/-- **The hypotheses** (the file header). -/
class Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  /-- `proto.RegisterEnum("message.MsgType", MsgType_name, MsgType_value)` (`message.pb.go`'s
  first `init`): inside `message`'s initialization, once (the header). -/
  RegisterEnum : ∀ (σ : GMap GoString Bool) (nameMap valueMap : Loc),
    {{ (ownGoState σ : IProp GF) ∗
        globalAddr rabia.internal.message.MsgType_value ↦ valueMap }}
      (App (App (App (Val #(functions RegisterEnum [])) (Val #(go!"message.MsgType")))
        (Val #nameMap)) (Val #valueMap))
    {{ RET #(); ownGoState σ }}
  /-- `proto.RegisterType(x, name)` (`message.pb.go`'s first `init`), `x` not the `nil` interface
  (Go panics on it, the file header). -/
  RegisterType : ∀ (σ : GMap GoString Bool) (x : GoInterface) (name : GoString),
    {{ ⌜x ≠ interface.nil⌝ ∗ (ownGoState σ : IProp GF) }}
      (App (App (Val #(functions RegisterType [])) (Val #x)) (Val #name))
    {{ RET #(); ownGoState σ }}
  /-- `proto.RegisterFile(filename, descriptor)` (`message.pb.go`'s second `init`). -/
  RegisterFile : ∀ (σ : GMap GoString Bool) (filename : GoString) (descriptor : GoSlice),
    {{ (ownGoState σ : IProp GF) }}
      (App (App (Val #(functions RegisterFile [])) (Val #filename)) (Val #descriptor))
    {{ RET #(); ownGoState σ }}

end github_com.gogo.protobuf.proto
end Perennial
