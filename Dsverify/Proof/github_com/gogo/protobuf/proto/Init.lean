/-
**A hypothesis**: gogo/protobuf's `proto` initializer meets Perennial's initialization spec (notes/dsv-rabia.md,
"The hypotheses"). `github_com.gogo.protobuf.proto` is translated names only in the part (the lab replaced it by its model (`harness/rpcmodel/gogoprotobuf/proto`); no model here), so its
`initialize'` cannot be proved here, and the rule is no new axiom: the spec is the class `InitHyp`
(a `Prop`), which every theorem whose proof initializes `github_com.gogo.protobuf.proto` takes as an instance argument
(`etc/gen-init.py`'s `dsv_inits` adds the section variable, `dsv_hyp_fix`, as for dsv-vr), up to the
kit's closed statement. Replace by the model's proved `wp_initialize'` when it lands.

Beside the initializer, the class holds the specs of the three `Register*` functions rabia's
`message` package calls in its `init`s (gogo/protobuf v1.3.2, `proto/properties.go`: `RegisterEnum`
records the two maps under the name, and panics on a name registered before; `RegisterType` records
the type, logging a duplicate; `RegisterFile` records the descriptor). Each returns and touches no
memory of the caller's. `RegisterEnum`'s spec, without a precondition, is true of a name's first
registration only, which is the only one in each of rabia's programs (no other package registers
`message.MsgType`); a model of the library would make it exact (a per-name token).
-/
module

public import Dsverify.Proof.github_com.gogo.protobuf.proto.Base
public import Net.Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace github_com.gogo.protobuf.proto

/-- **Hypothesis** (the file header): `github_com.gogo.protobuf.proto`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.proto get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.proto }}
  /-- `proto.RegisterEnum(typeName, nameMap, valueMap)` (`message.pb.go`'s first `init`). -/
  RegisterEnum : ∀ (typeName : GoString) (nameMap valueMap : Loc),
    {{ (True : IProp GF) }}
      (App (App (App (Val #(functions RegisterEnum [])) (Val #typeName)) (Val #nameMap))
        (Val #valueMap))
    {{ RET #(); True }}
  /-- `proto.RegisterType(x, name)` (`message.pb.go`'s first `init`). -/
  RegisterType : ∀ (x : GoInterface) (name : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val #(functions RegisterType [])) (Val #x)) (Val #name))
    {{ RET #(); True }}
  /-- `proto.RegisterFile(filename, descriptor)` (`message.pb.go`'s second `init`). -/
  RegisterFile : ∀ (filename : GoString) (descriptor : GoSlice),
    {{ (True : IProp GF) }}
      (App (App (Val #(functions RegisterFile [])) (Val #filename)) (Val #descriptor))
    {{ RET #(); True }}

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- Perennial's form of `github_com.gogo.protobuf.proto`'s initialization, from the hypothesis. -/
theorem wp_initialize' [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.proto get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.proto }} :=
  h.wp_init get_is_pkg_init Hinit

end init

end github_com.gogo.protobuf.proto
end Perennial
