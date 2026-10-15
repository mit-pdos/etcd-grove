/-
`raftpb.ConfChangeType.String` (`raft.pb.go:264`, gogoproto; not translated): the trust
boundary. Lean-first (no Rocq counterpart). Needed since the merge with `lean` (Perennial
`a54e1999f`): `confchange.Changer.apply`'s `fmt.Errorf("unexpected conf type %d", cc.Type)`
passes a `ConfChangeType`, a named type, which Perennial's `fmt.wp_Errorf` does not admit
(`fmt.ArgsWf`: arguments of predeclared basic types only); etcd-grove's `fmt.Errorf` axiom
(`Spec/fmt/Errorf.lean`) admits an argument whose `String()` returns some string.
-/
module

public import Spec.fmt.Errorf
public import Code.go_etcd_io.raft.v3.raftpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (gogoproto's generated enum method, not translated). A `ConfChangeType`'s
`String()` returns some string, needing nothing and changing nothing (`fmt.stringMethodSpec`).

Read against `raft.pb.go`: `func (x ConfChangeType) String() string { return
proto.EnumName(ConfChangeType_name, int32(x)) }`; `proto.EnumName` looks the value up in the
package-level map `ConfChangeType_name` (written only by the package's initializer) and returns
the name, or the decimal string of the value when there is none. -/
abbrev raftpb.ConfChangeType.String.spec : Prop :=
  ∀ (t : w32),
    ⊢ fmt.stringMethodSpec (GF := GF) (interface.mk raftpb.ConfChangeType.ty #t) go!"String"

end spec

end EtcdGrove
end Perennial
