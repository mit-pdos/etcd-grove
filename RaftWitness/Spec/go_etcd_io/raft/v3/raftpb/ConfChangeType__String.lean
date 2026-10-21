/-
`raftpb.ConfChangeType.String` (`raftpb/raft.pb.go:312`, protoc-gen-go; names-only in the
translation, `Code/go_etcd_io/raft/v3/raftpb.toml`): the trust boundary. The old proof's
axiom (`Spec/go_etcd_io/raft/v3/raftpb/ConfChangeType__String.lean`) restated for the raft v3.7
translation (2026-10-15, raft v3.7 retarget, stage R2): `confchange.Changer.apply`'s
`fmt.Errorf("unexpected conf type %d", cc.GetType())` passes a `ConfChangeType`, a named type,
which Perennial's `fmt.wp_Errorf` does not admit (`fmt.ArgsWf`: arguments of predeclared basic
types only); etcd-grove's `fmt.Errorf` axiom (`Spec/fmt/Errorf.lean`) admits an argument whose
`String()` returns some string.
-/
module

public import Spec.fmt.Errorf
public import RaftWitness.Code.go_etcd_io.raft.v3.raftpb

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

/-- **Trust boundary** (protoc-gen-go's generated enum method, not translated). A
`ConfChangeType`'s `String()` returns some string, needing nothing and changing nothing
(`fmt.stringMethodSpec`).

Read against raft v3.7's `raft.pb.go`: `func (x ConfChangeType) String() string { return
protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x)) }`; `EnumStringOf` looks
the number up in the enum's descriptor (built by the package's initializer, read-only after)
and returns its name, or the decimal string of the number when there is none. -/
abbrev raftpb.ConfChangeType.String.spec : Prop :=
  ∀ (t : w32),
    ⊢ fmt.stringMethodSpec (GF := GF) (interface.mk raftpb.ConfChangeType.ty #t) go!"String"

end spec

end EtcdGrove
end Perennial
