/-
`MessageType.String()` (`raftpb/raft.pb.go`, protoc-gen-go).

**Assumed (trust boundary).** The method is not translated (`Code/go_etcd_io/raft/v3/raftpb.toml`:
`"!*.String"`, protobuf plumbing): its body is `protoimpl.X.EnumStringOf(x.Descriptor(),
protoreflect.EnumNumber(x))`, the value's name in raftpb's file descriptor (built by the package's
initialization), or its number for an unknown value. It reads only that descriptor, writes nothing
and never panics, for every value.

**Users.** rafthttp's log lines of a dropped or refused message: `transport.go:205` (`Transport.Send`, unknown peer), `peer.go:256` (send buffer full), `remote.go:78,89`, `http.go:256`, `stream.go:537,548` (the stream reader).

**Changes.** From `specs-ref/Spec/go_etcd_io/raft/v3/raftpb/MessageType__String.lean` (the old
`fmt.stringMethodSpec` form): restated as a triple over this branch's conventions; restored at the
verify round (A5-completeness F1: it was left out as "logging only", but translated code calls it).

**Margin.** The string is not specified (only loggers read it).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- **Assumed.** `x.String()` returns some string, for any value. -/
def MessageType.String.spec : Prop :=
  ∀ (x : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (x @!! raftpb.MessageType.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end RaftPb
end EtcdGrove
end Perennial
