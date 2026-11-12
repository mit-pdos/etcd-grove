/-
## `confChangeToMsg(c)` (internal)

**Users.** `node.ProposeConfChange`, `RawNode.ProposeConfChange`. **Proof sketch.**
`MarshalConfChange` (raftpb, 3h: the entry type and bytes decoding back to `c`; no error for a
well-formed change). **Changes.** Mirrors the code.

**Size premise (integration I2).** `c.wireBound < Proto.marshalMax` (`2^48`: a context under about
`2^47` bytes) is `MarshalConfChange`'s (3h: protobuf-go fails to marshal a larger message; the old
spec had no premise, false of protobuf-go). True of every real change; a client-facing premise until
the user chooses otherwise (3h's open question 3: or a workload premise like grpc's `msgsFit`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- (internal) A `MsgProp` carrying `c` as one entry. -/
def confChangeToMsg.spec : Prop :=

  ∀ (cc : GoInterface) (dq : DFrac) (c : ConfChangeI),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ confChangePts cc dq c ∗ ⌜c.wireBound < Proto.marshalMax⌝ }}
    (App (Val (@! go_etcd_io.raft.v3.confChangeToMsg)) (Val #cc))
  {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err); confChangePts cc dq c ∗
      ⌜err = interface.nil⌝ ∗ ∃ (bs : List w8) (m : Msg), msgPts ml (DFrac.own 1) m ∗
      ⌜m.type = MsgProp ∧ m.entries = [⟨W64 0, c.entryType, bs⟩] ∧
        decodeConfChange c.entryType bs = some c⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
