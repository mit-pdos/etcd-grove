/-
## `pbutil.MustMarshalMessage(m)`

**Users.** rafthttp's message encoders (`msg_codec.go:40`, `msgappv2_codec.go:91,107`,
`pipeline.go:99`: a raft message, any fraction of it), the snapshotter (`snapshotter.go`: a
`raftpb.Snapshot`). Snippet: `pbutil.go` (`ReqMarshalRoundTrip`).

**Proof sketch.** `proto.Marshal` (`Proto.Marshal.spec`, `fits`); its error disjunct is excluded by
`marshalOk`; `fmt.Sprintf`/`panic` unreachable.

**Changes.** From `specs-ref`'s `MustMarshalMessage.lean` (over the old `PbType` record, unsound,
`pbenc-ok-inconsistent.md`): over `Proto`'s content. The capacity of the returned slice is not
given (no caller appends to it).

**Margin.** The bytes are `Marshal`'s deterministic output for a type without maps (`marshalOut`).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace PbUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

/-- **The message's encoding**, fresh; the message kept. -/
def MustMarshalMessage.spec : Prop :=
  ∀ (t : go.GoType) (p : Loc) (dq : DFrac) (c : Proto.Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ Proto.msgAt t p dq c ∗ ⌜c.fits ∧ Proto.marshalOk c⌝ }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage)) (Val #(Proto.msgVal t p)))
  {{ (b : GoSlice), RET #b; Proto.msgAt t p dq c ∗ ∃ bs : List w8, b ↦* bs ∗
      ⌜Proto.encodes t c bs ∧ (Proto.noMaps t → bs = Proto.marshalOut t c)⌝ }}

end spec
end PbUtil
end EtcdGrove
end Perennial
