/-
## `pbutil.MustUnmarshalMessage(um, data)`

**Users.** The apply thread (`etcdserver/apply.go:29`: a committed normal entry's
`InternalRaftRequest`, 3a; `server.go`'s `applyConfChange`: a `ConfChange`, 2d), rafthttp's
msgappv2 decoder (an `Entry`), the WAL's and snapshotter's decoders (2e). Snippet: `examples/specreq/pkgleaves/leaves.go`
(`ReqApplyDecode`).

**Proof sketch.** `proto.Unmarshal` (`Proto.Unmarshal.spec`); its error disjunct says no content of
depth below `depthMax` encodes the bytes, which the premise refutes; so `nil` and the content, canonical (`norm c = c`) and a merge
destination (`mergeDst`), as `Proto.Unmarshal.spec` gives it.

**Changes.** From `specs-ref`'s `MustUnmarshalMessage.lean` (two cases, the `ConfChange` and the
`InternalRaftRequest`, each over its own decoder): one spec over `Proto`'s content; each caller's
meaning of the content is its message owner's law (`xOwn ⊣⊢ msgAt ∗ ⌜xModels⌝`).

Second pass (rafthttp's request, after grpc-v3rpc restated `Proto.Unmarshal`): the post is
`Proto.mergeDst t p c` with `Proto.norm c = c` in place of `msgAt` (`mergeDst_msgAt` gives that
back): rafthttp's msgappv2 full-frame decoder needs a canonical content for raftpb's
`msgRecv_intro`.

**Margin.** None.
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

/-- **Decodes `data` into the message**: a canonical content the bytes encode (they encode one of
nesting below `depthMax`: else it panics), the message a merge destination. -/
def MustUnmarshalMessage.spec : Prop :=
  ∀ (t : go.GoType) (p : Loc) (c0 : Proto.Content) (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ Proto.msgAt t p (DFrac.own 1) c0 ∗ b ↦*{dq} bs ∗
      ⌜∃ c, Proto.encodes t c bs ∧ Proto.depth c < Proto.depthMax⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage)) (Val #(Proto.msgVal t p)))
      (Val #b))
  {{ RET #(); b ↦*{dq} bs ∗ ∃ c, Proto.mergeDst t p c ∗ ⌜Proto.encodes t c bs ∧ Proto.norm c = c⌝ }}

end spec
end PbUtil
end EtcdGrove
end Perennial
