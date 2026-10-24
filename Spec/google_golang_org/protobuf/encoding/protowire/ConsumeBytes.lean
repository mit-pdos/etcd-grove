/-
`protowire.ConsumeBytes`: the trust boundary
(`google.golang.org/protobuf/encoding/protowire` is names-only; the pure model
`protowire.consumeBytes` is in `apply/InvRequest.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf.encoding

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `protowire.ConsumeBytes(s)`: either returns `n < 0` (`protowire.consumeBytes bs = none`), or
consumes `0 ≤ n ≤ bs.length` bytes and returns a subslice `vsl` holding `v` with
`protowire.consumeBytes bs = some (v, sint.nat n)`. -/
abbrev protowire.ConsumeBytes.spec : Prop :=
  ∀ (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.encoding.protowire ∗
      s ↦*{dq} bs }}
    (App (Val (@! protowire.ConsumeBytes)) (Val #s))
  {{ (vsl : GoSlice) (n : w64), RET (PairV #vsl #n);
      (⌜sint.Z n < 0 ∧ protowire.consumeBytes bs = none⌝ ∗ s ↦*{dq} bs) ∨
      (∃ v : List w8,
        ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ bs.length ∧
          protowire.consumeBytes bs = some (v, sint.nat n)⌝ ∗
        vsl ↦*{dq} v ∗ (vsl ↦*{dq} v -∗ s ↦*{dq} bs)) }}

end spec

end EtcdGrove
end Perennial
