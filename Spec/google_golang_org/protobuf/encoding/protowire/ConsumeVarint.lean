/-
`protowire.ConsumeVarint`: the trust boundary
(`google.golang.org/protobuf/encoding/protowire` is names-only; the pure model
`protowire.consumeVarint` is in `apply/InvRequest.lean`). Lean-first (no Rocq counterpart).
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

/-- `protowire.ConsumeVarint(s)`: either returns `n < 0` (`protowire.consumeVarint bs = none`), or
consumes `0 ≤ n ≤ bs.length` bytes and returns `(v, n)` with
`protowire.consumeVarint bs = some (v, sint.nat n)`. -/
abbrev protowire.ConsumeVarint.spec : Prop :=
  ∀ (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.encoding.protowire ∗
      s ↦*{dq} bs }}
    (App (Val (@! protowire.ConsumeVarint)) (Val #s))
  {{ (v : w64) (n : w64), RET (PairV #v #n);
      s ↦*{dq} bs ∗
      ⌜(sint.Z n < 0 ∧ protowire.consumeVarint bs = none) ∨
        (0 ≤ sint.Z n ∧ sint.nat n ≤ bs.length ∧
          protowire.consumeVarint bs = some (v, sint.nat n))⌝ }}

end spec

end EtcdGrove
end Perennial
