/-
`protowire.ConsumeFieldValue`: the trust boundary
(`google.golang.org/protobuf/encoding/protowire` is names-only; the pure model
`protowire.consumeFieldValue` is in `apply/InvRequest.lean`). Lean-first (no Rocq counterpart).
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

/-- `protowire.ConsumeFieldValue(num, typ, s)`: either returns `n < 0`
(`protowire.consumeFieldValue num typ bs = none`), or consumes `0 ≤ n ≤ bs.length` bytes with
`protowire.consumeFieldValue num typ bs = some (sint.nat n)`. -/
abbrev protowire.ConsumeFieldValue.spec : Prop :=
  ∀ (num : w32) (typ : w8) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.encoding.protowire ∗
      s ↦*{dq} bs }}
    (App (App (App (Val (@! protowire.ConsumeFieldValue)) (Val #num)) (Val #typ)) (Val #s))
  {{ (n : w64), RET #n;
      s ↦*{dq} bs ∗
      ⌜(sint.Z n < 0 ∧ protowire.consumeFieldValue num typ bs = none) ∨
        (0 ≤ sint.Z n ∧ sint.nat n ≤ bs.length ∧
          protowire.consumeFieldValue num typ bs = some (sint.nat n))⌝ }}

end spec

end EtcdGrove
end Perennial
