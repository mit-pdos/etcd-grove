/-
`cloneBytes` (bbolt, internal; U6 of `notes/bbolt-proof-plan.md`): a fresh copy of a byte slice.
Proof: `Proof/go_etcd_io/bbolt/cloneBytes.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `cloneBytes(v)`: a new slice (length and capacity `len(v)`, owned) holding `v`'s bytes. -/
abbrev cloneBytes.spec : Prop :=
  ∀ (v : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ v ↦*{dq} bs }}
    (App (Val #(functions cloneBytes [])) (Val #v))
  {{ (c : GoSlice), RET #c; c ↦* bs ∗ ownSliceCap w8 c (DFrac.own 1) ∗ v ↦*{dq} bs }}

end spec

end bbolt
end EtcdGrove
end Perennial
