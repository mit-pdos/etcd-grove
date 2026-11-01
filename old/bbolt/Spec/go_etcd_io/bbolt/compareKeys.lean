module
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `compareKeys(left, right)`: `bytes.Compare`. -/
abbrev compareKeys.spec : Prop :=
  ∀ (l r : GoSlice) (a b : List w8) (da db : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ l ↦*{da} a ∗ r ↦*{db} b }}
    (App (App (Val #(functions compareKeys [])) (Val #l)) (Val #r))
  {{ RET #(bytes.compareResult a b); l ↦*{da} a ∗ r ↦*{db} b }}

end spec

end bbolt
end EtcdGrove
end Perennial
