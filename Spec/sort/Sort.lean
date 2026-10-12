module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `sort.Sort(data)` for the two slice types of `uint64`s bbolt sorts (`common.Pgids` and the
freelist's `txIDx`, whose `Less` is `<`, proved: `Pgids.Less`, `txIDx.Less`): the slice ends
sorted, a permutation of what it held. `sort.Sort` (pdqsort) is translated names-only; this
spec is an axiom (`Proof/sort/Sort.lean`). -/
abbrev sort.Sort.spec : Prop :=
  ∀ (T : go.GoType) (s : GoSlice) (xs : List w64),
  T = go_etcd_io.bbolt.internal.common.Pgids.ty ∨ T = txIDx.ty →
  {{ (s ↦* xs : IProp GF) }}
    (App (Val #(functions _root_.Perennial.sort.«Sort» [])) (Val #(interface.mkOk T #s)))
  {{ (ys : List w64), RET #(); ⌜PgidsSorted ys ∧ ys.Perm xs⌝ ∗ s ↦* ys }}

end spec

end bbolt
end EtcdGrove
end Perennial
