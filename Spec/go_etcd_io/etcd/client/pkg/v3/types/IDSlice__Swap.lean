/-
`types.IDSlice.Swap` (`id.go`; claim #34, stage 2, 2026-11-25: translated with its body, the
sort of `MemberIDs`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.types
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `p.Swap(i, j)` of an `IDSlice`: the two ids swapped. -/
abbrev types.IDSlice.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (ids : List w64) (i j a b : w64),
  0 ≤ sint.Z i → 0 ≤ sint.Z j → ids[sint.nat i]? = some a → ids[sint.nat j]? = some b →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ sl ↦* ids }}
    (App (App (Val (sl @!! go_etcd_io.etcd.client.pkg.v3.types.IDSlice.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* (ids.set (sint.nat i) b).set (sint.nat j) a }}

end spec

end EtcdGrove
end Perennial
