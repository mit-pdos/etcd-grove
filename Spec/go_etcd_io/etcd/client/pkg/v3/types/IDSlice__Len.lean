/-
`types.IDSlice.Len` (`id.go`; claim #34, stage 2, 2026-11-25: translated with its body, the
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

/-- `p.Len()` of an `IDSlice`: its length. -/
abbrev types.IDSlice.Len.spec : Prop :=
  ∀ (sl : GoSlice) (ids : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ sl ↦*{dq} ids }}
    (App (Val (sl @!! go_etcd_io.etcd.client.pkg.v3.types.IDSlice.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 ids.length); sl ↦*{dq} ids }}

end spec

end EtcdGrove
end Perennial
