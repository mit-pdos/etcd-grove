/- Lean-first (no Rocq counterpart).

`opsOf(ops)` (linkvtxn.go): a new slice of the client's operations of transaction operations
that decode to `ms` (`decAll decTOp`), in order (`opOf` of each: `clientOp`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev opsOf.spec : Prop :=
  ∀ (sl : GoSlice) (ops : List TOp) (dq : DFrac) (ms : List (linkv.MOp GoString GoString)),
  decAll decTOp ops = some ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ sl ↦*{dq} ops }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.opsOf)) (Val #sl))
  {{ (out : GoSlice), RET #out; sl ↦*{dq} ops ∗ opsAt out (ms.map clientOp) }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
