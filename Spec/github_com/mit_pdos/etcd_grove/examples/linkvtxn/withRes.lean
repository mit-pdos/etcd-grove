/- Lean-first (no Rocq counterpart).

`withRes(o, ...)` (linkvtxn.go): `o` with the results `rs` (`withResL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

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
abbrev withRes.spec : Prop :=
  ∀ (o : Output) (sl : GoSlice) (l : List TRes) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗ sl ↦*{dq} l }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.withRes)) (Val #o)) (Val #sl))
  {{ (o' : Output), RET #o'; sl ↦*{dq} l ∗ ⌜o' = withResL o l⌝ }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
