/- Lean-first (no Rocq counterpart).

`withRes(o, ...)` (etcd_txnlin.go): `o` with the results `rs` (`withResL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.txnlin


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

/-- See the file header. -/
abbrev withRes.spec : Prop :=
  ∀ (o : Output) (sl : GoSlice) (l : List TRes) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗ sl ↦*{dq} l }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.withRes)) (Val #o)) (Val #sl))
  {{ (o' : Output), RET #o'; sl ↦*{dq} l ∗ ⌜o' = withResL o l⌝ }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
