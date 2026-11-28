/- Lean-first (no Rocq counterpart).

`withKVs(o, ...)` (etcd_txnlin.go): `o` with the key-values `kvs` (`withKVsL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.lib.txnwork


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Assumptions]

/-- See the file header. -/
abbrev withKVs.spec : Prop :=
  ∀ (o : Output) (sl : GoSlice) (l : List KV) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork ∗ sl ↦*{dq} l }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.withKVs)) (Val #o)) (Val #sl))
  {{ (o' : Output), RET #o'; sl ↦*{dq} l ∗ ⌜o' = withKVsL o l⌝ }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
