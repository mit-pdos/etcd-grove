/- Lean-first (no Rocq counterpart).

`IsWrite(in)` (linkvtxn.go): `isWrite`, exported (remote's codec, `examples/etcd/dist/kvremote`):
whether an input may write (`isWriteL`).
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
abbrev IsWrite.spec : Prop :=
  ∀ (x : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.IsWrite)) (Val #x))
  {{ RET #(isWriteL x); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
