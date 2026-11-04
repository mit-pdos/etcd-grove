/- Lean-first (no Rocq counterpart).

`opOf(op)` (etcd_txnlin.go): the client's operation of a transaction operation that decodes to `m`
(`decTOp`): `OpGet(k)`, `OpPut(k, v)` or `OpDelete(k)` (`clientOp m`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Client

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
abbrev opOf.spec : Prop :=
  ∀ (op : TOp) (m : linkv.MOp GoString GoString), decTOp op = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.opOf)) (Val #op))
  {{ (o : go_etcd_io.etcd.client.v3.Op), RET #o; opFullAt o (clientOp m) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
