/- Lean-first (no Rocq counterpart).

`cmpOf(c)` (etcd_txnlin.go): the client's comparison of a transaction comparison that decodes to
`m` (`decCmp`): `Compare(Value(k), "=", v)`, `Compare(Version(k), "=", n)` or
`Compare(ModRevision(k), "=", n)`, the comparison the model's is sent as (`linkv.cmpOf`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Enc
public import Proof.go_etcd_io.etcd.client.v3.InvCmp

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
abbrev cmpOf.spec : Prop :=
  ∀ (c : Cmp) (m : linkv.MCmp GoString GoString), decCmp c = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpOf)) (Val #c))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cmpAt c' (linkv.cmpOf m) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
