/- Lean-first (no Rocq counterpart).

`cmpsFor(in)` (etcd_txnlin.go): a new slice of the client's comparisons of a transaction's
comparisons that decode to `cs` (`decAll decCmp`), in order (`cmpOf` of each: `linkv.cmpOf`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Client
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
abbrev cmpsFor.spec : Prop :=
  ∀ (x : Input) (cs : List (linkv.MCmp GoString GoString)),
  decAll decCmp (cmpsOfL x) = some cs → 0 ≤ sint.Z x.NCmps' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpsFor)) (Val #x))
  {{ (out : GoSlice), RET #out; cmpsAt out (cs.map linkv.cmpOf) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
