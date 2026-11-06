/- Lean-first (no Rocq counterpart).

`cmpStore(a, b)` (linkvtxn.go): -1, 0 or 1 as the store `a` holds contents below, equal to or
above `b`'s in `cmpStO`'s order (the revision, then the entries).
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
abbrev cmpStore.spec : Prop :=
  ∀ (a b : store) (ga gb : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗ storeOwn a ga ∗ storeOwn b gb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStore)) (Val #a)) (Val #b))
  {{ RET #(ordW (cmpStO ga gb)); True }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
