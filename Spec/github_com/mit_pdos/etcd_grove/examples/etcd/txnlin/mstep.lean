/- Lean-first (no Rocq counterpart).

`mstep(in, st)` (etcd_txnlin.go): an operation's effect on the store and its output (`mstepL`). The
store it returns is read-only (it may be `st`). Its premise bounds the store's length (`runOps`'s,
for three operations).
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
abbrev mstep.spec : Prop :=
  ∀ (x : Input) (s : store) (g : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗ storeOwn s g ∗ ⌜g.kvs.length + 4 < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.mstep)) (Val #x)) (Val #s))
  {{ (s' : store) (o : Output), RET (PairV #s' #o);
      storeOwn s' (mstepL x g).1 ∗ ⌜o = (mstepL x g).2⌝ }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
