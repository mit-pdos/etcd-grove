/- Lean-first (no Rocq counterpart).

`mstep(in, st)` (k8setcd3.go): `mstepL` of the store it holds. Its premise bounds the items'
number (`setItem`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev mstep.spec : Prop :=
  ∀ (x : Input) (s : mstore) (g : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ storeOwn s g ∗ ⌜g.items.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.mstep)) (Val #x)) (Val #s))
  {{ (s' : mstore) (o : Output), RET (PairV #s' #o);
      storeOwn s' (mstepL x g).1 ∗ ⌜o = (mstepL x g).2⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
