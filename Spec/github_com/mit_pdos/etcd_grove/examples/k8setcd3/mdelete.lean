/- Lean-first (no Rocq counterpart).

`mdelete(in, st)` (k8setcd3.go): `mdeleteL` of the store it holds.
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
abbrev mdelete.spec : Prop :=
  ∀ (x : Input) (s : mstore) (g : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ storeOwn s g }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.mdelete)) (Val #x)) (Val #s))
  {{ (s' : mstore) (y : Output), RET (PairV #s' #y);
      storeOwn s' (mdeleteL x g).1 ∗ ⌜y = (mdeleteL x g).2⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
