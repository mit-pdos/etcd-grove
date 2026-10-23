/- Lean-first (no Rocq counterpart).

`mupdate(in, st)` (k8setcd3.go): `mupdateL` of the store it holds. Its premise bounds the
items' number (`setItem`'s).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev mupdate.spec : Prop :=
  ∀ (x : Input) (s : mstore) (g : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ storeOwn s g ∗ ⌜g.items.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.mupdate)) (Val #x)) (Val #s))
  {{ (s' : mstore) (y : Output), RET (PairV #s' #y);
      storeOwn s' (mupdateL x g).1 ∗ ⌜y = (mupdateL x g).2⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
