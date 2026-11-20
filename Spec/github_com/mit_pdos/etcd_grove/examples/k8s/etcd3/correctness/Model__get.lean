/- Lean-first (no Rocq counterpart).

`(*Model).get(key, opts)` (`correctness/model.go`) on the frozen model `m`, with `key` the store key
of `x`'s key and `opts` `realRequest(x)`'s `GetOptions` (resource version `MinRV`,
`IgnoreNotFound`): the response `rgetL x m` (k8s 7g step 3).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev Model.get.spec : Prop :=
  ∀ (mp : Loc) (m : RM) (x : Input) (opts : k8s_io.apiserver.pkg.storage.GetOptions),
  opts.ResourceVersion' = x.MinRV' → opts.IgnoreNotFound' = x.IgnoreNotFound' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗ modelAt mp m }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"get" #mp))
      (Val #(k8s_etcd3.storeKeyL x.Key'))) (Val #opts))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response), RET #r;
      respRep r (rgetL x m) }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
