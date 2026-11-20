/- Lean-first (no Rocq counterpart).

`NewEmptyModel(prefix, newFunc, newListFunc, versioner)` (`correctness/model.go`): a fresh
`*Model` with an empty items map, resource version 1, the given prefix and functions, and a nil
`NeedsRewrite` (k8s 7g step 3; `initialModel` fills it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev NewEmptyModel.spec : Prop :=
  ∀ (pfx : GoString) (nf nlf : GoFunc) (v : k8s_io.apiserver.pkg.storage.Versioner),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewEmptyModel)) (Val #pfx)) (Val #nf)) (Val #nlf)) (Val #v))
  {{ (mp il : Loc), RET #mp;
      mp ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.mk il (W64 1) 0 pfx v nf nlf null ∗
      il ↦$ (∅ : GMap GoString GoInterface) }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
