/- Lean-first (no Rocq counterpart).

`(*Model).Clone()` (`correctness/model.go`): a fresh, owned `*Model` with the same contents (the
items deep-copied, `NeedsRewrite` cloned) (k8s 7g step 3).
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
abbrev Model.Clone.spec : Prop :=
  ∀ (mp : Loc) (m : RM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗ modelAt mp m }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"Clone" #mp)) (Val #()))
  {{ (mp' : Loc), RET #mp'; modelOwn mp' m }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
