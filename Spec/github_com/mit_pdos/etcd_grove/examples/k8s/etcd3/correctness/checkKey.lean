/- Lean-first (no Rocq counterpart).

`checkKey(key, recursive)` (`correctness/model.go`): `nil` iff `storage.PrepareKey("", key,
recursive)` accepts the key (`k8s.prepareKeyM`) (k8s 7g step 3).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev checkKey.spec : Prop :=
  ∀ (key : GoString) (r : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.checkKey))
      (Val #key)) (Val #r))
  {{ (err : GoInterface), RET #err;
      ⌜(err = GoInterface.nil) ↔ (k8s.prepareKeyM [] key r).isSome⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
