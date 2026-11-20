/-
Lean-first (no Rocq counterpart).

`NewWatchValidator(versioner, replay, keyFunc)` (`correctness/watch.go`) with the driver's versioner,
the replay at `rp` and the driver's `keyFunc`, as `realCheck` calls it: the validator `validatorV rp`
(k8s 7g step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev NewWatchValidator.spec : Prop :=
  ∀ (rp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewWatchValidator))
      (Val #(versionerV))) (Val #rp))
      (Val #(functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyFunc [])))
  {{ RET #(validatorV rp); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
