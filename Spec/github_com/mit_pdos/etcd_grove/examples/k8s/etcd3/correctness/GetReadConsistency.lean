/- Lean-first (no Rocq counterpart).

`GetReadConsistency(opts)` (`correctness/consistency.go`): `Consistent` for an empty resource
version, `NotOlderThan` otherwise (k8s 7g step 3).
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
abbrev GetReadConsistency.spec : Prop :=
  ∀ (opts : k8s_io.apiserver.pkg.storage.GetOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.GetReadConsistency))
      (Val #opts))
  {{ RET #(if opts.ResourceVersion' = [] then rconsStr .consistent else rconsStr .notOlderThan);
      True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
