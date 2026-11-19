/-
`identityConverter.IsMissingVersionError(err)`: `false`.

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI
open smd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- See the file header. -/
abbrev identityConverter.IsMissingVersionError.spec : Prop :=
  ∀ (ic : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.identityConverter) (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd }}
    (App (Val (ic @!! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.identityConverter.ty @!! go!"IsMissingVersionError")) (Val #e))
  {{ RET #false; True }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
