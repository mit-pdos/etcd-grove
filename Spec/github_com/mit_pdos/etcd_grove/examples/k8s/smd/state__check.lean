/-
`(*state).check(obj, managers, msg)`: returns (does not panic) when the model's `stCheck` holds:
the stored object equals `obj` and the managed fields equal `managers`.

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
abbrev state.check.spec : Prop :=
  ∀ (s sc : Loc) (st : St) (m : GoMap) (kvs : List (GoString × UVal)) (mfm : GoMap) (mf : MF)
    (msg : GoString),
  stCheck st (.map kvs) mf = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd ∗ ownState s sc st ∗ ownUMap m kvs ∗ ownMF mfm mf }}
    (App (App (App (Val (s @!! go.GoType.PointerType _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.ty @!! go!"check")) (Val #m)) (Val #mfm))
      (Val #msg))
  {{ RET #(); ownState s sc st }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
