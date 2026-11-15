/-
`labels.Set.Get(k)` (`k8s.io/apimachinery/pkg/labels`) of a non-nil set: the value at `k`, `""` if none (`labels.go:61-63`). Proved from the translated
body (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.4, Q7e-2-4). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apimachinery.pkg.labels.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.labels.Assumptions]

/-- See the file header. -/
abbrev labels.Set.Get.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (M : GMap GoString GoString) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels ∗ m ↦${dq} M }}
    (App (Val #(methods k8s_io.apimachinery.pkg.labels.Set'.ty go!"Get" #m)) (Val #k))
  {{ RET #((M.lookup k).getD []); m ↦${dq} M }}

end spec

end EtcdGrove
end Perennial
