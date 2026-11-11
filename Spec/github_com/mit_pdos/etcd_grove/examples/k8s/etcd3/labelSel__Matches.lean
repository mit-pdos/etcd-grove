/-
`s.Matches(l)` of a `labels.Set` holding `M` (as a `labels.Labels`): `lmL s M`. Stage 7e-2 (`notes/k8s-7e-2-draft.md` §6). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Sel
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj labelSel fieldSel)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev labelSel.Matches.spec : Prop :=
  ∀ (s : labelSel) (m : Loc) (M : GMap GoString GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ mapRO m M }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel.ty go!"Matches" #s))
      (Val #(interface.mkOk k8s_io.apimachinery.pkg.labels.Set'.ty #m)))
  {{ RET #(lmL s M); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
