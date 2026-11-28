/-
Lean-first (no Rocq counterpart).

`PinnedRead(in)` (`examples/k8s/etcd3/export.go`; k8s-dist K9 step 5): returns `pinnedReadL in`
(`ExportL.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ExportL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev PinnedRead.spec : Prop :=
  ∀ (x : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PinnedRead)) (Val #x))
  {{ RET #(pinnedReadL x); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
