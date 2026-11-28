/- Lean-first (no Rocq counterpart).

`rvOfMsg(msg)` (export.go, notes/k8s-dist-k9.md §2.7): exactly `rvOfMsgL msg`, the resource version
after the first occurrence of `"ResourceVersion in object meta: "`, or 0.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HistRevsDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev rvOfMsg.spec : Prop :=
  ∀ (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvOfMsg)) (Val #msg))
  {{ RET #(rvOfMsgL msg); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
