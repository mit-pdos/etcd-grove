/- Lean-first (no Rocq counterpart).

`shows(in, out, key, r)` (export.go, notes/k8s-dist-k9.md §2.5): exactly `showsL`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore mcfg Input Output Revs)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev shows.spec : Prop :=
  ∀ (x : Input) (y : Output) (key : GoString) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.shows)) (Val #x)) (Val #y)) (Val #key)) (Val #r))
  {{ RET #(showsL x y key r); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
