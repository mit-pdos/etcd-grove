/- Lean-first (no Rocq counterpart).

`Main()` (`examples/k8s/smd/smd.go`): the structured-merge-diff driver. It builds a schema (a Go
literal), an updater (`merge.UpdaterBuilder{Converter: identityConverter{}}.BuildUpdater()`) and an
empty object, then runs nine server-side-apply steps through `merge.Updater.Apply` and `Update`
(managers `A` and `B` apply, `C` updates: creation, a disjoint apply, a co-owning apply of an equal
value, a conflicting apply without force and with force, an apply that prunes, list items by key,
an update that takes ownership, an atomic map replaced whole), and after each one panics unless
the stored object, every manager's owned field set and (step 4) the conflicts are exactly the ones
written in the driver. Its triple says that it returns from the package's initialized state, so
every one of those panics is unreachable: SMD computes exactly those results. The closed theorem
is that the program never panics (`Results.lean`, `TopLevelRobustness.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
