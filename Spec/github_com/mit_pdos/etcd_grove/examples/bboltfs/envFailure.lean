/- Lean-first (no Rocq counterpart). `envFailure()` (`examples/bboltfs/programs.go`): counts an environmental failure (`atomic.AddUint64(&envErrors, 1)`) and returns true. The program's package fact `envFacts`: `sync/atomic` is initialized, and `envErrors` lives in an invariant (`envN`), which no proof reads. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- The namespace of `envErrors`'s invariant. -/
def envN : Namespace := nroot .@ "minibolt_env"

/-- What the programs need of the initialized program besides `pkgFacts`: `sync/atomic`'s
initialization, and `envErrors` (some count) in an invariant. -/
def envFacts : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
    inv envN (∃ x : w64, globalAddr github_com.mit_pdos.etcd_grove.examples.bboltfs.envErrors ↦ x))

instance envFacts_persistent : Persistent (envFacts (GF := GF)) := by
  unfold envFacts; infer_instance

/-- See the file header. -/
abbrev envFailure.spec : Prop :=
  {{ envFacts (GF := GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.envFailure)) (Val #()))
  {{ RET #true; True }}

end spec

end bboltfs
end EtcdGrove
end Perennial
