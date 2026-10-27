/- Lean-first (no Rocq counterpart).

`within(a, b)` (check.go): whether every key of `a` has the same value in `b` (`""` if `b`
lacks it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.ModelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev within.spec : Prop :=
  ∀ (la lb : Loc) (ma mb : GMap GoString GoString) (dqa dqb : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ la ↦${dqa} ma ∗ lb ↦${dqb} mb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.within)) (Val #la)) (Val #lb))
  {{ (b : Bool), RET #b; la ↦${dqa} ma ∗ lb ↦${dqb} mb ∗
      ⌜b = true ↔ ∀ k v, ma !! k = some v → (mb !! k).getD [] = v⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
