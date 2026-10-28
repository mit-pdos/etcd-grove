/- Lean-first (no Rocq counterpart).

`hashString(s)` (check.go): some hash of `s` (FNV-1a; nothing is claimed of it).
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.ModelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- See the file header. -/
abbrev hashString.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.hashString)) (Val #s))
  {{ (h : w64), RET #h; True }}

end spec

end kvwitness
end EtcdGrove
end Perennial
