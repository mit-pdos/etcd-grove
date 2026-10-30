/- Lean-first (no Rocq counterpart).

`hashMap(m)` (check.go): some hash of the map `m` (nothing is claimed of it: porcupine's cache
is sound for any hash).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev hashMap.spec : Prop :=
  ∀ (l : Loc) (m : GMap GoString GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗ l ↦${dq} m }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.hashMap)) (Val #l))
  {{ (h : w64), RET #h; l ↦${dq} m }}

end spec

end kvreconf
end EtcdGrove
end Perennial
