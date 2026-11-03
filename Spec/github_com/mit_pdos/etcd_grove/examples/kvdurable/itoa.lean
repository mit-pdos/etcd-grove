/- Lean-first (no Rocq counterpart).

`itoa(n)` (cluster.go): `n` in decimal (`decimalB`, `Nat.toDigits 10`), what `fileOf` names a file
by (`kdFileName`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev itoa.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.itoa)) (Val #n))
  {{ RET #(decimalB (uint.nat n)); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
