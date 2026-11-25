/- Lean-first (no Rocq counterpart).

`itoa(n)` (cluster.go): `n` in decimal (`decimalB`, `Nat.toDigits 10`), what `fileOf` names a file
by (`kdFileName`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev itoa.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.itoa)) (Val #n))
  {{ RET #(decimalB (uint.nat n)); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
