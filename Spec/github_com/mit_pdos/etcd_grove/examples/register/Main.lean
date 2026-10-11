/- Lean-first (no Rocq counterpart).

## `Main()` (cluster.go), the top-level driver

From what package initialization provides (`isPkgInit` of the register's package, which
holds its dependencies', raft's among them), `Main` is safe: it does not panic -- in
particular client B's check that its `Get` returns the value client A put -- and has no
undefined behavior. Everything else (raft's ghost state for the cluster, the term budget
and the tick credits, the storages' and the register's invariants, the operation credits,
the clients' invariant) is allocated in the proof, from nothing. No storage registry is
assumed either: the proof allocates one and instantiates the register's specs at it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end register
end EtcdGrove
end Perennial
