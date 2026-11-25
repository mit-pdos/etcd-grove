/-
Lean-first (no Rocq counterpart).

# The store's raft logger (2026-11-01, the cluster helpers)

`quietLogger{}` as a `raft.Logger` (kvreconf's `qLogger`, `kvreconf/Base.lean`), at kvdurable's
`quietLogger`: what `Cluster.config` sets `Config.Logger` to.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI

/-- The store's `quietLogger` type. -/
abbrev qLoggerTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvnet.quietLogger.ty

/-- `quietLogger{}`. -/
abbrev qLoggerV [GooseExts] : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.quietLogger :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvnet.quietLogger.mk

/-- `quietLogger{}` as a `raft.Logger`. -/
def qLogger [GooseExts] [GoGlobalContext] : GoInterfaceOk := interface.mk qLoggerTy #qLoggerV

end raft_kvnet
end EtcdGrove
end Perennial
