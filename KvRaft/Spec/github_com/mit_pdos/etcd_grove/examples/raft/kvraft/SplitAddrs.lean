/-
`SplitAddrs(s)` (addrs.go): the slice of the pieces of `s` between its commas, `splitAddrs s`
(the net extension's `splitBy 44`), owned with its capacity.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev SplitAddrs.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.SplitAddrs)) (Val #s))
  {{ (sl : GoSlice), RET #sl; sl ↦* splitAddrs s ∗ ownSliceCap GoString sl (DFrac.own 1) }}

end spec

end kvraft
end EtcdGrove
end Perennial
