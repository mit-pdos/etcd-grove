/-
`sleep(pause, stop)` (kvcheck.go): waits for `stop`'s close (a broadcast channel) or a random
time, and says which. As kvdurable's.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Base
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

/-- See the file header. -/
abbrev sleep.spec : Prop :=
  ∀ (pause : time.Duration) (stop : Loc) (γc : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck ∗
      ownBroadcastChan stop γc iprop(True) .Unknown }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.sleep)) (Val #pause))
      (Val #stop))
  {{ (b : Bool), RET #b; True }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
