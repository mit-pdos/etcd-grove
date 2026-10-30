/- Lean-first (no Rocq counterpart).

`sleep(pause, stop)` (reconf.go): a random wait, or until `stop` (a broadcast channel) is closed;
it says whether `stop` came. Nothing is promised of the answer.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev sleep.spec : Prop :=
  ∀ (pause : time.Duration) (stop : Loc) (γc : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      ownBroadcastChan stop γc iprop(True) .Unknown }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.sleep)) (Val #pause))
      (Val #stop))
  {{ (b : Bool), RET #b; True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
