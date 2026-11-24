/-
`closeAfter(c, d)` (timeout.go): a connection deadline as a timer (`time.AfterFunc`): unless
disarmed first, the timer closes `c` (the end `s` of the TCP connection `cn`). The caller hands over
`R`, the right to close the end: with it, the accessor (persistent) opens the end's state and the
direction from it for a `Close` and closes them at what it left (`CloseOutcome`, D1), as
`net.Conn.Close.spec` takes it. The timer and the returned function `disarm` race for `R` under a
mutex: the timer that wins closes `c` with it; a `disarm` that wins returns `true` and gives `R`
back (the timer then does nothing); otherwise `disarm` returns `false` and `R` is gone (`c` is
closed or being closed). `disarm` may be called any number of times (a later call returns `false`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev closeAfter.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (d : _root_.Perennial.time.Duration)
    (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      net.isConn (GF := GF) c cn s a ∗ R ∗
      □ (R -∗ |={⊤,∅}=> ∃ st dd, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s dd ∗
          ∀ res st' d', ⌜CloseOutcome st dd res st' d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ True) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.closeAfter)) (Val #c))
      (Val #d))
  {{ (disarm : GoFunc), RET #disarm;
      □ (∀ Φ : val → IProp GF, (∀ inTime : Bool, (if inTime then R else True) -∗ Φ #inTime) -∗
        WP (App (Val #disarm) (Val #())) {{ Φ }}) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
