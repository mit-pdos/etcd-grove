/-
`DialTCP(addr, timeout)` (`examples/raft/kvnet/client.go`): `net.DialTimeout("tcp", addr,
timeout)`, so `net.DialTimeout`'s spec at the network `"tcp"` (`Net/Spec/net/DialTimeout.lean`): for
a valid address, the caller's update takes the new connection's resources (`Qok cn`, with the end
`false` of `cn` the result) or, the dial abandoned, gives `Qfail`; a failure is an `*OpError` of
`"dial"`.
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
abbrev DialTCP.spec : Prop :=
  ∀ (a : GoString) (dur : _root_.Perennial.time.Duration) (et ed : GoInterface) (Qfail : IProp GF)
    (Qok : Nat → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      ⌜addrOk a = true⌝ ∗ globalAddr net.errTimeout ↦□ et ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      (Qfail ∧
        |={⊤,∅}=> ∃ S, netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ∗
          ∀ cn, ⌜cn ∉ S⌝ -∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a (S ∪ {[cn]}) -∗
            netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
            netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn true -∗
            ((netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ={∅,⊤}=∗ Qok cn) ∧
             (netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false
                { NetEnd.fresh with closed := true } -∗
              netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ⟨[], .fin⟩ ={∅,⊤}=∗
                Qfail))) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.DialTCP)) (Val #a))
      (Val #dur))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, net.isConn (GF := GF) c cn false a ∗ Qok cn) ∨
      (Qfail ∗ ∃ x e, net.netAddr x ∗ net.opErr go!"dial" interface.nil x e err ∗
        (net.sysErr (fun _ => True) e ∨ ⌜e = et ∨ e = ed⌝)) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
