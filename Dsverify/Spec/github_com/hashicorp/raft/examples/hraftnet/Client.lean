/-
`hraftnet.Client`'s spec (the hraft kit's client machines, notes/dsv-hraft.md, S5f).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ClientDeps
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : Net.NetProtoGS] [ρ : github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS]

open github_com.hashicorp.raft.examples.hraftnet github_com.mit_pdos.etcd_grove.examples.lib.remote

/-- `Client(c)`, `c < 5`: client machine `c` (it never returns). Its share of the start: net/rpc's codec
unregistered, the world's services and server addresses, the draw's invariant, the ids' invariant and
client `c`'s counter at 1, its address serving the far side's store `regR`, whose budget `N` keeps the
operations' counts below `2 ^ 56`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.Client.spec : Prop :=
  ∀ (K : HK GF) (c N : Nat), c < 5 → N + 1 < 2 ^ 56 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        sync.isMutex (globalAddr net.rpc.codecMu) (net.rpc.codecInv (GF := GF)) ∗ net.rpc.codecUnset ∗
        ⌜kitSS K⌝ ∗ drawInv K ∗ idInv K.g ∗ seqOwn K.g c 1 ∗
        ([∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) ∗
        remoteAddr (Gg := hG.goose_globalGS) (regR K.g.st) (clientAddrs.getD c go!"") ∗
        ⌜ρ.bud (clientAddrs.getD c go!"") = some N ∧ receiptBound GF ≤ 2 ^ 64⌝ }}
      (App (Val (@! Client)) (Val #(W64 (c : Int))))
    {{ RET #(); False }}

end spec

end Perennial
