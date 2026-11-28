/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/BootstrapCluster.lean (241f27e).
-/
/-
`raft.BootstrapCluster`'s spec (raft-internal interface, notes/raft-iface.md). On empty stores: stores the genesis entry (the configuration entry of the servers `ss`, term 1, index 1; the log store's write takes a fraction of the durable-prefix view at 0) and current term 1; returns nil.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `BootstrapCluster`: On empty stores: stores the genesis entry (the configuration entry of the servers `ss`, term 1, index 1) and current term 1; returns nil. (Stage 3: the log store over a partial map, `LogAbs`; its writes no longer take the durable-prefix view and `llogIdx`; the snapshot store is `isSnapStore`, empty.) (hraft_robust R5) Pre-model writes: the two writes' window
resources (`Ws` of the `SetUint64(CurrentTerm, 1)`, `Wl` of the `StoreLog` of the genesis at 1) are the caller's,
lent to the stores and given back at their commits (the kit's families decide what they are before the
generation is armed). -/
abbrev github_com.hashicorp.raft.BootstrapCluster.spec : Prop :=
  ∀ (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Qc : SnapshotMeta → List w8 → IProp GF) (cp : Loc) (c : Config) (logsI stableI snapsI : GoInterfaceOk) (trans : GoInterface)
    (cfgv : Configuration) (ss : List Server) (dq : DFrac) (γ : GNames) (i : SID)
    (ownL : LogAbs → IProp GF) (ownS : StableAbs → IProp GF) (ownSS : SnapLatest → IProp GF)
    (eof : GoInterface) (sst : StableAbs) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ cp ↦ c ∗ ⌜cfgOk c i⌝ ∗
     isLogStore logsI ownL Wl ∗ isStableStore stableI ownS Ws ∗ isSnapStore snapsI ownSS eof Qc ∗
     cfgv.Servers' ↦*{dq} ss ∗ ⌜srvsOk γ ss ∧ γ.srvs.Nodup ∧ γ.srvs ≠ []⌝ ∗
     ownL LogAbs.empty ∗ ownS sst ∗ ⌜(sst.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0) = W64 0⌝ ∗
     ownSS none ∗ Ws (.setU (go!"CurrentTerm" : List w8) (W64 1)) ∗ Wl (.store 1 [genesisOf ss]) ∗ rtok tid }}
    (App (App (App (App (App (App (Val (@! github_com.hashicorp.raft.BootstrapCluster)) (Val #cp)) (Val #(GoInterface.ok logsI))) (Val #(GoInterface.ok stableI))) (Val #(GoInterface.ok snapsI))) (Val #trans)) (Val #cfgv))
  {{ RET #interface.nil; cp ↦ c ∗ cfgv.Servers' ↦*{dq} ss ∗
      ownL (LogAbs.empty.store 1 [genesisOf ss]) ∗
      ownS { sst with ints := sst.ints.insert (go!"CurrentTerm" : List w8) (W64 1) } ∗
      ownSS none ∗ Ws (.setU (go!"CurrentTerm" : List w8) (W64 1)) ∗ Wl (.store 1 [genesisOf ss]) ∗ rtok tid }}

end spec

end Perennial
