/-
(hraft_robust R3) The spec of `disk.(*Disk).GetUint64` (`disk.go`): the key's value or `0`, atomically.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Inv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

/-- `d.GetUint64(key)`: atomically, the key's value, `0` if none. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetUint64.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (key : GoSlice) (kb : List w8),
  ⊢ ∀ Φ : val → IProp GF,
    isDisk g d Wl Ws Wf -∗ key ↦*□ kb -∗
    (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ st, diskOwnS g st ∗
      (diskOwnS g st ={∅,⊤ \ ↑storeN}=∗ Φ (PairV #((st.ints.lookup kb).getD (W64 0)) #interface.nil))) -∗
    WP (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"GetUint64")) (Val #key)) {{ Φ }}

end sec

end Perennial
