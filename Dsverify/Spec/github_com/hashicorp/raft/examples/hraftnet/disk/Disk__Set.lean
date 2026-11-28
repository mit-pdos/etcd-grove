/-
(hraft_robust R3) The spec of `disk.(*Disk).Set` (`disk.go`): `bytes[key] := val`, durably, the window resource lent until the commit.
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

/-- `d.Set(key, val)`: committed (durable) at the client's atomic update, which gets `Ws (.set kb vb)` back. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.Set.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (key vs : GoSlice) (kb vb : List w8),
  ⊢ ∀ Φ : val → IProp GF,
    isDisk g d Wl Ws Wf -∗ key ↦*□ kb -∗ vs ↦*□ vb -∗ Ws (.set kb vb) -∗
    (Ws (.set kb vb) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ st, diskOwnS g st ∗
      (diskOwnS g { st with bytes := st.bytes.insert kb vb } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
    WP (App (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"Set")) (Val #key)) (Val #vs)) {{ Φ }}

end sec

end Perennial
