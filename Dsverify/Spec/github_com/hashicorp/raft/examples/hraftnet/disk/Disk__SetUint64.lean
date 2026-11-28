/-
(hraft_robust R3) The spec of `disk.(*Disk).SetUint64` (`disk.go`): `ints[key] := v`, durably, the window resource lent until the commit.
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

/-- `d.SetUint64(key, v)`: committed (durable) at the client's atomic update, which gets `Ws (.setU kb v)` back. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.SetUint64.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (key : GoSlice) (kb : List w8) (v : w64),
  ⊢ ∀ Φ : val → IProp GF,
    isDisk g d Wl Ws Wf -∗ key ↦*□ kb -∗ Ws (.setU kb v) -∗
    (Ws (.setU kb v) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ st, diskOwnS g st ∗
      (diskOwnS g { st with ints := st.ints.insert kb v } ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
    WP (App (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"SetUint64")) (Val #key)) (Val #v)) {{ Φ }}

end sec

end Perennial
