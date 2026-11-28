/-
(hraft_robust R3) The spec of `disk.(*Disk).DeleteRange` (`disk.go`): the entries at `mn..mx` deleted, durably, the window resource lent until the commit; `hi` the largest index left.
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

/-- `d.DeleteRange(mn, mx)`: committed (durable) at the client's atomic update, which gets
`Wl (.del main mn mx)` back (`main` is the client's tag); `LastIndex` afterwards is the largest index left. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.DeleteRange.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (main : Bool) (mn mx : w64),
  ⊢ ∀ Φ : val → IProp GF,
    isDisk g d Wl Ws Wf -∗ Wl (.del main (uint.nat mn) (uint.nat mx)) -∗
    (Wl (.del main (uint.nat mn) (uint.nat mx)) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗
      (∀ hi' : w64, diskOwnL g (A.delete (uint.nat mn) (uint.nat mx) hi') ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
    WP (App (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"DeleteRange")) (Val #mn)) (Val #mx)) {{ Φ }}

end sec

end Perennial
