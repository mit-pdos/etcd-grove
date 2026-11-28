/-
(hraft_robust R3) The spec of `disk.(*Disk).StoreLogs` (`disk.go`): the entries stored and the staged commit index written, durably, the window resource lent until the commit.
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

/-- `d.StoreLogs(sl)`: the entries `es` (pointed to by `ptrs`, at `first..`) inserted and `staged` written,
committed (durable) at the client's atomic update, which gets `Wl (.store first es)` back. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLogs.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF)
    (sl : GoSlice) (dq : DFrac) (ptrs : List Loc) (first : Nat) (es : RLog),
  ⊢ ∀ Φ : val → IProp GF,
    ⌜1 ≤ first ∧ ptrs.length = es.length ∧ first + es.length ≤ 2 ^ 64⌝ -∗
    isDisk g d Wl Ws Wf -∗ sl ↦*{dq} ptrs -∗
    ([∗list] k ↦ p ∈ ptrs, ∃ e, ⌜es[k]? = some e⌝ ∗ logPtr p (first + k) e) -∗
    Wl (.store first es) -∗
    (Wl (.store first es) -∗ |NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, diskOwnL g A ∗
      (diskOwnL g (A.store first es) ={∅,⊤ \ ↑storeN}=∗ (sl ↦*{dq} ptrs -∗ Φ #interface.nil))) -∗
    WP (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"StoreLogs")) (Val #sl)) {{ Φ }}

end sec

end Perennial
