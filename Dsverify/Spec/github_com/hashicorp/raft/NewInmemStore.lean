/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/NewInmemStore.lean (241f27e).
-/
/-
`raft.NewInmemStore`'s spec: a fresh store, with empty log contents and empty stable contents
(the two client views) and the persistent handle. Its reader tokens go to a thread pool, which
needs the bound `threadBound GF ≤ 2^28` (a quarter thread pool, `HrVerify/Proof/Threads/QPool.lean`, D15). The handle records the package fact
`errLogNotFoundOk` (what `GetLog`'s miss returns), taken here.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.InmemStoreBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft in
/-- `NewInmemStore()` returns a fresh store with empty views. -/
abbrev github_com.hashicorp.raft.NewInmemStore.spec : Prop :=
  ThreadBoundLe GF (2 ^ 28) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ errLogNotFoundOk }}
    (App (Val (@! github_com.hashicorp.raft.NewInmemStore)) (Val #()))
  {{ (i : Loc), RET #i; ∃ γs : InmemNames, isInmemStore γs i ∗ inmemLogs γs LogAbs.empty ∗
      kvView γs ⟨∅, ∅⟩ }}

end spec

end Perennial
