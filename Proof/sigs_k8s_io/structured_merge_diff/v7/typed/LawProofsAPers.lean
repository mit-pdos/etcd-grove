/-
**Proofs of `typed`'s representation laws** (`WalkerLaws.lean`), part A (continued): a finished
comparison handed out (`ownCmp_persist`, over the root law `ownSet_persist`) and truncating a
walker's path (`ownPath_truncate`, the merging walker's `ownPath_pop`).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Sets
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
import all Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem ownCmp_persist_law_holds : ownCmp_persist.law (GF := GF) := fun c C => by
  unfold ownCmp isComparison
  iintro ⟨%r, %m, %a, Hc, Hr, Hm, Ha⟩
  imod (typedPointsto_dfractional _ _).dfractional_persist _ $$ Hc with #Hc
  imod ownSet_persist_law_holds r _ $$ Hr with #Hr
  imod ownSet_persist_law_holds m _ $$ Hm with #Hm
  imod ownSet_persist_law_holds a _ $$ Ha with #Ha
  imodintro
  iexists r, m, a
  iframe #

theorem ownPath_truncate_law_holds : ownPath_truncate.law (GF := GF) := fun s p pe =>
  ownPath_pop s p pe

end laws

end smd
end EtcdGrove
end Perennial
