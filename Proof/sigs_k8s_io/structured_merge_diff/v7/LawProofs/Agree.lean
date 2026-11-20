/-
**The root laws' agreement part, proved** (`v7/Laws.lean`, "Agreement"): `isIface_agree`, from
`value`'s `isIface_agree'` (`value/LawProofsAgree.lean`).

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsAgree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isIface_agree_law_holds : isIface_agree.law (GF := GF) := isIface_agree'

end laws

end smd
end EtcdGrove
end Perennial
