/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/NewObserver.lean (241f27e).
-/
/-
The proof of `raft.NewObserver` (with no channel, not blocking): a fresh `Observer` whose
`channel`, `blocking`, `filter` and `id` fields are made read-only; the id comes from
`nextObserverID`'s atomic counter (its invariant is in `isPkgInit`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.NewObserver
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.NewObserver.wp_proof :
    github_com.hashicorp.raft.NewObserver.spec (GF := GF) (hG := hG) := by
  intro γ i r fl
  wp_start as #Hfl
  ihave #Hg := pkgGlobals_of_init $$ Hpkg
  unfold pkgGlobals
  icases Hg with ⟨-, -, -, -, #Hinv⟩
  iapply wp_fupd
  wp_auto
  wp_apply_core sync.atomic.wp_AddUint64 _ (W64 1) $$ [] [-]
  · iPkgInit
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%n, Hn⟩
  iexists n
  iframe Hn
  iintro Hn
  imod Hmask with -
  imod Hclose $$ [Hn] with -
  · inext; iexists _; iframe
  imodintro
  wp_auto
  iStructNamed «$r0»
  ipersist channel
  ipersist blocking
  ipersist filter
  ipersist id
  imodintro
  iapply HΦ
  unfold obsOk
  iexists fl, _
  iframe #

end proof

end Perennial
