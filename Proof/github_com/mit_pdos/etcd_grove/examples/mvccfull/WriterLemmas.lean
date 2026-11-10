/-
mvccfull's writer: small Iris lemmas of the writer's part of an incarnation (F1 Prove). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RestoreLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterShares
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EndLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The bounds' facts hold at the writer's state and bounds** (the invariant's, which its halves
pin). -/
theorem incW_bndOk (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface)
    (qw : Qp) (σ : MvccState) (b : Bnd) :
    incW (GF := GF) ks γh i mp m ι kv qw σ b ={⊤}=∗
      incW ks γh i mp m ι kv qw σ b ∗ ⌜∃ Hl, bndOk ks σ b Hl⌝ := by
  haveI := isInc_persistent hpers
  iintro H
  iunfold incW at H
  icases H with ⟨#Hinc, Hret, Hσw, Hbw⟩
  imod bnd_acc hpers ks γh i mp m ι kv qw σ b $$ [Hret Hσw Hbw]
    with ⟨%Hl0, %Hok0, Hrl, Hrh, Hcl, Hch, Hcls⟩
  · iframe #; iframe
  imod Hcls $$ %b %Hok0 Hrl Hrh Hcl Hch with ⟨Hret, Hσw, Hbw⟩
  imodintro
  isplitl
  · iunfold incW; iframe #; iframe
  · ipureintro; exact ⟨Hl0, Hok0⟩

end lemmas

end mvccfull
end EtcdGrove
end Perennial
