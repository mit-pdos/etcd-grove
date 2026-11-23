/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/MsgSetQ.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumMaps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArith

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.mset
open replica.quorum

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics]

def quorumIs (q : GoInterface) (sz : Nat) (mem : w32 → Prop) : IProp netDistGF :=
  iprop(⌜sz < 2 ^ 62⌝ ∗
    ((⌜(q = interface.mkOk replica.Majority.ty #(W64 sz) ∨
        q = interface.mkOk replica.ThreeQuarters.ty #(W64 sz)) ∧ ∀ k, mem k⌝) ∨
     ∃ (ql : Loc) (s : List Nat), ⌜q = interface.mkOk replica.Quorum.ty #ql ∧ sz = s.length ∧
        s.Nodup ∧ (∀ x ∈ s, x < 2 ^ 31) ∧ ∀ k, mem k ↔ k ∈ s.map w32n⌝ ∗
        qOwn ql DFrac.discard s))

instance quorumIs_persistent (q : GoInterface) (sz : Nat) (mem : w32 → Prop) :
    Persistent (quorumIs q sz mem) := by unfold quorumIs; infer_instance
end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]

theorem quorumIs_ok (q : GoInterface) (sz : Nat) (mem : w32 → Prop) :
    quorumIs q sz mem ⊢ ⌜∃ i, q = GoInterface.ok i⌝ := by
  unfold quorumIs
  iintro ⟨%Hsz, (⟨%Hq, -⟩ | ⟨%ql, %s, ⟨%Hq, -⟩, -⟩)⟩
  · ipureintro; rcases Hq with h | h <;> exact ⟨_, h⟩
  · ipureintro; exact ⟨_, Hq⟩

theorem quorumIs_sz (q : GoInterface) (sz : Nat) (mem : w32 → Prop) :
    quorumIs q sz mem ⊢ ⌜sz < 2 ^ 62⌝ := by
  unfold quorumIs
  iintro ⟨%Hsz, -⟩
  ipureintro; exact Hsz

theorem wp_qSize (i : GoInterfaceOk) (sz : Nat) (mem : w32 → Prop) :
  {{ quorumIs (GoInterface.ok i) sz mem }}
    (App (Val #(methods i.ty go!"Size" i.v)) (Val #()))
  {{ RET #(W64 sz); True }} := by
  unfold quorumIs
  iintro %Φ ⟨%Hsz, Hq⟩ HΦ
  icases Hq with (⟨%Hq, -⟩ | ⟨%ql, %s, ⟨%Hq, %Hs, %Hnd, %Hlt, -⟩, #Hql⟩)
  · rcases Hq with h | h <;> cases h
    · wp_apply replica.Majority.Size.wp_proof
      iapply HΦ; itrivial
    · wp_apply replica.ThreeQuarters.Size.wp_proof
      iapply HΦ; itrivial
  · cases Hq; subst Hs
    wp_apply replica.Quorum.Size.wp_proof $$ [$Hql] as -
    · ipureintro; exact ⟨Hnd, Hlt⟩
    iapply HΦ; itrivial

theorem wp_qContains (i : GoInterfaceOk) (sz : Nat) (mem : w32 → Prop) (r : w32) :
  {{ quorumIs (GoInterface.ok i) sz mem }}
    (App (Val #(methods i.ty go!"Contains" i.v)) (Val #r))
  {{ (b : Bool), RET #b; ⌜b = true → mem r⌝ }} := by
  unfold quorumIs
  iintro %Φ ⟨%Hsz, Hq⟩ HΦ
  icases Hq with (⟨%Hq, %Hm⟩ | ⟨%ql, %s, ⟨%Hq, %Hs, %Hnd, %Hlt, %Hm⟩, #Hql⟩)
  · rcases Hq with h | h <;> cases h
    · wp_apply replica.Majority.Contains.wp_proof
      iapply HΦ; ipureintro; intro _; exact Hm r
    · wp_apply replica.ThreeQuarters.Contains.wp_proof
      iapply HΦ; ipureintro; intro _; exact Hm r
  · cases Hq
    wp_apply replica.Quorum.Contains.wp_proof $$ [$Hql] as -
    iapply HΦ; ipureintro; intro h; exact (Hm r).2 (by simpa using h)

end specs
end replica.mset
end Perennial.github_com.imdea_software.swiftpaxos
