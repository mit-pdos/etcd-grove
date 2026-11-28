/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__emit.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.SpecsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReportB2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

theorem ite_true_ent_b2 {GF : BundledGFunctors} {P Q : IProp GF} {b : Bool} (h : b = true) :
    (if b then P else Q) ⊢ P := by
  subst h; exact .rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.emit.wp_proof (wp_record : Recorder.record.spec (GF := GF) (hG := hG)) :
    node.emit.spec (GF := GF) (hG := hG) := by
  intro c γ n j p ev Qr
  wp_start as ⟨#Hc, #Hn, Hok, Hev, Hrep⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  iunfold emitOk at Hok
  icases Hok with ⟨Hdead, Hfuse⟩
  iunfold eventOwn at Hev
  icases Hev with ⟨%g, Hp, %Hg, He, Hv, Ho, Hm, Hcs⟩
  simp only [reports]
  icases Hrep with ⟨Hw, Hau⟩
  wp_auto
  ipersist Hp
  ihave Hev : AntCheck.eventRO p (atNode (AntSim.nameOf (AntSim.nodeId j)) ev) $$ [He Hv Ho Hm Hcs]
  · iunfold AntCheck.eventRO
    iexists _
    iframe Hp
    iframe
    ipureintro
    simp only [atNode]
    exact ⟨Hg.1, by trivial, Hg.2.2⟩
  wp_bind (App (Val #(methods _ _ #r)) (Val #p))
  iapply (wp_record γ.strm r p (atNode (AntSim.nameOf (AntSim.nodeId j)) ev) Qr) $$ [$Hpkg $Hrec $Hev $Hw $Hau]
  inext
  iintro HQ
  try wp_auto
  iapply HΦ
  iframe
  iunfold emitOk
  iframe

/-- **`node.emit.specB2`** (#33 parity B2; staged beside B1's `wp_proof` until B2's spec replaces it):
`emit` by the kill fields (`emitStep`). -/
theorem node.emit.wp_proofB2 (wp_record : Recorder.record.spec (GF := GF) (hG := hG)) :
    node.emit.specB2 (GF := GF) (hG := hG) := by
  intro c γ n j p ev Qr dead fuse
  wp_start as ⟨#Hc, #Hn, Hk, Hev, Hrep⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, #Hr, #Hrec, -⟩
  ihave #Hn' := Hn
  iunfold nodeROB2 at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, #Hid, #Hname, -⟩
  iunfold killOwn at Hk
  icases Hk with ⟨Hdead, Hfuse⟩
  have h0 : uint.Z (W64 0) = 0 := rfl
  cases dead
  · by_cases hz : uint.Z fuse > 0
    · have hz' : uint.Z (W64 0) < uint.Z fuse := by omega
      by_cases h1 : fuse - W64 1 = W64 0
      · -- the fuse burns out: killed, nothing recorded
        have he : emitStep false fuse = (false, true, W64 0) := by
          unfold emitStep; rw [if_neg Bool.false_ne_true, if_pos hz, if_pos h1]
        rw [he]
        wp_auto
        rw [decide_eq_true hz']
        wp_auto
        rw [h1]
        wp_auto
        iapply HΦ
        iunfold killOwn
        iframe
        isplitr
        · ipureintro; rfl
        rw [if_neg Bool.false_ne_true]
        iempintro
      · have he : emitStep false fuse = (true, false, fuse - W64 1) := by
          unfold emitStep; rw [if_neg Bool.false_ne_true, if_pos hz, if_neg h1]
        rw [he]
        ihave Hrep := ite_true_ent_b2 (rfl : (true, false, fuse - W64 1).1 = true) $$ Hrep
        iunfold eventOwn at Hev
        icases Hev with ⟨%g, Hp, %Hg, He, Hv, Ho, Hm, Hcs⟩
        simp only [reports]
        icases Hrep with ⟨Hw, Hau⟩
        wp_auto
        rw [decide_eq_true hz']
        wp_auto
        rw [decide_eq_false h1]
        wp_auto
        ipersist Hp
        ihave Hev : AntCheck.eventRO p (atNode (AntSim.nameOf (AntSim.nodeId j)) ev) $$ [He Hv Ho Hm Hcs]
        · iunfold AntCheck.eventRO
          iexists _
          iframe Hp
          iframe
          ipureintro
          simp only [atNode]
          exact ⟨Hg.1, by trivial, Hg.2.2⟩
        wp_bind (App (Val #(methods _ _ #r)) (Val #p))
        iapply (wp_record γ.strm r p (atNode (AntSim.nameOf (AntSim.nodeId j)) ev) Qr) $$ [$Hpkg $Hrec $Hev $Hw $Hau]
        inext
        iintro HQ
        try wp_auto
        iapply HΦ
        iunfold killOwn
        iframe
        isplitr
        · ipureintro; rfl
        rw [if_pos rfl]
        iexact HQ
    · have he : emitStep false fuse = (true, false, fuse) := by
        unfold emitStep; rw [if_neg Bool.false_ne_true, if_neg hz]
      rw [he]
      have hz' : ¬ uint.Z (W64 0) < uint.Z fuse := by omega
      ihave Hrep := ite_true_ent_b2 (rfl : (true, false, fuse).1 = true) $$ Hrep
      iunfold eventOwn at Hev
      icases Hev with ⟨%g, Hp, %Hg, He, Hv, Ho, Hm, Hcs⟩
      simp only [reports]
      icases Hrep with ⟨Hw, Hau⟩
      wp_auto
      rw [decide_eq_false hz']
      wp_auto
      ipersist Hp
      ihave Hev : AntCheck.eventRO p (atNode (AntSim.nameOf (AntSim.nodeId j)) ev) $$ [He Hv Ho Hm Hcs]
      · iunfold AntCheck.eventRO
        iexists _
        iframe Hp
        iframe
        ipureintro
        simp only [atNode]
        exact ⟨Hg.1, by trivial, Hg.2.2⟩
      wp_bind (App (Val #(methods _ _ #r)) (Val #p))
      iapply (wp_record γ.strm r p (atNode (AntSim.nameOf (AntSim.nodeId j)) ev) Qr) $$ [$Hpkg $Hrec $Hev $Hw $Hau]
      inext
      iintro HQ
      try wp_auto
      iapply HΦ
      iunfold killOwn
      iframe
      isplitr
      · ipureintro; rfl
      rw [if_pos rfl]
      iexact HQ
  · have he : emitStep true fuse = (false, true, fuse) := by unfold emitStep; rw [if_pos rfl]
    rw [he]
    wp_auto
    iapply HΦ
    iunfold killOwn
    iframe
    isplitr
    · ipureintro; rfl
    rw [if_neg Bool.false_ne_true]
    iempintro

end proof

end AntHarness
end EtcdGrove
end Perennial
