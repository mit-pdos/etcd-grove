/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__emit.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

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

end proof

end AntHarness
end EtcdGrove
end Perennial
