/-
(hraft_robust R3) The proof of `disk.(*Sink).Write` (`snap.go`), as `examples/snapstore`'s.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Sink__Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Write.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Write.spec (GF := GF) (hG := hG) :=
  fun k p dq bs c => by
  wp_start as ⟨Hst, Hp⟩
  simp only [sinkSt]
  icases Hst with ⟨%dsl, Hdata, Hsl, Hcap, Hclosed, Hsize⟩
  wp_auto
  wp_apply wp_slice_append dsl bs p c dq $$ [$Hsl $Hcap $Hp] as %dsl' ⟨Hsl, Hcap, Hp⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hp
  have Hl : p.len = W64 (c.length : Int) := by word
  rw [Hl]
  iapply HΦ
  iframe Hp
  iexists dsl'
  iframe

end proof

end Perennial
