/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.snapsM()` (B 214-230, `InMem.snapsM`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__snapsM
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem inMem.snapsM.wp_proof
    (wp_has : Event.has.spec (GF := GF) (hG := hG)) :
    inMem.snapsM.spec (GF := GF) (hG := hG) := by
  intro gx x
  wp_start as #Hx
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FSnap : val) = #fSnap from rfl]
  wp_apply wp_has gx.ev' x.ev fSnap x.ev.snap.isSome $$ [He]
  · iframe He; ipureintro; exact Event.hasF_Snap _
  try wp_auto
  rw [show x.ev.snap.isSome = x.snapsM from rfl]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
