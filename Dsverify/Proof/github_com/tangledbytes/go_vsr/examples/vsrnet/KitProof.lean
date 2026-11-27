/-
The proofs of the vr kit's functions (`kit.go`, notes/dsv-vr.md), as paxos's
`examples/paxosnet/KitProof.lean`: so far `Gen` (with `digit`, `digits`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.CodecProofDefs
public import Perennial.Proof.github_com.goose_lang.primitive.RandomUint64
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitProofDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost.Impl

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply github_com.goose_lang.primitive.RandomUint64.wp_proof as %r -
  wp_apply wp_digit as %d %Hd
  wp_if_destruct
  · wp_apply wp_digit as %d2 %Hd2
    wp_apply wp_digits as %ds %Hds
    iapply HΦ
    imodintro
    ipureintro
    exact ⟨⟨_, kin_put d d2 ds Hd Hd2 Hds⟩, rfl⟩
  · iapply HΦ
    imodintro
    ipureintro
    exact ⟨⟨_, kin_get d Hd⟩, rfl⟩

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
