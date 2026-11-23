/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/gob/SetCodec.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `Spec/gob/SetCodec.lean` (the run's package state for gob: `hst`).
-/
module

public import Dsverify.Proof.encoding.gob.Base
public import Dsverify.Spec.encoding.gob.SetCodec

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [pkgState : github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [net.rpc.RpcKit] [net.rpc.RpcCodec GF]

theorem SetCodec.wp_proof (hst : pkgState.gob = isInit) : SetCodec.spec (GF := GF) := by
  intro c
  wp_start as ⟨%Hc, #Hfns⟩
  ihave ⟨-, -, #Hsync⟩ := deps_of_pkg $$ Hpkg
  ihave #Hi := isInit_access hst $$ Hpkg
  iNamed Hi
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $HcodecMu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (globalAddr encoding.gob.codec ↦ (null : Loc) ∨ codecSet : IProp GF) $$ [Hinv]
  · unfold codecInv; iexact Hinv
  icases Hinv with (Hnull | #Hset)
  · wp_auto
    ipersist Hnull
    wp_apply sync.Mutex.Unlock.wp_proof (globalAddr encoding.gob.codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
    · unfold codecInv codecSet; iright; iexists c; iframe Hnull Hfns; ipureintro; exact Hc
    iapply HΦ
    unfold codecSet
    iexists c; iframe Hnull Hfns; ipureintro; exact Hc
  · unfold codecSet
    icases Hset with ⟨%c', %Hc', #Hcp, #Hfns'⟩
    wp_auto
    rw [decide_eq_false Hc']
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof (globalAddr encoding.gob.codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
    · unfold codecInv codecSet; iright; iexists c'; iframe Hcp Hfns'; ipureintro; exact Hc'
    iapply HΦ
    iexists c'; iframe Hcp Hfns'; ipureintro; exact Hc'

end proof

end Perennial.encoding.gob
