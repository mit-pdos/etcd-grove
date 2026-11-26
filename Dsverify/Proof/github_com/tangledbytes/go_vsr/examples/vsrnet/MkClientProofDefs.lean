/-
The definitions, specs and lemmas of `MkClientProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.OpProofDefs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitLib
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS
attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- `replicas(addrs, conf)`: the configuration's replicas' addresses, server machines `1 .. N`. -/
theorem wp_replicas (sl : GoSlice) (n h r : Nat) (hc : ConfOk n h r) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ VsrWire.addrs }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.replicas)) (Val #sl))
        (Val #(confOf n h r)))
    {{ (ms : GoSlice), RET #ms; ms ↦*□ subslice 7 (7 + n) VsrWire.addrs }} := by
  wp_start as #Hsl
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
  have hn : n ≤ 5 := by rcases hc.1 with rfl | rfl <;> decide
  have h12 : VsrWire.addrs.length = 12 := rfl
  have hb : 0 ≤ sint.Z (W64 6 + W64 1) ∧
      sint.Z (W64 6 + W64 1) ≤ sint.Z (W64 6 + W64 1 + W64 (n : Int)) ∧
      sint.Z (W64 6 + W64 1 + W64 (n : Int)) ≤ sint.Z sl.len := by
    rw [h12] at Hlen
    refine ⟨by word, by word, by word⟩
  rw [ite_eq_left ⟨hb.1, hb.2.1, Int.le_trans hb.2.2 Hwf.2⟩]
  wp_auto
  iapply HΦ
  icases (ownSlice_slice (W64 6 + W64 1) (W64 6 + W64 1 + W64 (n : Int)) sl DFrac.discard
    VsrWire.addrs hb).1 $$ Hsl with ⟨-, Hm, -⟩
  have e1 : sint.nat (W64 6 + W64 1) = 7 := by word
  have e2 : sint.nat (W64 6 + W64 1 + W64 (n : Int)) = 7 + n := by word
  rw [e1, e2]
  iexact Hm

/-- `mkClient(addrs, conf, c)`: client `c`'s system, its counter at 1. -/
abbrev mkClient.spec : Prop :=
  ∀ (γ : Names) (c : Nat) (sl : GoSlice) (cf : Conf), c < 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ VsrWire.addrs ∗
      confOk (G := hG.goose_globalGS) γ cf ∗ pkg.network.netProtos γ ∗
      sysInv (G := hG.goose_globalGS) γ ∗ regInv (G := hG.goose_globalGS) γ ∗
      nextReq (G := hG.goose_globalGS) γ (c + 1) 1 ∗
      encoding.json.kitCodecOk vsrnet.scanF ∗ encoding.json.codecFresh (GF := GF) }}
    (App (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.mkClient)) (Val #sl))
      (Val #cf)) (Val #(W64 (c : Int))))
  {{ (x : Loc), RET #x; sysRes γ c (interface.mkOk (go.GoType.PointerType Sys.ty) #x) 1 }}

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
