/-
The definitions, specs and lemmas of `OrchProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ConfDefs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitProofDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__RemoteAddr

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Masks, the model's decoder -/

theorem pendN_vsr : (↑pendN : CoPset) ⊆ ⊤ \ Impl.vsrE := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  unfold Impl.vsrE
  intro h
  exact ndot_ne_disjoint nroot (show "remote" ≠ "vsr" by decide) p ⟨h1, h⟩

theorem lintestN_vsr :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (Impl.vsrE ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · unfold Impl.vsrE
    intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "vsr" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- **porcupine's model is the pending-writes model** of the far side's store `kvR g`. -/
theorem kvS_pendDec (g : Impl.GN) :
    PendDec (kvR (GF := GF) (Gg := hG.goose_globalGS) g) (kvS (GF := GF)) :=
  .ofTotal (fun _ => rfl) {
  init := rfl
  ok s i o := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i (.ok o))
  err s i := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i .err)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, .ok o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, .err, rfl⟩
  noObs _ := rfl }

theorem kvR_encOut_inj (g : Impl.GN) (o o' : KOut)
    (h : (kvR (GF := GF) (Gg := hG.goose_globalGS) g).encOut
        ((kvR (GF := GF) (Gg := hG.goose_globalGS) g).ov o) =
      (kvR (GF := GF) (Gg := hG.goose_globalGS) g).encOut
        ((kvR (GF := GF) (Gg := hG.goose_globalGS) g).ov o')) :
    o = o' :=
  encOut_inj o o' h

theorem pendCtx_kvS (g : Impl.GN) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (kvR g) (kvS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (kvR g) (kvS (GF := GF)) γp := rfl

theorem pendLib_kvS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (kvS (GF := GF)) γp (kvS (GF := GF)).M.init := rfl

/-- `ClientAddrs()` returns a new slice of the client machines' addresses. -/
theorem wp_ClientAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.ClientAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* clientAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) clientAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `attempt()`: some duration. -/
theorem wp_attempt :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.attempt)) (Val #()))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-- `Orch()`: the orchestrator; it returns (porcupine accepts the history). Its share of the
start: the size token, the system's invariant and the configuration addresses' protocols (to fix
and send the configuration), and remote's: the client machines' addresses serve `kvR γ.gn`, the
slot map, the pending library's invariant and state. -/
abbrev Orch.spec : Prop :=
  ∀ (γ : Names) (γp : PendNames), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ sysInv (G := hG.goose_globalGS) γ ∗ sizeTok γ ∗
      confProtos (G := hG.goose_globalGS) γ ∗
      ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
      pendCtx (Gg := hG.goose_globalGS) (kvR γ.gn) (kvS0 (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init ∗
      [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 24 }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Orch)) (Val #()))
  {{ RET #(); True }}

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
