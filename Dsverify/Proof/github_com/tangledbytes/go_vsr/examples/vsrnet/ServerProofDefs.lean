/-
The definitions, specs and lemmas of `ServerProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitLib
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.vsrkv
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Perennial.Spec.time.Sleep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec

/-! ## The server machine's share -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Server machine `id`'s share of the start (the lab's `serverRes`; see the file header). -/
def srvShare (γ : Names) (id : Nat) : IProp GF :=
  iprop(VsrWire.protos γ ∗ confProtos γ ∗ sysInv γ ∗ regInv γ ∗ repOwn γ (id - 1) VsrModel.initRep)

instance srv_protos_persistent (γ : Names) : Persistent (VsrWire.protos (G := G) γ) := by
  unfold VsrWire.protos; infer_instance

end defs

section defs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [π : NetProtoGS] [encoding.json.DecoderRep GF]

end defs2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF] [encoding.json.EncoderRep GF]
variable [vw_sem : github_com.tangledbytes.go_vsr.examples.vsrwire.Assumptions]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem addrs_len : VsrWire.addrs.length = 12 := rfl

/-- `replicas(addrs, conf)`: `addrs[7 : 7 + N]`. -/
theorem wp_replicasS (sl : GoSlice) (n h r : Nat) (hn : 7 + n ≤ sint.Z sl.cap) (hn5 : n ≤ 5) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.replicas)) (Val #sl))
        (Val #(confOf n h r)))
    {{ RET #(slice.slice sl GoString (W64 7) (W64 7 + W64 (n : Int))); True }} := by
  wp_start as -
  wp_auto
  rw [show (W64 6 + W64 1 : w64) = W64 7 from rfl]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  wp_auto
  iapply HΦ; itrivial

/-- `runReplica(id, addrs, conf)`, `id = i + 1`: replica `i < N` of the configuration at server
machine `id`'s address `addrs[NC + id]`, the configuration's replicas its members; the event loop
forever. -/
abbrev runReplica.spec : Prop :=
  ∀ (γ : Names) (i : Nat) (n h r : Nat), ConfOk n h r → i < n → ∀ (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ VsrWire.addrs ∗
      VsrWire.protos (G := hG.goose_globalGS) γ ∗ sysInv (G := hG.goose_globalGS) γ ∗
      regInv (G := hG.goose_globalGS) γ ∗ repOwn (G := hG.goose_globalGS) γ i VsrModel.initRep ∗
      fact (G := hG.goose_globalGS) γ (.size n) ∗ encoding.json.codecFresh (GF := GF) }}
    (App (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.runReplica))
      (Val #(W64 ((i + 1 : Nat) : Int)))) (Val #sl)) (Val #(confOf n h r)))
  {{ RET #(); False }}

/-- **`Server(id)`**: server machine `id` (`1 ≤ id ≤ 5`, machine `NC + id`), given the start's
share (`srvShare`) and encoding/json's fresh registry (`codecFresh`, from the machine's boot);
it never returns. -/
abbrev Server.spec : Prop :=
  ∀ (γ : Names) (id : w64), 1 ≤ uint.nat id ∧ uint.nat id ≤ 5 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗
      srvShare (G := hG.goose_globalGS) γ (uint.nat id) ∗ encoding.json.codecFresh (GF := GF) }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Server)) (Val #id))
  {{ RET #(); False }}

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
