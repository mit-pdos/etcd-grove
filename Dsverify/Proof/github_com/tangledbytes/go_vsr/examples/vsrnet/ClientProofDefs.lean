/-
The definitions, specs and lemmas of `ClientProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.MkClientProofDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

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
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- Client `c`'s system at its address `a`: its request counter `n` is at most one more than the
calls to `a` it served (`budUsed a m`). -/
def sysTok (γ : Names) (c : Nat) (a : GoString) (sys : GoInterface) : IProp GF :=
  iprop(∃ n m : Nat, ⌜n ≤ m + 1⌝ ∗ sysRes γ c sys n ∗ budUsed (Gg := hG.goose_globalGS) a m)

/-- `Op` meets remote's `svcOp` over `sysTok`, at an address whose budget is 24 calls. -/
theorem Op_svcOp (wp_Op : Op.spec (GF := GF) (hG := hG)) (γ : Names) (c : Nat) (hc : c < 6)
    (a : GoString) (hbud : ρ.bud a = some 24) :
    isPkgInit (PROP := IProp GF) kpkg ⊢
      svcOp (RBase.svc (Gg := hG.goose_globalGS) (kvR γ.gn)) a (sysTok γ c a)
        (functions github_com.tangledbytes.go_vsr.examples.vsrnet.Op []) := by
  unfold svcOp
  iintro #Hpkg %sys %i %Ψ
  iintro !> %Φ ⟨Htok, HU, Hu⟩ HΦ
  unfold sysTok
  icases Htok with ⟨%n, %m, %hnm, Hres, Hused⟩
  ihave ⟨Hused, %Hle⟩ := budUsed_add (Gg := hG.goose_globalGS) a m $$ Hused Hu
  have hm : m + 1 ≤ 24 := Hle 24 hbud
  iapply (wp_Op γ c n sys i Ψ hc (by omega)) $$ [Hres HU]
  · isplitr
    · iexact Hpkg
    isplitl [Hres]
    · iexact Hres
    iexact HU
  iintro !> %v ⟨%n', %hn', Hres, Hv⟩
  iapply HΦ
  isplitl [Hres Hused]
  · iexists n', m + 1
    iframe
    ipureintro; omega
  icases Hv with (⟨%o, %Ho, HΨ⟩ | %Hv)
  · ileft; iexists o; iframe; ipureintro; exact Ho
  · iright; ipureintro; exact Hv

/-- `Client(c)`: client machine `c`; it never returns. Its share of the start: the configuration
addresses' and go-vsr addresses' protocols, the ghost layer's invariants, client `c + 1`'s request
counter, and its address serving the far side's store. -/
abbrev Client.spec : Prop :=
  ∀ (γ : Names) (c : Nat), c < 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ confProtos (G := hG.goose_globalGS) γ ∗
      pkg.network.netProtos γ ∗ sysInv (G := hG.goose_globalGS) γ ∗
      regInv (G := hG.goose_globalGS) γ ∗ nextReq (G := hG.goose_globalGS) γ (c + 1) 1 ∗
      remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD c []) ∗
      ⌜ρ.bud (clientAddrs.getD c []) = some 24⌝ }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Client)) (Val #(W64 (c : Int))))
  {{ RET #(); False }}

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
