/-
The vr kit's orchestrator (`kit.go`'s `Orch`, notes/dsv-vr.md): `Configure(CfgAddrs(), choose())`
(the orchestrator fixes the number of replicas of its chosen configuration with its size token,
`conf_size`, before it sends it), then `remote.Check(Model(), ClientAddrs(), Codec(), Gen, Ops,
attempt())` against the far side's store `kvR γ.gn` and the map's porcupine model `kvS`. Ported
from dsverify-lab `examples/vr/proof/VsrProof/Top/Orch.lean` (its `RunRemote`, recorder and
porcupine axiom replaced by remote's `Check`, as paxos's kit `Orch.wp_proof`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Conf
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitProof
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__RemoteAddr

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

/-- The client machines' addresses (`ClientAddrs()`), client `c`'s at `c`. -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7541", go!"127.0.0.1:7542", go!"127.0.0.1:7543", go!"127.0.0.1:7544",
   go!"127.0.0.1:7545", go!"127.0.0.1:7546"]

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
    PendDec (kvR (GF := GF) (Gg := hG.goose_globalGS) g) (kvS (GF := GF)) where
  init := rfl
  ok s i o := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i (.ok o))
  err s i := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i .err)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, .ok o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, .err, rfl⟩
  noObs _ := rfl

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

theorem Orch.wp_proof (conn_readerOk : connReaderOk (GF := GF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := VsrModel.Store) (I := KIn) (O := KOut)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γ γp hrb
  rw [pendCtx_kvS, pendLib_kvS]
  wp_start as ⟨#Hsys, Hsize, #Hcp, #Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  -- the configuration
  wp_apply CfgAddrs.wp_proof as %cfgs Hcfgs
  wp_apply wp_choose as %n %h %r %Hc
  iapply fupd_wp
  imod conf_size γ Hc $$ Hsys Hsize with #Hf
  imodintro
  wp_apply (Configure.wp_proof net.Dial.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof conn_readerOk γ cfgs (DFrac.own 1) n h r Hc)
    $$ [Hcfgs] as -
  · iframe; iframe #
  -- the check
  wp_apply Model.wp_proof as %m #Hm
  wp_apply wp_ClientAddrs as %addrs Haddrs
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (Codec.wp_proof γ.gn) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 6 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  wp_apply wp_Check (kvR γ.gn) kvS γp m addrs clientAddrs cd _ (W64 8) d pendN_vsr lintestN_vsr
    (kvS_pendDec γ.gn) (kvR_encOut_inj γ.gn) (fun st => kvR_timeless γ.gn st) hrb
    (by rw [hlen']; decide) (by decide) (by rw [hlen']; decide) 24 (by decide) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    iapply (show ⊢ EtcdGrove.lintest.genSpec (GF := GF)
        (functions github_com.tangledbytes.go_vsr.examples.vsrnet.Gen [])
        (fun x => iprop(∃ i, ⌜x = (kvR (Gg := hG.goose_globalGS) γ.gn).iv i⌝)) from Gen.wp_proof)
  iapply HΦ
  itrivial

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
