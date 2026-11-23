/-
`vsrnet.mkClient` (notes/dsv-vr.md): client `c`'s go-vsr client (id `c + 1`) over a new `*TCP` at
its machine's address `Addrs()[1 + c]`, with the configuration's replicas (`replicas`), a `*Real`
time and the discarding logger (`logger`): the system's resource at counter 1 (`sysRes`). Ported
from dsverify-lab `examples/vr/proof/VsrProof/Top/NewProof.lean` (`wp_mkClient`), without the
client's invariant (`ClientDefs.lean`).

The library pieces `logger` needs, which no model gives yet (notes/dsv-vr.md, "Hypotheses"), are
the hypotheses `log.slog.New.spec` and `log.slog.DiscardHandler.load_spec`
(`Proof/replica/LibHyps.lean`; `wp_logger`, `KitLib.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.OpProof
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.KitLib
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results

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
      encoding.json.kitCodecOk vsrnet.scanF }}
    (App (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.mkClient)) (Val #sl))
      (Val #cf)) (Val #(W64 (c : Int))))
  {{ (x : Loc), RET #x; sysRes γ c (interface.mkOk (go.GoType.PointerType Sys.ty) #x) 1 }}

theorem mkClient.wp_proof (wp_NewTCP : pkg.network.NewTCP.spec (GF := GF) (hG := hG))
    (wp_New : log.slog.New.spec (GF := GF) (hG := hG))
    (wp_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG))
    (wp_RegisterJSON_set : RegisterJSON.codecSet_spec (GF := GF) (hG := hG)) :
    mkClient.spec (GF := GF) (hG := hG) := by
  intro γ c sl cf hc
  wp_start as ⟨#Hsl, #Hcf, #Hprotos, #HsysI, #HregI, Hnext, #Hkit⟩
  ihave #Hfd := kit_frameDecoderSet $$ []
  · iPkgInit
  unfold confOk
  icases Hcf with ⟨%n, %h, %r, ⟨%Hcf, %Hok⟩, #Hsize⟩
  subst Hcf
  ihave #Hnp : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network $$ []
  · iPkgInit
  ihave #Hcp : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client $$ []
  · iPkgInit
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.time $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_RegisterJSON_set as #Hcs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have h12 : VsrWire.addrs.length = 12 := rfl
  have hb : 0 ≤ sint.Z (W64 1 + W64 (c : Int)) ∧ sint.Z (W64 1 + W64 (c : Int)) < sint.Z sl.len := by
    rw [h12] at Hlen
    constructor <;> word
  rw [ite_eq_left hb]
  list_elem VsrWire.addrs (1 + c) as a
  wp_apply wp_load_slice_index sl (sint.Z (W64 1 + W64 (c : Int))) VsrWire.addrs DFrac.discard a
    hb.1 $$ [Hsl] as -
  · iframe #
    ipureintro
    rw [show (sint.Z (W64 1 + W64 (c : Int))).toNat = 1 + c by word]
    exact Ha_lookup
  have hma : a = meC c := by simp [meC, List.getD_eq_getElem?_getD, Ha_lookup]
  subst hma
  wp_apply (wp_NewTCP vsrnet.scanF (meC c) γ (List.mem_of_getElem? Ha_lookup)) as %tcp ⟨#Htcp, Hsnd⟩
  · iframe #
  wp_apply (wp_replicas sl n h r Hok) as %ms #Hms
  · iframe #
  wp_apply pkg.time.NewReal.wp as %rl %Hrl
  wp_apply (wp_requestMs (W64 (r : Int)) (by have := Hok.2.2; word)) as %rq -
  wp_apply (wp_logger wp_New wp_Discard) as %lg #Hlg
  have hn : n = 3 ∨ n = 5 := Hok.1
  have hms : ∀ a ∈ subslice 7 (7 + n) VsrWire.addrs, a ∈ VsrWire.addrs := fun a ha =>
    List.mem_of_mem_take (List.mem_of_mem_drop (by simpa [subslice] using ha))
  have hlen : (subslice 7 (7 + n) VsrWire.addrs).length = n := by
    rcases hn with rfl | rfl <;> rfl
  wp_apply (pkg.client.New.wp vsrnet.scanF _ γ DFrac.discard (subslice 7 (7 + n) VsrWire.addrs)
    (by rw [hlen]; rcases hn with rfl | rfl <;> decide) (by rw [hlen]; rcases hn with rfl | rfl <;> decide)
    hms Hrl) $$ [Hsnd] as %vc ⟨-, Hvc⟩
  · iframe #
    dsimp only
    isplitr
    · unfold pkg.network.isNet
      iexists tcp, meC c
      iframe #
      ipureintro; rfl
    unfold pkg.network.netSender
    iexists tcp
    iframe
    ipureintro; rfl
  have hid : uint.nat (W64 (c : Int) + W64 1) = c + 1 := by word
  dsimp only at *
  rw [hid]
  iapply HΦ
  unfold sysRes
  iexists _, tcp, vc, false, false, ⟨0, none⟩, n
  iframe
  iframe #
  ipureintro
  exact ⟨rfl, Nat.le_refl 1, fun _ => ⟨rfl, rfl⟩⟩

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
