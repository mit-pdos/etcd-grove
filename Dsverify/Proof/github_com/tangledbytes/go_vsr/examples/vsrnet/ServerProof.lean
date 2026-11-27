/-
The vr kit's server machines (`kit.go`'s `Server`, `runReplica`, `logger`, `replicas`, `Addrs`;
notes/dsv-vr.md), ported from dsverify-lab `examples/vr/proof/VsrProof/Top/{Serve,NewProof,Shares}.lean`
(`wp_runReplica`, `wp_serve`, `wp_Server`, `wp_logger`, `wp_replicas`, `serverRes`).

* `srvShare γ id`: server machine `id`'s share of the start (the lab's `serverRes`): the protocols
  of the go-vsr addresses (`VsrWire.protos γ`) and of the configuration addresses (`confProtos γ`),
  the ghost layer's invariants, and replica `id - 1`'s initial model state (used only if `id ≤ N`:
  the start gives it to every server machine, N being chosen later by the orchestrator, as the lab).
  No address token: the net extension's `addrTok` is the pure `addrOk`, which `addrProto` holds.
* The kit's codec registered (`encoding.json.codecSet`, the lab's `registerJSON`) comes from
  `RegisterJSON()`'s call (`RegisterJSON.spec`, `KitLib.lean`), from the machine's boot resource
  `codecFresh`. The
  frame-decoder hook set (`events.frameDecoderSet`) and `network.ErrNoConn`'s value are the
  package facts of `vsrwire` (which the kit links) and `network` (`kit_frameDecoderSet`,
  `Conf.lean`).
* The `log/slog` hypotheses (no model here) are `Dsverify/Spec/log/slog/Logger.lean`'s; `logger()`,
  `Addrs()`, `RegisterJSON()` are `KitLib.lean`'s.
* `runReplica.spec`/`wp_proof`: replica `id - 1 < N` at `Addrs()[NC + id]`, the configuration's
  replicas its members; the event loop forever (`RET; False`).
* `Server.spec`/`wp_proof`: `waitConf` (`confOk γ`: N with `fact γ (.size N)`), `runReplica` if
  `id ≤ N`, then the sleep loop forever.
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
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ServerProofDefs

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
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF] [encoding.json.EncoderRep GF]
variable [vw_sem : github_com.tangledbytes.go_vsr.examples.vsrwire.Assumptions]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem runReplica.wp_proof
    (wp_New : log.slog.New.spec (GF := GF) (hG := hG))
    (wp_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG))
    (wp_RegisterJSON : RegisterJSON.spec (GF := GF) (hG := hG))
    (wp_NewTCP : pkg.network.NewTCP.spec (GF := GF) (hG := hG))
    (wp_TCP_Run : pkg.network.TCP.Run.spec (GF := GF) (hG := hG))
    (wp_Recv : pkg.network.TCP.Recv.spec (GF := GF) (hG := hG))
    (wp_StoreNew : vsrkv.New.spec (GF := GF) (hG := hG))
    (wp_Handle_value : vsrkv.Store.Handle_value.spec (GF := GF) (hG := hG))
    (wp_NewReal : pkg.time.NewReal.spec (GF := GF) (hG := hG))
    (wp_ReplicaNew : pkg.replica.New.spec (GF := GF) (hG := hG))
    (wp_Run : pkg.replica.Replica.Run.spec (GF := GF) (hG := hG))
    (wp_Submit : pkg.replica.Replica.Submit.spec (GF := GF) (hG := hG)) :
    runReplica.spec (GF := GF) (hG := hG) := by
  intro γ i n h r hconf hi sl
  wp_start as ⟨#Hsl, #Hprotos, #HsysI, #HregI, Hrep, #Hsize, Hfr⟩
  ihave #Hfd := kit_frameDecoderSet $$ []
  · iPkgInit
  have hk := codec_ok
  unfold examples.vsrnet.codecOk at hk
  ihave #Hkit := hk
  ihave #HnP : pkg.network.netProtos γ $$ [Hprotos]
  · unfold pkg.network.netProtos; iexact Hprotos
  have hn5 : n ≤ 5 := by unfold ConfOk at hconf; omega
  ihave %Hslen := ownSlice_len $$ Hsl
  ihave %Hslwf := ownSlice_wf $$ Hsl
  have hlen : sint.Z sl.len = 12 := by
    have := Hslen.1; simp [VsrWire.addrs] at this; word
  wp_auto
  wp_apply wp_RegisterJSON $$ [Hfr] as #Hset
  · iframe
  have hix : 0 ≤ sint.Z (W64 6 + W64 ((i + 1 : Nat) : Int)) ∧
      sint.Z (W64 6 + W64 ((i + 1 : Nat) : Int)) < sint.Z sl.len := by
    rw [hlen]; constructor <;> word
  simp only [hix, _root_.and_self, ↓reduceIte]
  have hmeq : (sint.Z (W64 6 + W64 ((i + 1 : Nat) : Int))).toNat = 7 + i := by word
  have hme : VsrWire.addrs[(sint.Z (W64 6 + W64 ((i + 1 : Nat) : Int))).toNat]? =
      some (VsrWire.addrs.getD (7 + i) go!"") := by
    rw [hmeq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [addrs_len]; omega)]
    rfl
  wp_apply (wp_load_slice_index sl _ VsrWire.addrs DFrac.discard _ hix.1) $$ [Hsl] as -
  · isplitl
    · iexact Hsl
    ipureintro; exact hme
  have hmem : VsrWire.addrs.getD (7 + i) go!"" ∈ VsrWire.addrs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [addrs_len]; omega)]
    simp
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network $$ []
  · iPkgInit
  wp_apply (wp_NewTCP examples.vsrnet.scanF (VsrWire.addrs.getD (7 + i) go!"") γ hmem)
    as %tcp ⟨#Htcp, Hts⟩
  · iframe #
  wp_apply wp_StoreNew as %st Hst
  ihave #Hh := wp_Handle_value st $$ []
  · iPkgInit
  wp_apply (wp_heartbeatMs _ (by unfold ConfOk at hconf; word)) as %hb -
  wp_apply wp_NewReal as %rl %Hrl
  wp_apply (wp_replicasS sl n h r (by have := Hslwf.2; rw [hlen] at this; omega) hn5)
  wp_apply (wp_logger wp_New wp_Discard) as %lg #Hlg
  have hbd : 0 ≤ sint.Z (W64 7) ∧ sint.Z (W64 7) ≤ sint.Z (W64 7 + W64 (n : Int)) ∧
      sint.Z (W64 7 + W64 (n : Int)) ≤ sint.Z sl.len := by
    rw [hlen]; refine ⟨by decide, ?_, ?_⟩ <;> word
  ihave #Hmem := (ownSlice_slice (W64 7) (W64 7 + W64 (n : Int)) sl DFrac.discard VsrWire.addrs
    hbd).1 $$ Hsl
  icases Hmem with ⟨-, #Hmem, -⟩
  have hmsl : (subslice (sint.nat (W64 7)) (sint.nat (W64 7 + W64 (n : Int))) VsrWire.addrs).length
      = n := by
    have e : sint.nat (W64 7 + W64 (n : Int)) = 7 + n := by word
    rw [e]; simp only [subslice, List.length_take, List.length_drop, addrs_len]
    simp only [show sint.nat (W64 7) = 7 from rfl]; omega
  have hmc : ∀ a ∈ subslice (sint.nat (W64 7)) (sint.nat (W64 7 + W64 (n : Int))) VsrWire.addrs,
      a ∈ VsrWire.addrs := by
    intro a ha; unfold subslice at ha; exact List.mem_of_mem_take (List.mem_of_mem_drop ha)
  have hid : uint.nat (W64 ((i + 1 : Nat) : Int) - W64 1) = i := by word
  ihave #Hrp : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica $$ []
  · iPkgInit
  wp_apply (wp_ReplicaNew examples.vsrnet.scanF
    ⟨hb * W64 1000000, methods (go.GoType.PointerType vsrkv.Store.ty) go!"Handle" #st,
      interface.mkOk (go.GoType.PointerType pkg.network.TCP.ty) #tcp,
      interface.mkOk (go.GoType.PointerType pkg.time.Real.ty) #rl, W64 ((i + 1 : Nat) : Int) - W64 1,
      slice.slice sl GoString (W64 7) (W64 7 + W64 (n : Int)), lg⟩ γ n i tcp
      (VsrWire.addrs.getD (7 + i) go!"") DFrac.discard _
      (vsrkv.isStore st) hid hi hmsl (by omega) hmc rfl Hrl) $$ [Hts Hst Hrep]
    as %rp ⟨-, Hrp⟩
  · iframe; iframe #
  have hget : VsrWire.addrs[7 + i]? = some (VsrWire.addrs.getD (7 + i) go!"") := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [addrs_len]; omega)]; rfl
  ihave #Hps := Hprotos
  iunfold VsrWire.protos at Hps
  ihave #Hpa := (BigSepL.bigSepL_lookup (PROP := IProp GF)
    (Φ := fun _ a => addrProto (Gg := hG.goose_globalGS) a (VsrWire.protoOf γ) (VsrWire.protoOf γ))
    hget) $$ Hps
  iunfold addrProto at Hpa
  icases Hpa with ⟨%γa, -, -, #Htok, -⟩
  wp_apply wp_fork $$ []
  · wp_apply (wp_TCP_Run tcp γ (VsrWire.addrs.getD (7 + i) go!"")) as %e -
    · iframe; iframe #
    itrivial
  have hRun := wp_Run
  wp_for
  wp_apply (wp_Recv tcp γ (VsrWire.addrs.getD (7 + i) go!"")) $$ [] as %ev %ok Hev
  · iframe #
  cases ok
  case true =>
    simp only [↓reduceIte]
    wp_auto
    wp_apply (wp_Submit rp γ i tcp ev) $$ [Hrp Hev] as Hrp
    · iframe
    wp_apply (hRun rp γ i tcp) $$ [Hrp] as Hrp
    · iframe
    wp_for_post
    iframe
  wp_auto
  wp_apply (hRun rp γ i tcp) $$ [Hrp] as Hrp
  · iframe
  wp_apply time.wp_Sleep
  wp_for_post
  iframe

theorem Server.wp_proof
    (wp_CfgAddrs : CfgAddrs.spec (GF := GF) (hG := hG))
    (wp_waitConf : waitConf.spec (GF := GF) (hG := hG))
    (wp_runReplica : runReplica.spec (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro γ id hid
  obtain ⟨i, hi_eq⟩ : ∃ i : Nat, uint.nat id = i + 1 := ⟨uint.nat id - 1, by omega⟩
  have hex : id = W64 ((i + 1 : Nat) : Int) := by word
  subst hex
  have hi5 : i < 5 := by omega
  rw [hi_eq]
  wp_start as ⟨Hsh, Hfr⟩
  iunfold srvShare at Hsh
  rw [Nat.add_sub_cancel]
  icases Hsh with ⟨#Hprotos, #Hcps, #HsysI, #HregI, Hrep⟩
  wp_auto
  wp_apply wp_CfgAddrs as %cfgs Hcfgs
  wp_apply (wp_waitConf γ cfgs _
    (W64 6 + W64 ((i + 1 : Nat) : Int)) (by word)) $$ [Hcfgs] as %cf ⟨-, HP⟩
  · iframe; iframe #
  iunfold confOk at HP
  icases HP with ⟨%n, %h, %r, %Hcf, #Hsize⟩
  obtain ⟨rfl, hconf⟩ := Hcf
  wp_auto
  wp_if_destruct
  · have hin : i < n := by
      have : n ≤ 5 := by unfold ConfOk at hconf; omega
      word
    wp_apply wp_Addrs as %sl Hsl
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    imodintro
    wp_apply (wp_runReplica γ i n h r hconf hin sl) $$ [Hrep Hfr] as %hf
    · iframe; iframe #
    exact hf.elim
  · wp_for
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
