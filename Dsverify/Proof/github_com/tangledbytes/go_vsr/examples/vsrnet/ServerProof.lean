/-
The vr kit's server machines (`kit.go`'s `Server`, `runReplica`, `logger`, `replicas`, `Addrs`;
notes/dsv-vr.md), ported from dsverify-lab `examples/vr/proof/VsrProof/Top/{Serve,NewProof,Shares}.lean`
(`wp_runReplica`, `wp_serve`, `wp_Server`, `wp_logger`, `wp_replicas`, `serverRes`).

* `srvShare γ id`: server machine `id`'s share of the start (the lab's `serverRes`): the protocols
  of the go-vsr addresses (`VsrWire.protos γ`) and of the configuration addresses (`confProtos γ`),
  the ghost layer's invariants, and replica `id - 1`'s initial model state (used only if `id ≤ N`:
  the start gives it to every server machine, N being chosen later by the orchestrator, as the lab).
  No address token: the net extension's `addrTok` is the pure `addrOk`, which `addrProto` holds.
* `srvLibState`: the packages' state the server's calls need that today's package facts do not
  give (notes/dsv-vr.md, "Open (events' package facts)" and finding 2): the frame-decoder hook set
  (`events.frameDecoderSet`, `vsrwire`'s fact in the lab), the kit's codec registered
  (`encoding.json.codecSet`, the lab's `registerJSON`; here `RegisterJSON` is empty until jsongen
  writes the codec), `network.ErrNoConn`'s value (`network`'s fact in the lab). Persistent; a
  precondition of `Server` until the package facts carry them.
* The `log/slog` hypotheses (no model here): `log.slog.New.spec` (`New(h)` is a logger) and
  `log.slog.DiscardHandler.load_spec` (reading the package variable `DiscardHandler` returns).
* `runReplica.spec`/`wp_proof`: replica `id - 1 < N` at `Addrs()[NC + id]`, the configuration's
  replicas its members; the event loop forever (`RET; False`).
* `Server.spec`/`wp_proof`: `waitConf` (`confOk γ`: N with `fact γ (.size N)`), `runReplica` if
  `id ≤ N`, then the sleep loop forever.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Conf
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrkv.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Perennial.Spec.time.Sleep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

/-! ## `log/slog` hypotheses -/

namespace log.slog

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.slog.Assumptions]

/-- **Hypothesis** (no `log/slog` model; the lab's `New.wp_DiscardHandler`, over any handler):
`slog.New(h)` is a logger. -/
abbrev New.spec : Prop :=
  ∀ (h : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog }}
    (App (Val (@! log.slog.New)) (Val #h))
  {{ (l : Loc), RET #l; isLogger l }}

/-- **Hypothesis** (no `log/slog` model): reading the package variable `DiscardHandler`, `log/slog`
initialized, returns (some handler; the lab's package state fixed its value). -/
abbrev DiscardHandler.load_spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog }}
    (App (Val (GoInstruction (GoLoad log.slog.Handler.ty)))
      (Val #(globalAddr log.slog.DiscardHandler)))
  {{ (h : GoInterface), RET #h; True }}

end spec

end log.slog

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

/-- The packages' state the server's calls need beyond today's package facts (see the file
header; persistent). -/
def srvLibState : IProp GF :=
  iprop(pkg.events.frameDecoderSet ∗ encoding.json.codecSet (GF := GF) ∗
    errors.newVar (GF := GF) pkg.network.ErrNoConn
      go!"network: no connection to the source address")

instance srvLibState_persistent : Persistent (srvLibState (GF := GF)) := by
  unfold srvLibState; infer_instance

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

/-- `Addrs()`: a new slice of the go-vsr addresses. -/
theorem wp_AddrsS :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Addrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* VsrWire.addrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) VsrWire.addrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `RegisterJSON()`: nothing (until jsongen writes the codec, notes/dsv-vr.md finding 2). -/
theorem wp_RegisterJSONS :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.RegisterJSON)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as -
  iapply HΦ; itrivial

/-- `logger()` = `slog.New(slog.DiscardHandler)`: a logger. -/
theorem wp_loggerS (wp_New : log.slog.New.spec (GF := GF) (hG := hG))
    (wp_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.logger)) (Val #()))
    {{ (l : Loc), RET #l; log.slog.isLogger l }} := by
  wp_start as -
  ihave #Hslog : isPkgInit (PROP := IProp GF) pkg_id.log.slog $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Discard as %h -
  wp_apply wp_New as %l #Hl
  iapply HΦ
  iexact Hl

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
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ srvLibState (GF := GF) ∗ sl ↦*□ VsrWire.addrs ∗
      VsrWire.protos (G := hG.goose_globalGS) γ ∗ sysInv (G := hG.goose_globalGS) γ ∗
      regInv (G := hG.goose_globalGS) γ ∗ repOwn (G := hG.goose_globalGS) γ i VsrModel.initRep ∗
      fact (G := hG.goose_globalGS) γ (.size n) }}
    (App (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.runReplica))
      (Val #(W64 ((i + 1 : Nat) : Int)))) (Val #sl)) (Val #(confOf n h r)))
  {{ RET #(); False }}

theorem runReplica.wp_proof
    (wp_New : log.slog.New.spec (GF := GF) (hG := hG))
    (wp_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG))
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_LDebug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_LInfo : log.slog.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_LWarn : log.slog.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_LError : log.slog.Logger.Error.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_RemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG))
    (wp_newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_Unmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG)
      (jc := examples.vsrnet.jsonCodec))
    (wp_NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG))
    (wp_Encode : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG)
      (jc := examples.vsrnet.jsonCodec))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)) :
    runReplica.spec (GF := GF) (hG := hG) := by
  intro γ i n h r hconf hi sl
  wp_start as ⟨#Hls, #Hsl, #Hprotos, #HsysI, #HregI, Hrep, #Hsize⟩
  iunfold srvLibState at Hls
  icases Hls with ⟨#Hfd, #Hset, #Herr⟩
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
  wp_apply wp_RegisterJSONS
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
  wp_apply (pkg.network.NewTCP.wp (pkg.events.Event.FromDecoder.wp wp_Unmarshal codec_ok)
      examples.vsrnet.scanF (VsrWire.addrs.getD (7 + i) go!"") γ hmem)
    as %tcp ⟨#Htcp, Hts⟩
  · iframe #
  wp_apply vsrkv.New.wp as %st Hst
  ihave #Hh := vsrkv.Store.Handle_value.wp st $$ []
  · iPkgInit
  wp_apply (wp_heartbeatMs _ (by unfold ConfOk at hconf; word)) as %hb -
  wp_apply pkg.time.NewReal.wp as %rl %Hrl
  wp_apply (wp_replicasS sl n h r (by have := Hslwf.2; rw [hlen] at this; omega) hn5)
  wp_apply (wp_loggerS wp_New wp_Discard) as %lg #Hlg
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
  wp_apply (pkg.replica.New.wp examples.vsrnet.scanF
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
  · wp_apply (pkg.network.TCP.Run.wp wp_Debug wp_newDecoder pkg.events.NewNetworkEvent.wp wp_Close
      wp_Accept wp_RemoteAddr wp_Listen tcp γ (VsrWire.addrs.getD (7 + i) go!"")) as %e -
    · iframe; iframe #
    itrivial
  have hRun := pkg.replica.Replica.Run.wp (GF := GF) (hG := hG) wp_LDebug wp_LInfo wp_LWarn wp_LError
    (pkg.network.TCP.Send.wp wp_Debug wp_newDecoder pkg.events.NewNetworkEvent.wp wp_Dial wp_Close)
    (pkg.events.Event.ToWriter.wp wp_NewEncoder wp_Encode codec_ok)
  wp_for
  wp_apply (pkg.network.TCP.Recv.wp tcp γ (VsrWire.addrs.getD (7 + i) go!"")) $$ [] as %ev %ok Hev
  · iframe #
  cases ok
  case true =>
    simp only [↓reduceIte]
    wp_auto
    wp_apply (pkg.replica.Replica.Submit.wp rp γ i tcp ev) $$ [Hrp Hev] as Hrp
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

/-- **`Server(id)`**: server machine `id` (`1 ≤ id ≤ 5`, machine `NC + id`), given the start's
share (`srvShare`) and the packages' state (`srvLibState`); it never returns. -/
abbrev Server.spec : Prop :=
  ∀ (γ : Names) (id : w64), 1 ≤ uint.nat id ∧ uint.nat id ≤ 5 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ srvLibState (GF := GF) ∗
      srvShare (G := hG.goose_globalGS) γ (uint.nat id) }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Server)) (Val #id))
  {{ RET #(); False }}

theorem Server.wp_proof
    (wp_New : log.slog.New.spec (GF := GF) (hG := hG))
    (wp_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG))
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_LDebug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_LInfo : log.slog.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_LWarn : log.slog.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_LError : log.slog.Logger.Error.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_RemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG))
    (conn_readerOk : connReaderOk (GF := GF) (hG := hG))
    (wp_newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_Unmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG)
      (jc := examples.vsrnet.jsonCodec))
    (wp_NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG))
    (wp_Encode : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG)
      (jc := examples.vsrnet.jsonCodec))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro γ id hid
  obtain ⟨i, hi_eq⟩ : ∃ i : Nat, uint.nat id = i + 1 := ⟨uint.nat id - 1, by omega⟩
  have hex : id = W64 ((i + 1 : Nat) : Int) := by word
  subst hex
  have hi5 : i < 5 := by omega
  rw [hi_eq]
  wp_start as ⟨#Hls, Hsh⟩
  iunfold srvShare at Hsh
  rw [Nat.add_sub_cancel]
  icases Hsh with ⟨#Hprotos, #Hcps, #HsysI, #HregI, Hrep⟩
  wp_auto
  wp_apply CfgAddrs.wp_proof as %cfgs Hcfgs
  wp_apply (waitConf.wp_proof wp_Listen wp_Accept wp_Write wp_Close conn_readerOk γ cfgs _
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
    wp_apply wp_AddrsS as %sl Hsl
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    imodintro
    wp_apply (runReplica.wp_proof wp_New wp_Discard wp_Debug wp_LDebug wp_LInfo wp_LWarn wp_LError
      wp_Listen wp_Accept wp_Dial wp_Close wp_RemoteAddr wp_newDecoder wp_Unmarshal wp_NewEncoder
      wp_Encode codec_ok γ i n h r hconf hin sl) $$ [Hrep] as %hf
    · iframe; iframe #
    exact hf.elim
  · wp_for
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
