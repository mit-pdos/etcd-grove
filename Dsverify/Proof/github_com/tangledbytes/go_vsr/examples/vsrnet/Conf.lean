/-
The vr kit's configuration protocol (`kit.go`: `CfgAddrs`, `Conf`, `heartbeatMs`, `requestMs`,
`choose`, `Conf.encode`, `decode`, `sendConf`, `Configure`, `awaitConf`, `waitConf`), ported from
dsverify-lab `examples/vr/proof/VsrProof/{Top/Orch,Top/AwaitConf,Wire/Basic}.lean` (notes/dsv-vr.md)
onto the net extension (`net.Dial`/`Listen`/`Listener.Accept`/`Conn.Write`/`Conn.Close` specs as
hypotheses, `GooseLang/Ext/Net/Proto.lean`'s laws) and Perennial's `io.ReadFull` (`io.wp_ReadFull`,
over an `io.readerOk` of the connection: the hypothesis `conn_readerOk`).

* `cfgAddrs` (`Wire/Addrs.lean`): the kit's `CfgAddrs()`, machine `n`'s configuration address at
  `n` (the orchestrator's, `n = 0`, unused).
* `confBytes n h r`, `ConfOk n h r`: a configuration's three bytes; one `decode` accepts.
* `confProto γ`, `ackProto`, `confProtos γ`: the configuration's wire: what the orchestrator writes
  to a configuration address is a prefix of the bytes of one accepted configuration whose number
  of replicas is the system's (`fact γ (.size n)`); the answers mean nothing.
* `confOk γ cf`: what a machine learns, `cf` an accepted configuration with `fact γ (.size n)`.
* `Configure.wp_proof`: from `fact γ (.size n)` (the orchestrator's `ghost_size` of its
  `sizeTok`, as the lab's `wp_New_proof`), the configuration is sent to machines `1 .. NC + N`.
* `waitConf.wp_proof`: machine `n`'s configuration is `confOk γ`.
-/
module

public import Net.Proof.net.AtAddr
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Kit
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.Addrs
public import Perennial.Proof.github_com.goose_lang.primitive.RandomUint64
public import Perennial.Proof.io.Link
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import GooseLang.Ext.Net.Stream
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.LibHyps
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ConfDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The configuration's wire -/

section conf
variable [GooseExts]

end conf

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

end defs

/-! ## Pure facts -/

/-! ## The proofs -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem CfgAddrs.wp_proof : CfgAddrs.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) cfgAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

theorem Configure.wp_proof (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (conn_readerOk : connReaderOk (GF := GF) (hG := hG)) :
    Configure.spec (GF := GF) (hG := hG) := by
  intro γ cfgs dq n h r hc
  wp_start as ⟨Hcfgs, #Hps, #Hf⟩
  obtain ⟨hn, hh, hr⟩ := hc
  wp_auto
  ihave %Hclen := ownSlice_len $$ Hcfgs
  have hn5 : n ≤ 5 := by rcases hn with rfl | rfl <;> decide
  ihave IH : iprop(∃ (k : w64), "n" ∷ n_ptr ↦ k ∗ "Hcfgs" ∷ cfgs ↦*{dq} cfgAddrs ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ 7 + n⌝) $$ [n Hcfgs]
  · iexists _; iframe; ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  by_cases Hif : uint.Z k ≤ uint.Z (W64 6 + W64 (n : Int))
  · simp only [Hif, decide_true, ↓reduceIte]
    have hk12 : uint.nat k ≤ 11 := by word
    obtain ⟨a, ha⟩ : ∃ a, cfgAddrs[uint.nat k]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by simp [cfgAddrs]; omega)⟩
    ihave #Hps' := Hps
    iunfold confProtos at Hps'
    ihave #Hpa := (BigSepL.bigSepL_lookup (PROP := IProp GF)
      (Φ := fun _ a => addrProto (Gg := hG.goose_globalGS) a (confProto γ) ackProto) ha) $$ Hps'
    wp_call
    wp_for
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z cfgs.len := by
      have : cfgAddrs.length = 12 := rfl
      rw [this] at Hclen
      constructor <;> word
    rw [ite_eq_left hb]
    wp_apply wp_load_slice_index cfgs (sint.Z k) _ dq a hb.1 $$ [$Hcfgs] as Hcfgs
    · ipureintro; rw [show (sint.Z k).toNat = uint.nat k by word]; exact ha
    wp_method_call
    wp_auto
    wp_apply wp_Conf_encode n h r ⟨hn, hh, hr⟩ as %bsl Hbsl
    wp_apply wp_sendConf wp_Dial wp_Write wp_Close conn_readerOk γ a bsl n h r ⟨hn, hh, hr⟩
      $$ [$Hpa $Hf $Hbsl] as %ok -
    cases ok
    · simp only [Bool.not_false]
      cleanup_bool_decide
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · simp only [Bool.not_true]
      cleanup_bool_decide
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have : uint.Z (W64 6 + W64 (n : Int)) = 6 + n := by word
      constructor <;> word
  · simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iexact Hcfgs

theorem waitConf.wp_proof (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (conn_readerOk : connReaderOk (GF := GF) (hG := hG)) :
    waitConf.spec (GF := GF) (hG := hG) := by
  intro γ cfgs dq m hm
  wp_start as ⟨Hcfgs, #Hps⟩
  obtain ⟨ca, hca⟩ : ∃ ca, cfgAddrs[uint.nat m]? = some ca :=
    ⟨_, List.getElem?_eq_getElem (by simp [cfgAddrs]; omega)⟩
  ihave #Hps' := Hps
  iunfold confProtos at Hps'
  ihave #Hpa := (BigSepL.bigSepL_lookup (PROP := IProp GF)
    (Φ := fun _ a => addrProto (Gg := hG.goose_globalGS) a (confProto γ) ackProto) hca) $$ Hps'
  ihave %Hclen := ownSlice_len $$ Hcfgs
  wp_auto
  wp_apply chan.wp_make2 (V := Conf) (W64 1) $$ [] as %ch %γch ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  iapply fupd_wp
  imod start_future (V := Conf) ch γch _ (.inr rfl) $$ Hch Hoc with ⟨%γf, #Hfut, HAwait⟩
  imod future_alloc_promise (V := Conf) γf ch (confOk (G := hG.goose_globalGS) γ) [] $$ Hfut HAwait
    with ⟨Hful, HAwait⟩
  imodintro
  have hb : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z cfgs.len := by
    have : cfgAddrs.length = 12 := rfl
    rw [this] at Hclen
    constructor <;> word
  rw [ite_eq_left hb]
  wp_apply wp_load_slice_index cfgs (sint.Z m) _ dq ca hb.1 $$ [$Hcfgs] as Hcfgs
  · ipureintro; rw [show (sint.Z m).toNat = uint.nat m by word]; exact hca
  wp_apply wp_fork $$ [Hful]
  · wp_apply (wp_awaitConf wp_Listen wp_Accept wp_Write wp_Close conn_readerOk γ γf ch ca)
      $$ [Hful]
    · iframe; iframe #
    itrivial
  wp_apply (wp_future_await (t := Conf.ty) γf ch _) $$ [HAwait]
    as %cf %P %pre %post ⟨%Hsplit, HP, -⟩
  · iframe; iframe #
  have hP : P = confOk (G := hG.goose_globalGS) γ := by
    rcases pre with _ | ⟨_, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at Hsplit; exact Hsplit.1.symm
    · simp at Hsplit
  subst hP
  iapply HΦ
  iframe

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
