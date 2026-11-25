/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProxyTcpInit.lean`, run
`rabia-r1wake-1`, onto `Net/`'s listeners: `net.Listen` with `listen_au` of the proxy address's
protocols (`shared_proxyProto`), retried until it succeeds.)

The proof of `rabia/internal/tcp.ProxyTcpInit`.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.ProtoLemmas
public import Net.Spec.net.Listen
public import Net.Proof.net.AtAddr
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [package_sem : rabia.internal.tcp.Assumptions]
variable [net.Assumptions] [go.BasicIntoValInj] [sync.Assumptions]

set_option goose.wp.extras true

theorem table_init (γ : Names) (n : Nat) :
    ⊢ ([∗list] c ↦ cl ∈ List.replicate n (zero_val Loc),
        ∃ ch, ⌜(List.replicate n (zero_val GoChan))[c]? = some ch⌝ ∗ tableEntry (GF := GF) γ c cl ch) := by
  refine BI.Entails.trans (Q := iprop(□ (True : IProp GF))) ?_ (BigSepL.bigSepL_intro ?_)
  · iintro -; imodintro; itrivial
  intro k x hx
  iintro -
  iexists zero_val GoChan
  have hk : k < n := by
    rw [List.getElem?_replicate] at hx; split at hx <;> simp_all
  have hx' : x = zero_val Loc := by
    rw [List.getElem?_replicate] at hx; split at hx <;> simp_all
  isplitr
  · ipureintro; rw [List.getElem?_replicate]; simp [hk]
  unfold tableEntry
  ileft; ipureintro; exact hx'

theorem ProxyTcpInit.wp_proof (wp_Listen : net.Listen.spec (GF := GF) (hG := hG)) : ProxyTcpInit.spec (GF := GF) := by
  intro γ cf k γl id toProxy hid hk
  wp_start as ⟨#Hconf, #Hsh, #Hc2p, Hrcpts⟩
  ihave %Hok := confRO_ok cf $$ Hconf
  ihave #Hproto := shared_proxyProto γ k (Nat.lt_of_lt_of_le hk (RCfg.n_le_maxS cf Hok)) $$ Hsh
  ihave %Haddr := addrTok_ok (proxyAddr k) $$ [Hproto]
  · iapply addrProto_tok $$ Hproto
  unfold confRO
  icases Hconf with ⟨-, %ps, #Hconf, #Hps⟩
  ihave Hc2 := Hconf
  iStructNamed Hc2
  wp_auto
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp (proxyAddr k) as %lv %err Hres
  · (try iframe HnetPk)
    iframe %Haddr
    iapply listen_au $$ Hproto
  ihave HI : (∃ (lv err : GoInterface), "listener" ∷ listener_ptr ↦ lv ∗ "err" ∷ err_ptr ↦ err ∗
      "Hres" ∷ ((⌜err = interface.nil⌝ ∗ ∃ l, ownListener lv l (proxyAddr k)) ∨
        ∃ i, ⌜err = interface.ok i⌝) : IProp GF) $$ [listener err Hres]
  · iexists lv, err
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #HE⟩)
    · ileft; iframe %He; iexists l; unfold ownListener; iframe Hl Hlis Hla
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      iright; iexists _; ipureintro; rfl
  wp_for HI
  icases Hres with (⟨%Heq, %l, Hl⟩ | ⟨%i, %Hne⟩)
  · subst Heq
    wp_auto
    cleanup_bool_decide
    wp_auto
    wp_apply (chan.wp_make1 (V := Unit)) as %done %γd ⟨#Hdone, -, Hdo⟩
    imod start_bag (doneP (GF := GF)) .Idle done γd (by simp) $$ Hdone Hdo with #Hdb
    imod wg_alloc «$v1_ptr» (2 * nC) (by decide) $$ «$v1» with Hwg
    wp_apply (wp_slice_make2 (V := GoChan) _) as %scs ⟨Hscs, -⟩
    · ipureintro; decide
    wp_apply (wp_slice_make2 (V := Loc) _) as %cns ⟨Hcns, -⟩
    · ipureintro; decide
    wp_apply (wp_slice_make2 (V := Loc) _) as %rds ⟨Hrds, -⟩
    · ipureintro; decide
    wp_apply +noauto (wp_slice_make2 (V := Loc) _) as %wrs ⟨Hwrs, -⟩
    · ipureintro; decide
    wp_pures
    wp_alloc p as Hp
    iStructNamed Hp
    imod sync.init_Mutex (tableInv (GF := GF) γ scs cns rds wrs) ⊤ _ $$ ConnsLock [Hscs Hcns Hrds Hwrs]
      with #Hlock
    · inext
      unfold tableInv
      iexists _, _, _, _
      iframe
      isplitr
      · ipureintro; simp [nC]
      iapply table_init
    ipersist SendChan
    ipersist Conns
    ipersist Readers
    ipersist Writers
    ipersist Listener
    ipersist RecvChan
    ipersist Done
    ipersist Wg
    wp_auto
    iapply HΦ
    isplitr
    · unfold proxyTcpRO
      iexists scs, cns, rds, wrs
      iframe #
    unfold proxyTcpOwn doneChan
    iexists lv, l, toProxy, done, «$v1_ptr»
    iframe
    iframe #
    ipureintro; exact hk
  · subst Hne
    wp_auto
    rw [if_pos (by simp)]
    wp_auto
    wp_apply time.wp_Sleep
    ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
    · solve_pkg_init
    wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp (proxyAddr k) as %lv' %err' Hres
    · (try iframe HnetPk)
      iframe %Haddr
      iapply listen_au $$ Hproto
    wp_for_post
    iframe
    iexists lv', err'
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #HE⟩)
    · ileft; iframe %He; iexists l; unfold ownListener; iframe Hl Hlis Hla
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne'
      obtain ⟨pe, rfl⟩ := Hne'.2 (by simp)
      iright; iexists _; ipureintro; rfl

end proof

end Perennial.rabia.internal.tcp
