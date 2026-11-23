/-
The orchestrator (`kit.go`'s `Orch`, `orch`, `New`, `send`, `sendConf`): it chooses the
configuration (`confIs γ c` from `orchRes`'s `confTok γ`), sends it to every machine that needs
it under the configuration protocol (`confInProto γ`, `ackProto`), waits, and runs
`remote.Check` against the kit's model (`Model.spec`) with the kit's codec (`codec_proof`) and
generator (`gens_proof`): porcupine's model is the pending-writes model of the far side's store
(`qS_pendDec`), the masks are disjoint (`pendN_raxos`, `lintestN_raxos`), the codec is injective
on outputs (`qR_encOut_inj`). The library specs are parameters (the kit's `Results` supplies the
proofs).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitAwait
public import Dsverify.Proof.raxos.examples.quepaxanet.KitCodecFn
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Perennial.Spec.time.Sleep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

section send
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [_root_.Perennial.io.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

theorem slice_to_array1 (l : Loc) (d : w8) :
    (slice.mk l (W64 1) (W64 1) ↦* [d] : IProp GF) ⊢ l ↦ (GoArray.mk [d] : GoArray w8 1) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; simp at H
  · iExactEq H; rfl

/-- `c.Close()` on an end of a library connection: some error. -/
theorem wp_closeConn (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    {{ net.connAt (GF := GF) t cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (e : GoInterface), RET #e; True }} := by
  iintro %Φ ⟨#Hca, #HcIs⟩ HΦ
  wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [] as %e -
  · iframe Hca
    imod close_au cn s $$ HcIs with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Ho Hst Hdd
    imod Hcl $$ %res %st' %d' %Ho Hst Hdd with -
    imodintro; itrivial
  iapply HΦ
  itrivial

/-- `sendConf(a, b)`, `b` the configuration's encoding, at a configuration address `a`: one
attempt. -/
theorem wp_sendConf_of
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (γ : QNames) (a : GoString) (c : QConf) (hc : c.ok) (b : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗
        addrProto a (confInProto γ) ackProto ∗ confIs γ c ∗ b ↦* encConf c }}
      (App (App (Val (@! raxos.examples.quepaxanet.sendConf)) (Val #a)) (Val #b))
    {{ (ok : Bool), RET #ok; True }} := by
  wp_start as ⟨#Hpr, #Hconf, Hb⟩
  ihave %Hok := addrTok_ok a $$ [Hpr]
  · iapply addrProto_tok $$ Hpr
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  icases (github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll) $$ Hpoll with ⟨%ed, #Hed⟩
  ihave #Hioi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hioi with ⟨-, -, -, -, #HEOFv, #HUEOFv, -⟩
  iunfold errors.newVar at HEOFv
  iunfold errors.newVar at HUEOFv
  icases HEOFv with ⟨%xe, #Heof, -⟩
  icases HUEOFv with ⟨%xu, #Hueof, -⟩
  wp_auto
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp a iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (confInProto γ) ackProto [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
    as %cv %err (⟨%Herr, %cn, #Hc2, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au a (confInProto γ) ackProto $$ Hpr
  · subst Herr
    iunfold connEnd at Hend
    icases Hend with ⟨Hs, Hr⟩
    ihave #HcIs := sendTok_connIs cn false _ _ $$ Hs
    ihave Hr := recvTok_L cn false _ _ $$ Hr
    iunfold net.isConn at Hc2
    icases Hc2 with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    ihave #Hp0 : (□ confInProto (GF := GF) γ cn ([] ++ encConf c)) $$ []
    · iintro !>
      unfold confInProto
      iexists c
      iframe Hconf
      ipureintro; exact ⟨hc, by simp⟩
    wp_apply wp_Write t cn false a la ra _ (encConf c) (DFrac.own 1) ed
        (writeP cn false (confInProto γ) []) $$ [Hb Hs]
      as %n %err ⟨%w, %res, Hs, Hb, %Hw, #HE⟩
    · iframe Hca Hb Hed
      isplitl [Hs]
      · iapply writeP_init $$ Hs
      · iapply write_acc cn false (confInProto γ) [] (encConf c) $$ Hp0
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    cases res with
    | some ke =>
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply wp_closeConn wp_Close t cn false a la ra $$ [$Hca $HcIs] as %e -
      iapply HΦ
      itrivial
    | none =>
      have herr := Hne.1 rfl
      subst herr
      wp_auto
      ihave #Hrok := net.conn_readerOk wp_Read t cn false a la ra _ ed ackProto
        $$ [$Hio $Hca $Heof $Hed]
      have h0 : sint.Z (W64 0) = 0 := rfl
      rw [h0, go.arrayIndexRef_0, show W64 1 - W64 0 = W64 1 from rfl]
      ihave Hsl := slice_array a_ptr 1 _ (by decide) $$ a
      rw [show (zero_val (GoArray w8 1)).arr = [W8 0] from rfl]
      rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t =
        GoInterface.ok (net.connIface t) from rfl]
      wp_apply wp_ReadFull (net.connIface t) (fun _ m => 0 < m)
          (recvTokL (Gg := hG.goose_globalGS) cn false ackProto) _ [] _ _ _ _
        $$ [$Hio $Hrok $Heof $Hueof $Hr $Hsl] as %n2 %err2 ⟨%data, %Hd, Hsl, Hr, #Hres⟩
      · ipureintro; intro ys hys; omega
      cases err2 with
      | ok ie =>
        wp_auto
        wp_apply wp_closeConn wp_Close t cn false a la ra $$ [$Hca $HcIs] as %e -
        iapply HΦ
        itrivial
      | nil =>
        ihave %hd1 : ⌜data.length = 1⌝ $$ [Hres]
        · iunfold _root_.Perennial.io.readFullRes at Hres
          icases Hres with (%h | ⟨%e, %h, -⟩)
          · ipureintro; rw [h.1]; rfl
          · exfalso
            obtain ⟨-, hne, h1, h2⟩ := h
            by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe ∧ data ≠ []
            · exact absurd (h1 hc) (by intro h; cases h)
            · exact hne (h2 hc).symm
        obtain ⟨d, rfl⟩ : ∃ d, data = [d] := by
          match data, hd1 with
          | [d], _ => exact ⟨d, rfl⟩
        rw [show List.drop [d].length [W8 0] = [] from rfl, List.append_nil]
        ihave Ha := slice_to_array1 a_ptr d $$ Hsl
        wp_auto
        ihave ⟨Hv, -⟩ := array_acc (V := w8) a_ptr (sint.Z (W64 0)) (DFrac.own 1) 1
          (GoArray.mk [d]) d (by decide) rfl $$ Ha
        wp_auto
        wp_if_destruct
        all_goals
          (try wp_auto)
          wp_apply wp_closeConn wp_Close t cn false a la ra $$ [$Hca $HcIs] as %e -
          (try wp_auto)
          iapply HΦ
          itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial

/-- `send(cfgs, conf)`: the configuration to nodes `1..6 + c.n`, each until it acknowledges. -/
theorem wp_send_of [log.Assumptions]
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (γ : QNames) (c : QConf) (hc : c.ok) (cfgs : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sharedRes γ ∗ confIs γ c ∗ cfgs ↦*□ cfgAddrsL }}
      (App (App (Val (@! raxos.examples.quepaxanet.send)) (Val #cfgs)) (Val #(goConf c)))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hsh, #Hconf, #Hcfgs⟩
  wp_auto
  wp_apply wp_String conf_ptr c $$ [$conf] as %str conf
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.string #(go!"quepaxanet: configuration: " ++ str)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.log $$ []
  · iPkgInit
  wp_apply wp_log_Println _ _ $$ [$Hlog $Hlit]
  ihave %Hcfl := ownSlice_len _ _ _ $$ Hcfgs
  have hcfl : sint.Z cfgs.len = 12 := by
    have : cfgAddrsL.length = 12 := rfl
    obtain ⟨h1, h2⟩ := Hcfl
    have h3 : ((sint.nat cfgs.len : Nat) : Int) = sint.Z cfgs.len := Int.toNat_of_nonneg h2
    omega
  have hn5 : c.n ≤ 5 := by rcases hc.1 with h | h <;> omega
  ihave HS : (∃ nv : w64, "n" ∷ n_ptr ↦ nv ∗ "conf" ∷ conf_ptr ↦ goConf c ∗
      "%Hnv" ∷ ⌜1 ≤ uint.nat nv ∧ uint.nat nv ≤ 6 + c.n + 1⌝ : IProp GF) $$ [n conf]
  · iexists W64 1; iframe; ipureintro; constructor <;> word
  wp_for HS
  wp_if_destruct
  · have hnv : uint.nat nv ≤ 6 + c.n := by
      have : uint.nat (W64 (c.n : Int)) = c.n := by word
      word
    have hk : 1 ≤ uint.nat nv ∧ uint.nat nv ≤ 11 := ⟨Hnv.1, by omega⟩
    have hidx : 0 ≤ sint.Z nv ∧ sint.Z nv < sint.Z cfgs.len := by
      constructor <;> word
    ihave #Hpr := confProto_of_shared γ (uint.nat nv) hk $$ Hsh
    wp_for
    rw [ite_eq_left hidx]
    wp_apply wp_load_slice_index cfgs _ _ DFrac.discard (portAddr (7640 + uint.nat nv))
      hidx.1 $$ [Hcfgs] as -
    · iframe Hcfgs; ipureintro
      rw [show (sint.Z nv).toNat = uint.nat nv by word]
      exact cfgAddrsL_get _ (by omega)
    wp_apply wp_encode conf_ptr c hc $$ [$conf] as %b ⟨conf, Hb⟩
    wp_apply wp_sendConf_of wp_Read wp_Write wp_Close wp_ReadFull wp_Dial γ _ c hc b
      $$ [$Hpr $Hconf $Hb] as %ok -
    cases ok
    · rw [if_pos (by simp)]
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · rw [if_neg (by simp; intro h; exact absurd (go.IntoValInj.intoVal_inj h) (by decide))]
      rw [if_pos (by simp)]
      wp_for_post
      iframe
      iexists nv + W64 1
      iframe
      ipureintro; constructor <;> word
  · wp_end

/-- `New(cfgs)`: the configuration chosen (`confIs γ c` from `confTok γ`) and sent. -/
theorem wp_New_of [log.Assumptions] [hr : hyp.RandHyp GF]
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (γ : QNames) (cfgs : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ orchRes γ ∗ cfgs ↦*□ cfgAddrsL }}
      (App (Val (@! raxos.examples.quepaxanet.New)) (Val #cfgs))
    {{ RET #(); True }} := by
  wp_start as ⟨Hres, #Hcfgs⟩
  wp_auto
  wp_apply wp_choose as %c %hc
  unfold orchRes
  icases Hres with ⟨Hconf, #Hsh⟩
  iapply fupd_wp
  imod conf_choose γ c $$ Hconf with #Hconf
  imodintro
  wp_apply wp_send_of wp_Read wp_Write wp_Close wp_ReadFull wp_Dial γ c hc cfgs
    $$ [$Hsh $Hconf $Hcfgs]
  wp_end

end send

/-! ## Masks, injectivity, the model's decoder -/

theorem pendN_raxos : (↑pendN : CoPset) ⊆ ⊤ \ (↑raxosN : CoPset) := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  intro h
  exact ndot_ne_disjoint nroot (show "remote" ≠ "raxos" by decide) p ⟨h1, h⟩

theorem lintestN_raxos :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ ((↑raxosN : CoPset) ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "raxos" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

section dec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : raxos.examples.quepaxanet.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- Distinct outputs have distinct bytes. -/
theorem qR_encOut_inj (γ : QNames) (o o' : QOut)
    (h : (qR (Gg := Gg) γ).encOut ((qR (Gg := Gg) γ).ov o) =
      (qR (Gg := Gg) γ).encOut ((qR (Gg := Gg) γ).ov o')) : o = o' := by
  have hb : ∀ o : QOut, (encOutB false o.1.found o.1.v).length < 2 ^ 63 := by
    intro o; have := o.2; unfold qOutOk at this; simp [encOutB]; omega
  simp only [qR, qov] at h
  rw [encOutV_outV _ _ _ (hb o), encOutV_outV _ _ _ (hb o')] at h
  simp only [encOutB, List.cons.injEq] at h
  obtain ⟨-, hf, hv⟩ := h
  have hf' : o.1.found = o'.1.found := by
    cases h1 : o.1.found <;> cases h2 : o'.1.found <;> simp_all [flagB]
  apply Subtype.ext
  cases o with | mk o _ => cases o' with | mk o' _ =>
  cases o; cases o'
  simp_all

end dec

section dec2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : raxos.examples.quepaxanet.Assumptions]

/-- **porcupine's model is the pending-writes model** of the far side's store `qR γ`. -/
theorem qS_pendDec (γ : QNames) : PendDec (qR (Gg := hG.goose_globalGS) γ) (qS (GF := GF)) where
  init := rfl
  ok s i o := by
    have h' : qOutOk ⟨(Out.mk false o.1.found o.1.v).Found', (Out.mk false o.1.found o.1.v).V'⟩ :=
      o.2
    have e := EtcdGrove.linkv.pM_step qB qDecQ s _ ⟨kin (In.mk i.1.put i.1.k i.1.v), i.2⟩ _
      (qDecQ_box (In.mk i.1.put i.1.k i.1.v) (Out.mk false o.1.found o.1.v) i.2 h')
    exact e
  err s i := by
    have h' : qOutOk ⟨(Out.mk true false []).Found', (Out.mk true false []).V'⟩ := by
      unfold qOutOk; simp
    exact EtcdGrove.linkv.pM_step qB qDecQ s _ ⟨kin (In.mk i.1.put i.1.k i.1.v), i.2⟩ _
      (qDecQ_box (In.mk i.1.put i.1.k i.1.v) (Out.mk true false []) i.2 h')
  ioOk_ok i o := BI.pure_intro ⟨⟨_, rfl, i.2⟩, _, rfl, o.2⟩
  ioOk_err i := BI.pure_intro ⟨⟨_, rfl, i.2⟩, _, rfl, by unfold qOutOk; simp⟩
  noObs _ := rfl

theorem pendCtx_qS (γ : QNames) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (qR γ) (qS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (qR γ) (qS (GF := GF)) γp := rfl

theorem pendLib_qS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (qS0 (GF := GF)) γp (qS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (qS (GF := GF)) γp (qS (GF := GF)).M.init := rfl

end dec2

/-! ## The orchestrator -/

section orch
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [_root_.Perennial.io.Assumptions] [log.Assumptions]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

/-- **`Orch()`**: the configuration chosen and sent, then `remote.Check` returns. -/
theorem Orch.wp_proof [hr : hyp.RandHyp GF]
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := raxos.pure.Store) (I := QIn) (O := QOut))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γ γp hrb
  rw [pendCtx_qS, pendLib_qS]
  wp_start as ⟨Hres, #Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  wp_apply wp_CfgAddrs as %cfgs Hcfgs
  wp_apply wp_ClientAddrs as %addrs Haddrs
  wp_apply gens_proof as %gen #Hgen
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hcfgs with #Hcfgs
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_New_of wp_Read wp_Write wp_Close wp_ReadFull wp_Dial γ cfgs $$ [$Hres $Hcfgs]
  wp_apply time.wp_Sleep
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply wp_Model as %m #Hm
  wp_apply (codec_proof γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 6 := by
    obtain ⟨h1, h2⟩ := Hal
    have : clientAddrs.length = 6 := rfl
    have h3 : ((sint.nat addrs.len : Nat) : Int) = sint.Z addrs.len := Int.toNat_of_nonneg h2
    omega
  wp_apply wp_Check (qR γ) qS γp m addrs clientAddrs cd gen _ d pendN_raxos lintestN_raxos
    (qS_pendDec γ) (qR_encOut_inj γ) (fun st => qR_timeless γ st) hrb (by rw [hlen']; decide)
    (by decide) (by rw [hlen']; decide) 60 (by decide) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    simp only [qR]; iexact Hgen
  iapply HΦ
  itrivial

end orch

end raxos.examples.quepaxanet
end Perennial
