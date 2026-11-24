/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Client/Op.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md), restated for the kit's `op` on remote and `Net/`.

`op(sys, x)` (`wp_op`, the statement `op.spec` of `KitSpecs.lean`): client `c`'s operation under
its lock. Past `K = 4` operations it answers the unknown output. Otherwise it spends a budget unit
(D14), waits for its start once (`time.Sleep`), opens its connection if needed (`wp_connect`; a
failure answers unknown), registers the request (`op_begin`, with remote's update as the Gryff
client's, `lin_opAU`), writes it (opcode, `Marshal`, `Flush`) and reads replies: a reply with
`OK = 1` to its request witnesses the commit (`reply_opDone`), whose claim (`op_end`) gives the
caller's postcondition `Φ` of the output; a reply to another request is skipped; any error, a
reply with `OK ≠ 1` or another opcode drops the connection (`wp_drop`) and answers unknown.
-/
module

public import Dsverify.Proof.gryff.Client.Conn
public import Dsverify.Proof.gryff.Client.Stream
public import Dsverify.Proof.gryff.Wire.Specs
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto dsverify_lab.harness
open Perennial.gryff.netN wire.gryffproto
open github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS
attribute [local instance] opReg_persistent opDone_persistent

section small
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions]

set_option goose.wp.extras true

/-- `unknown()`: the unknown output. -/
theorem wp_unknown :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet }}
      (App (Val (@! gryff.examples.gryffnet.unknown)) (Val #()))
    {{ (v : GoInterface), RET #v; ⌜v = examples.gryffnet.outV ⟨true, W64 0⟩⌝ }} := by
  wp_start as -
  wp_auto
  iapply HΦ; ipureintro; rfl

/-- `noDep()`: key `-1`, no value. -/
theorem wp_noDep :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet }}
      (App (Val (@! gryff.examples.gryffnet.noDep)) (Val #()))
    {{ (d : gryff.src.gryffproto.Dep), RET #d; ⌜d = noDepV⌝ }} := by
  wp_start as -
  wp_auto
  iapply HΦ; ipureintro; rfl

/-- `Start(c)`. -/
theorem wp_Start (c : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet }}
      (App (Val (@! gryff.examples.gryffnet.Start)) (Val #c))
    {{ (d : w64), RET #d; True }} := by
  wp_start as -
  wp_auto
  iapply HΦ; itrivial

end small

section connOk
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

theorem connOk_conn (γ : GryffNames GF) (c : Nat) (v : examples.gryffnet.client) :
    connOk γ c v ⊢ connOk γ c v ∗
      ⌜∃ tc : Loc, v.conn' = interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #tc⌝ := by
  apply persistent_entails_left
  iintro H
  iunfold connOk at H
  icases H with ⟨%tc, %cn, %a, %la, %ra, %eof, %ed, %R, %body, %sent, %pend, %r, %Hc, -⟩
  ipureintro; exact ⟨tc, Hc.1⟩

theorem sysSt_intro (γ : GryffNames GF) (c : Nat) (sp cl : Loc) (ops : w64)
    (v : examples.gryffnet.client) (h4 : uint.nat ops ≤ 4) :
    sp.[examples.gryffnet.Sys, go!"started"] ↦ true ∗ sp.[examples.gryffnet.Sys, go!"ops"] ↦ ops ∗
      cl ↦ v ∗ clientSt γ c v (uint.nat ops) ∗ budget (GF := GF) γ.proto (4 - uint.nat ops) ⊢
      sysSt γ c sp cl := by
  iintro ⟨Hs, Ho, Hp, Hc, Hb⟩
  iunfold sysSt
  iexists true, ops, v
  iframe
  ipureintro; exact h4

theorem clientSt_nil (γ : GryffNames GF) (c : Nat) (v : examples.gryffnet.client) (j : Nat)
    (h : uint.nat v.gen' ≤ j ∧ 0 ≤ sint.Z v.seq' ∧ sint.Z v.seq' ≤ j)
    (hn : v.conn' = interface.nil) :
    unusedIds γ c (uint.nat v.gen') ⊢ clientSt γ c v j := by
  iintro H
  iunfold clientSt
  iframe H
  isplitr
  · ipureintro; exact h
  ileft; ipureintro; exact hn

/-- A client's handshake and whole registered requests are an allowed dialer's stream. -/
theorem clientStream_ok (γ : GryffNames GF) (a : GoString) (cn : Nat) (hs : w32) (last : Int)
    (body : List w8) (hhs : hs < peerMark) :
    clientConnAt γ hs cn ∗ clientReqsOk γ hs last body ⊢ □ gryffWireP γ a cn (u32Le hs ++ body) := by
  iintro ⟨#Hcc, #Hr⟩
  iintro !>
  unfold gryffWireP
  iright
  iexists u32Le hs ++ body
  isplitr
  · ipureintro; exact List.prefix_refl _
  iintro !>
  unfold dialStream
  iexists hs, body
  isplitr
  · ipureintro; rfl
  iright
  isplitr
  · ipureintro; exact hhs
  iframe Hcc
  iexists last
  iexact Hr

/-- A prefix of an allowed dialer's stream is allowed. -/
theorem gryffWireP_prefix (γ : GryffNames GF) (a : GoString) (cn : Nat) (W W' : List w8)
    (h : W' <+: W) : □ gryffWireP γ a cn W ⊢ □ gryffWireP γ a cn W' := by
  unfold gryffWireP
  iintro #H
  iintro !>
  icases H with (%Hn | ⟨%full, %Hf, #Hs⟩)
  · ileft; ipureintro; subst Hn; exact List.prefix_nil.mp h
  iright
  iexists full
  iframe Hs
  ipureintro; exact h.trans Hf

variable [ρ : RemoteGS]

/-- Remote's update of the input is the Gryff client's (`lin_opAU`; a read's persistent one used
once). -/
theorem slotUpd_opAU (γp : ProtoNames) (i : examples.gryffnet.In) (Φ : w64 → IProp GF) :
    slotUpd (Gg := hG.goose_globalGS) (examples.gryffnet.casR γp) i Φ ⊢
      opAU γp (examples.gryffnet.toRI i) (fun _ _ o => Φ (examples.gryffnet.fromRO o).V') := by
  unfold slotUpd
  split
  · exact examples.gryffnet.lin_opAU γp i Φ
  · iintro #H
    iapply examples.gryffnet.lin_opAU γp i Φ $$ H

end connOk

section budget
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

theorem budget_split1 (γp : ProtoNames) (a n : Nat) (h : a = 1 + n) :
    budget (GF := GF) γp a ⊢ budget γp 1 ∗ budget γp n := by
  subst h; exact budget_split γp 1 n

end budget

section op
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [wire.BufioSpecs GF] [wire.BinaryVarintHyps GF]
variable [net.Assumptions] [net.FieldAssumptions] [nS : NetSpecs GF]
variable [ρ : RemoteGS]

set_option goose.wp.extras true

set_option hygiene false in
/-- Drop the connection and take the unknown output. -/
local macro "drop_unknown" : tactic => `(tactic| (
  wp_apply (wp_drop c sp mu cl { v' with seq' := v'.seq' + W32 1 } tc cn (replicaOf c) la ra
    Hconn') $$ [Hp] as Hp
  · iframe Hp; iframe #
  wp_apply wp_unknown as %u %Hu
  subst Hu))

set_option hygiene false in
/-- The postcondition after the connection was dropped: the unknown output. -/
local macro "drop_post" : tactic => `(tactic| (
  iapply HΦ
  isplitl [Hstarted Hops Hp Hids Hbud]
  · iapply (sysSt_intro γ c sp cl (ops + W64 1) _ (by omega))
    iframe Hstarted Hops Hp Hbud
    iapply clientSt_nil γ c
      ({ conn' := interface.nil, r' := v'.r', w' := v'.w', id' := v'.id', gen' := v'.gen',
         seq' := v'.seq' + W32 1 } : examples.gryffnet.client) (uint.nat (ops + W64 1))
      (hdrop _ rfl rfl) rfl $$ Hids
  iright; ipureintro; rfl))

set_option hygiene false in
/-- Skip a reply to another request: the next iteration, with the reply read. -/
local macro "skip_loop" h:term : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists _
  iframe Hrd
  ipureintro; exact $h))

set_option hygiene false in
/-- The postcondition of a commit: the output, the connection kept, its replies read up to
`R2`. -/
local macro "ok_post" R2:term:max hR2:term:max : tactic => `(tactic| (
  iapply HΦ
  isplitr [HQ]
  · iapply (sysSt_intro γ c sp cl (ops + W64 1) _ (by omega))
    iframe Hstarted Hops Hp Hbud
    iunfold clientSt
    iframe Hids
    isplitr
    · ipureintro; exact hdrop _ rfl rfl
    iright
    iunfold connOk
    iexists tc, cn, replicaOf c, la, ra, eof, ed, $R2,
      (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)), (sent2 ++ pend2), [],
      (sint.Z (v'.seq' + W32 1) + 1)
    iframe Hown Heof Hed Hrd Hwok Hwr Hcca Hreqs2 Hturn
    ipureintro
    exact ⟨Hconn', rfl, Hgen1, Hid, by simp [Hsent3], Int.le_refl _, $hR2⟩
  · ileft; iexists _; iframe HQ; ipureintro; rfl))

/-- `op(sys, x)`: see the file header (`KitSpecs.lean`'s `op.spec`). -/
theorem wp_op (γ : GryffNames GF) (c : Nat) (sp mu cl : Loc) (i : examples.gryffnet.In)
    (Φo : w64 → IProp GF) (hc : c < 6) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ □ protoInvs γ ∗
        examples.gryffnet.replicaLises γ ∗ sysFixed c sp mu cl ∗ sysSt γ c sp cl ∗
        slotUpd (Gg := hG.goose_globalGS) (examples.gryffnet.casR γ.proto) i Φo }}
      (App (App (Val (@! gryff.examples.gryffnet.op)) (Val #sp)) (Val #i))
    {{ (v : GoInterface), RET #v; sysSt γ c sp cl ∗
        ((∃ o, ⌜v = examples.gryffnet.outV ⟨false, o⟩⌝ ∗ Φo o) ∨
          ⌜v = examples.gryffnet.outV ⟨true, W64 0⟩⌝) }} := by
  wp_start as ⟨#Hinv, #Hlis, #Hfix, Hst, HU⟩
  ihave #Hfix' := Hfix
  iunfold sysFixed at Hfix'
  icases Hfix' with ⟨%ads, #Hmu, #Hcf, #Haddrs, #Hads, #Hcl⟩
  iunfold sysSt at Hst
  icases Hst with ⟨%started, %ops, %v, Hstarted, Hops, %Hops4, Hp, Hcs, Hbud⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_unknown as %u %Hu
    iapply HΦ
    isplitl [Hstarted Hops Hp Hcs Hbud]
    · iunfold sysSt
      iexists started, ops, v
      iframe
      ipureintro; exact Hops4
    iright; ipureintro; exact Hu
  have hops4 : uint.nat ops < 4 := by
    have : ¬ (4 : Int) ≤ uint.Z ops := Hif
    have h2 : (uint.nat ops : Int) = uint.Z ops := by word
    omega
  have hops1 : uint.nat (ops + W64 1) = uint.nat ops + 1 := by word
  -- the budget unit of this operation (D14)
  ihave ⟨Hb1, Hbud⟩ := budget_split1 γ.proto _ (4 - uint.nat (ops + W64 1))
    (by rw [hops1]; omega) $$ Hbud
  -- the start, once
  wp_join iprop(sp.[examples.gryffnet.Sys, go!"started"] ↦ true ∗ sys_ptr ↦ sp)
    at (if: _ then _ else _) with [Hstarted sys] as ⟨Hstarted, sys⟩
  · cases started
    · wp_auto
      wp_apply wp_Start as %d -
      wp_apply time.wp_Sleep
      wp_join_done
    · wp_auto
      wp_join_done
  -- the connection
  iunfold clientSt at Hcs
  icases Hcs with ⟨%Hcs, Hids, Hco⟩
  obtain ⟨hgen, hseq0, hseqj⟩ := Hcs
  wp_join (Q := fun r => iprop(
      ((⌜r = executeVal⌝ ∗ ∃ v' : examples.gryffnet.client, cl ↦ v' ∗
          unusedIds γ c (uint.nat v'.gen') ∗ connOk γ c v' ∗
          ⌜uint.nat v'.gen' ≤ uint.nat ops + 1 ∧ v'.seq' = v.seq'⌝ ∗
          «$res0_ptr» ↦ GoInterface.nil) ∨
        (⌜r = returnVal #()⌝ ∗ cl ↦ v ∗ unusedIds γ c (uint.nat v.gen') ∗
          ⌜v.conn' = interface.nil⌝ ∗
          «$res0_ptr» ↦ examples.gryffnet.outV ⟨true, W64 0⟩)) ∗ sys_ptr ↦ sp ∗ cl_ptr ↦ cl))
    at (if: _ then _ else _) with [Hp Hids Hco «$res0» sys cl]
  · icases Hco with (%Hnil | Hco)
    · rw [Hnil]
      wp_auto
      wp_apply (wp_connect γ c sp mu cl v hc (by omega) Hnil hseq0) $$ [Hp Hids] as %b Hb
      · iframe Hp Hids; iframe #
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hb with ⟨Hp, Hids⟩
        wp_auto
        wp_apply wp_unknown as %u %Hu
        subst Hu
        isplitl [Hp Hids «$res0»]
        · iright
          iframe
          ipureintro; trivial
        · iframe
      · simp only [↓reduceIte]
        icases Hb with ⟨%v', Hp, %Hv', Hids, Hco⟩
        wp_auto
        iframe sys cl
        ileft
        isplitr
        · ipureintro; rfl
        iexists v'
        rw [Hv'.1]
        iframe Hp Hids Hco «$res0»
        ipureintro; exact ⟨by omega, Hv'.2⟩
    · ihave ⟨Hco, %Htc⟩ := connOk_conn γ c v $$ Hco
      obtain ⟨tc, Htc⟩ := Htc
      rw [Htc]
      wp_auto
      iframe sys cl
      ileft
      isplitr
      · ipureintro; rfl
      iexists v
      iframe Hp Hids Hco «$res0»
      ipureintro; exact ⟨by omega, rfl⟩
  rename_i r
  iintro ⟨Hr, sys, cl⟩
  icases Hr with (⟨%Hr, %v', Hp, Hids, Hco, %Hv', «$res0»⟩ | ⟨%Hr, Hp, Hids, %Hn, «$res0»⟩)
  rotate_left
  · -- `connect` failed: unknown
    subst Hr
    wp_auto
    iapply HΦ
    isplitl [Hstarted Hops Hp Hids Hbud]
    · iunfold sysSt
      iexists true, (ops + W64 1), v
      iframe Hstarted Hops Hp Hbud
      isplitr
      · ipureintro; omega
      iunfold clientSt
      iframe Hids
      isplitr
      · ipureintro; refine ⟨by omega, hseq0, by omega⟩
      ileft; ipureintro; exact Hn
    iright; ipureintro; rfl
  subst Hr
  wp_auto
  -- the connection's parts
  iunfold connOk at Hco
  icases Hco with ⟨%tc, %cn, %a, %la, %ra, %eof, %ed, %R, %body, %sent, %pend, %r, %Hc, #Hown,
    #Heof, #Hed, Hrd, #Hwok, Hwr, #Hcca, #Hreqs, Hturn⟩
  obtain ⟨Hconn', Ha, Hgen1, Hid, Hsp, Hrr, HR⟩ := Hc
  subst Ha
  ihave ⟨Hwr, #Hcis⟩ := writerRoom_connIs _ _ _ _ _ _ _ _ $$ Hwr
  have hseq' : sint.Z (v'.seq' + W32 1) = sint.Z v'.seq' + 1 := by rw [Hv'.2]; word
  have hhsp : v'.id' < peerMark := by
    rw [Hid]; exact gid_lt_peerMark _ _ hc (by omega)
  -- register the operation (D14: its budget unit)
  ihave #Hpi := Hinv
  iunfold protoInvs at Hpi
  icases Hpi with ⟨#HgI, -⟩
  ihave HAU := slotUpd_opAU γ.proto i Φo $$ HU
  iapply fupd_wp
  imod op_begin (GF := GF) γ.proto (sint.Z v'.id') r (sint.Z (v'.seq' + W32 1))
    (examples.gryffnet.toRI i) _ ⊤ (by intro x _; exact CoPset.subseteq_top x ‹_›) (by omega)
    $$ [Hturn HAU Hb1] with ⟨Hpend, #Hreg⟩
  · iframe Hturn HAU Hb1
    iexact HgI
  imodintro
  have hm := reqMsg_ok v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)
  ihave #Hreqs2 := clientReqsOk_snoc γ v'.id' (v'.seq' + W32 1) (sint.Z v'.seq')
    (examples.gryffnet.toRI i) body _ (by rw [hseq']; omega) (by rw [hseq', Hv'.2]; omega) hm
    $$ [$Hreqs $Hreg]
  ihave #HQm : □ gryffWireP γ (replicaOf c) cn
      (sent ++ pend ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)) $$ []
  · rw [Hsp, List.append_assoc]
    iapply clientStream_ok γ (replicaOf c) cn v'.id' _ _ hhsp $$ [$Hcca $Hreqs2]
  ihave #Hgp : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto $$ []
  · iPkgInit
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  -- the request: its opcode and message, buffered
  wp_join iprop((∃ (sent2 pend2 : List w8) (err2 : GoInterface),
        ⌜err2 = interface.nil → sent2 ++ pend2 = sent ++ pend ++
          reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)⌝ ∗
        wire.ownWriter v'.w' (connWSt tc la ra ed)
          (sendTok (Gg := hG.goose_globalGS) cn false (gryffWireP γ (replicaOf c)))
          (gryffWireP γ (replicaOf c) cn) sent2 pend2 err2) ∗
      w_ptr ↦ v'.w' ∗ req_ptr ↦ (v'.seq' + W32 1) ∗ k_ptr ↦ W64 0 ∗ x_ptr ↦ i ∗ cl_ptr ↦ cl ∗
      cl ↦ { v' with seq' := v'.seq' + W32 1 })
    with [Hwr w req k x cl Hp] as ⟨⟨%sent2, %pend2, %err2, %Hsent2, Hwr⟩, w, req, k, x, cl, Hp⟩
  · -- a Write
    have hri : examples.gryffnet.toRI i = .write i.A' := by
      unfold examples.gryffnet.toRI; rw [if_pos Hif]
    rw [hri]
    ihave #HQc : □ gryffWireP γ (replicaOf c) cn (sent ++ pend ++ [W8 26]) $$ []
    · iapply gryffWireP_prefix γ _ cn _ _ ⟨Write.enc ⟨v'.seq' + W32 1, v'.id', W64 0, i.A', noDepV⟩, by
      simp [reqMsg, gryffWrite]⟩ $$ HQm
    wp_apply (wire.wp_WriteByte_room v'.w' _ _ _ sent pend 1 (W8 26) (Nat.le_refl _)) $$ [$Hwr $HQc]
      as Hwr
    wp_apply wp_noDep as %d %Hd
    subst Hd
    ihave Hwr := wire.writerRoom_own $$ Hwr
    ihave #HQw : □ gryffWireP γ (replicaOf c) cn (sent ++ (pend ++ [W8 26]) ++
        Write.enc ⟨v'.seq' + W32 1, v'.id', W64 0, i.A', noDepV⟩) $$ []
    · rw [show sent ++ (pend ++ [W8 26]) ++ Write.enc ⟨v'.seq' + W32 1, v'.id', W64 0, i.A', noDepV⟩
          = sent ++ pend ++ reqMsg v'.id' (v'.seq' + W32 1) (.write i.A') by
          simp [reqMsg, gryffWrite]]
      iexact HQm
    wp_apply (wire.gryffproto.Write.wp_Marshal «$r0_ptr» (DFrac.own 1)
      ⟨v'.seq' + W32 1, v'.id', W64 0, i.A', noDepV⟩ v'.w' _ _ _ sent (pend ++ [W8 26])
      interface.nil) $$ [$Hwok $Hwr $HQw «$r0»] as ⟨%kk, %sent', %pend', %err', %Hk, -, Hwr⟩
    · iframe «$r0»
    wp_join_done
    iframe w req k x cl Hp
    iexists sent', pend', err'
    iframe Hwr
    ipureintro
    intro he
    obtain ⟨-, hs', -, hkn, -⟩ := Hk
    rw [hs', hkn he, List.take_length]
    simp [reqMsg, gryffWrite]
  · have hne1 := Hif
    wp_if_destruct
    · -- a CAS
      have hri : examples.gryffnet.toRI i = .cas i.A' i.B' := by
        unfold examples.gryffnet.toRI; rw [if_neg hne1, if_pos Hif]
      rw [hri]
      ihave #HQc : □ gryffWireP γ (replicaOf c) cn (sent ++ pend ++ [W8 22]) $$ []
      · iapply gryffWireP_prefix γ _ cn _ _ ⟨RMW.enc ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV, i.A', i.B'⟩, by
        simp [reqMsg, gryffRMW]⟩ $$ HQm
      wp_apply (wire.wp_WriteByte_room v'.w' _ _ _ sent pend 1 (W8 22) (Nat.le_refl _)) $$ [$Hwr $HQc]
        as Hwr
      wp_apply wp_noDep as %d %Hd
      subst Hd
      ihave Hwr := wire.writerRoom_own $$ Hwr
      ihave #HQw : □ gryffWireP γ (replicaOf c) cn (sent ++ (pend ++ [W8 22]) ++
          RMW.enc ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV, i.A', i.B'⟩) $$ []
      · rw [show sent ++ (pend ++ [W8 22]) ++ RMW.enc ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV, i.A', i.B'⟩
            = sent ++ pend ++ reqMsg v'.id' (v'.seq' + W32 1) (.cas i.A' i.B') by
            simp [reqMsg, gryffRMW]]
        iexact HQm
      wp_apply (wire.gryffproto.RMW.wp_Marshal «$r0_ptr» (DFrac.own 1)
        ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV, i.A', i.B'⟩ v'.w' _ _ _ sent (pend ++ [W8 22])
        interface.nil) $$ [$Hwok $Hwr $HQw «$r0»] as ⟨%kk, %sent', %pend', %err', %Hk, -, Hwr⟩
      · iframe «$r0»
      wp_join_done
      iframe w req k x cl Hp
      iexists sent', pend', err'
      iframe Hwr
      ipureintro
      intro he
      obtain ⟨-, hs', -, hkn, -⟩ := Hk
      rw [hs', hkn he, List.take_length]
      simp [reqMsg, gryffRMW]
    · -- a Read
      have hri : examples.gryffnet.toRI i = .read := by
        unfold examples.gryffnet.toRI; rw [if_neg hne1, if_neg Hif]
      rw [hri]
      ihave #HQc : □ gryffWireP γ (replicaOf c) cn (sent ++ pend ++ [W8 24]) $$ []
      · iapply gryffWireP_prefix γ _ cn _ _ ⟨Read.enc ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV⟩, by
        simp [reqMsg, gryffRead]⟩ $$ HQm
      wp_apply (wire.wp_WriteByte_room v'.w' _ _ _ sent pend 1 (W8 24) (Nat.le_refl _)) $$ [$Hwr $HQc]
        as Hwr
      wp_apply wp_noDep as %d %Hd
      subst Hd
      ihave Hwr := wire.writerRoom_own $$ Hwr
      ihave #HQw : □ gryffWireP γ (replicaOf c) cn (sent ++ (pend ++ [W8 24]) ++
          Read.enc ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV⟩) $$ []
      · rw [show sent ++ (pend ++ [W8 24]) ++ Read.enc ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV⟩
            = sent ++ pend ++ reqMsg v'.id' (v'.seq' + W32 1) (.read) by
            simp [reqMsg, gryffRead]]
        iexact HQm
      wp_apply (wire.gryffproto.Read.wp_Marshal «$r0_ptr» (DFrac.own 1)
        ⟨v'.seq' + W32 1, v'.id', W64 0, noDepV⟩ v'.w' _ _ _ sent (pend ++ [W8 24])
        interface.nil) $$ [$Hwok $Hwr $HQw «$r0»] as ⟨%kk, %sent', %pend', %err', %Hk, -, Hwr⟩
      · iframe «$r0»
      wp_join_done
      iframe w req k x cl Hp
      iexists sent', pend', err'
      iframe Hwr
      ipureintro
      intro he
      obtain ⟨-, hs', -, hkn, -⟩ := Hk
      rw [hs', hkn he, List.take_length]
      simp [reqMsg, gryffRead]
  have hdrop : ∀ (w : examples.gryffnet.client), w.gen' = v'.gen' → w.seq' = v'.seq' + W32 1 →
      uint.nat w.gen' ≤ uint.nat (ops + W64 1) ∧ 0 ≤ sint.Z w.seq' ∧
        sint.Z w.seq' ≤ ((uint.nat (ops + W64 1) : Nat) : Int) := by
    intro w hg hs
    rw [hg, hs, hseq', Hv'.2, hops1]
    refine ⟨by omega, by omega, by push_cast; omega⟩
  -- the flush
  wp_apply (wire.wp_Flush v'.w' (connWSt tc la ra ed)
    (sendTok (Gg := hG.goose_globalGS) cn false (gryffWireP γ (replicaOf c)))
    (gryffWireP γ (replicaOf c) cn) sent2 pend2 err2) $$ Hwr as %fe ⟨%kf, %Hkf, Hwr⟩
  cases fe with
  | ok ei =>
    -- the flush failed
    wp_auto
    drop_unknown
    drop_post
  | nil =>
  obtain ⟨-, hk, herr⟩ := Hkf
  have hk := hk rfl
  have herr2 : err2 = interface.nil := by
    cases err2 with
    | nil => rfl
    | ok ei => exact absurd (herr (by simp)).1 (by simp)
  subst hk herr2
  rw [List.take_length, List.drop_length]
  have Hsent3 : sent2 ++ pend2 = u32Le v'.id' ++
      (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)) := by
    rw [Hsent2 rfl, Hsp, List.append_assoc]
  wp_auto
  ihave ⟨Hwr, #Hlb⟩ := wire.ownWriter_sentLb $$ Hwr
  ihave Hwr := wire.ownWriter_room $$ Hwr
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hrok : wire.readerOk (connRSt tc la ra eof ed)
      (recvTokL (Gg := hG.goose_globalGS) cn false (gryffWireQ γ (replicaOf c))) $$ []
  · unfold wire.readerOk; iframe #
  -- the replies
  ihave HL : iprop(∃ R' : List w8, "Hrd" ∷ wire.ownReader v'.r' (connRSt tc la ra eof ed)
      (recvTokL (Gg := hG.goose_globalGS) cn false (gryffWireQ γ (replicaOf c))) R' ∗
      "%HR" ∷ ⌜repliesOk R'⌝) $$ [Hrd]
  · iexists R; iframe Hrd; ipureintro; exact HR
  clear HR R
  wp_for HL
  wp_apply (wire.wp_ReadByte v'.r' (connRSt tc la ra eof ed) _ R') $$ [Hrd] as %cb %rerr Hres
  · iframe Hrd; iframe #
  icases Hres with (⟨%Herr, Hrd⟩ | ⟨%Herr, -, Hrd⟩)
  rotate_left
  · -- the read failed
    rcases rerr with ei | _
    · wp_auto
      drop_unknown
      wp_for_post
      drop_post
    · exact absurd rfl Herr
  subst Herr
  wp_auto
  wp_if_destruct
  · -- a ReadReply
    wp_apply (wire.gryffproto.ReadReply.wp_Unmarshal «$r0_ptr» _ v'.r' (connRSt tc la ra eof ed) _
      (R' ++ [W8 25])) $$ [Hrd «$r0»] as %e2 Hres2
    · iframe Hrd «$r0»; iframe #
      iapply wire.readNext_true _ _ _ _ ReadReply.nextOk (fun _ => trivial)
    icases Hres2 with (⟨%He2, %m, -, Hm, Hrd⟩ | ⟨%He2, -, %vv, %R2, Hm, Hrd⟩)
    rotate_left
    · rcases e2 with ei | _
      · wp_auto
        drop_unknown
        wp_for_post
        drop_post
      · exact absurd rfl He2
    subst He2
    wp_auto_lc 2
    have hsh : replyShape (W8 25 :: ReadReply.enc m) := Or.inl ⟨m, rfl⟩
    have HR2 : repliesOk (R' ++ [W8 25] ++ ReadReply.enc m) := by
      simpa using repliesOk_snoc HR hsh
    wp_if_destruct
    rotate_left
    · skip_loop HR2
    have hA := Hif
    wp_if_destruct
    rotate_left
    · skip_loop HR2
    have hB := Hif
    wp_apply examples.gryffnet.wp_isWrite
    cases hw : examples.gryffnet.isWriteG i
    rotate_left
    · wp_auto
      skip_loop HR2
    have hri : examples.gryffnet.toRI i = .read := by
      unfold examples.gryffnet.isWriteG at hw
      unfold examples.gryffnet.toRI
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hw
      rw [if_neg hw.1, if_neg hw.2]
    wp_auto
    by_cases hok : m.OK' = W8 1
    rotate_left
    · wp_if_destruct
      · exact absurd Hif hok
      drop_unknown
      wp_for_post
      drop_post
    -- the reply: the operation's commit
    ihave #Hlb' : sentLb (Gg := hG.goose_globalGS) cn false (u32Le v'.id' ++
        (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i))) $$ []
    · rw [← Hsent3]; iexact Hlb
    iapply fupd_wp
    imod netN.ownReader_protoNow _ _ _ _ _ _ ⊤ $$ Hrd with ⟨Hrd, #Hpp⟩
    ihave #Hdone := reply_opDone γ (replicaOf c) cn v'.id' (v'.seq' + W32 1) (.value m.V')
      (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)) R'
      (W8 25 :: ReadReply.enc m) hhsp HR hsh (Or.inl ⟨m, m.V', rfl, hA, hB, hok, rfl, rfl⟩)
      $$ [Hlb' Hpp]
    · iframe Hlb'
      rw [show R' ++ W8 25 :: ReadReply.enc m = R' ++ [W8 25] ++ ReadReply.enc m by simp]
      iexact Hpp
    imod op_end (GF := GF) γ.proto (sint.Z v'.id') (sint.Z (v'.seq' + W32 1))
      (examples.gryffnet.toRI i) (.value m.V') _ ⊤ (by intro x _; exact CoPset.subseteq_top x ‹_›)
      $$ [Hpend Hdone] with ⟨HQ, Hturn⟩
    · iframe Hpend Hdone
      iexact HgI
    imod lc_fupd_elim_later $$ Hlc1 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    imodintro
    icases HQ with ⟨%σ, %σ', HQ⟩
    wp_if_destruct
    rotate_left
    · exact absurd hok Hif
    wp_for_post
    ok_post (R' ++ [W8 25] ++ ReadReply.enc m) HR2
  wp_if_destruct
  · -- a WriteReply
    wp_apply (wire.gryffproto.WriteReply.wp_Unmarshal «$r0_ptr» _ v'.r' (connRSt tc la ra eof ed) _
      (R' ++ [W8 27])) $$ [Hrd «$r0»] as %e2 Hres2
    · iframe Hrd «$r0»; iframe #
      iapply wire.readNext_true _ _ _ _ WriteReply.nextOk (fun _ => trivial)
    icases Hres2 with (⟨%He2, %m, -, Hm, Hrd⟩ | ⟨%He2, -, %vv, %R2, Hm, Hrd⟩)
    rotate_left
    · rcases e2 with ei | _
      · wp_auto
        drop_unknown
        wp_for_post
        drop_post
      · exact absurd rfl He2
    subst He2
    wp_auto_lc 2
    have hsh : replyShape (W8 27 :: WriteReply.enc m) := Or.inr (Or.inl ⟨m, rfl⟩)
    have HR2 : repliesOk (R' ++ [W8 27] ++ WriteReply.enc m) := by
      simpa using repliesOk_snoc HR hsh
    wp_if_destruct
    rotate_left
    · skip_loop HR2
    have hA := Hif
    wp_if_destruct
    rotate_left
    · skip_loop HR2
    have hB := Hif
    wp_if_destruct
    rotate_left
    · skip_loop HR2
    try wp_auto
    by_cases hok : m.OK' = W8 1
    rotate_left
    · wp_if_destruct
      · exact absurd Hif hok
      drop_unknown
      wp_for_post
      drop_post
    -- the reply: the operation's commit
    ihave #Hlb' : sentLb (Gg := hG.goose_globalGS) cn false (u32Le v'.id' ++
        (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i))) $$ []
    · rw [← Hsent3]; iexact Hlb
    iapply fupd_wp
    imod netN.ownReader_protoNow _ _ _ _ _ _ ⊤ $$ Hrd with ⟨Hrd, #Hpp⟩
    ihave #Hdone := reply_opDone γ (replicaOf c) cn v'.id' (v'.seq' + W32 1) .done
      (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)) R'
      (W8 27 :: WriteReply.enc m) hhsp HR hsh (Or.inr (Or.inl ⟨m, rfl, hA, hB, hok, rfl⟩))
      $$ [Hlb' Hpp]
    · iframe Hlb'
      rw [show R' ++ W8 27 :: WriteReply.enc m = R' ++ [W8 27] ++ WriteReply.enc m by simp]
      iexact Hpp
    imod op_end (GF := GF) γ.proto (sint.Z v'.id') (sint.Z (v'.seq' + W32 1))
      (examples.gryffnet.toRI i) .done _ ⊤ (by intro x _; exact CoPset.subseteq_top x ‹_›)
      $$ [Hpend Hdone] with ⟨HQ, Hturn⟩
    · iframe Hpend Hdone
      iexact HgI
    imod lc_fupd_elim_later $$ Hlc1 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    imodintro
    icases HQ with ⟨%σ, %σ', HQ⟩
    wp_if_destruct
    rotate_left
    · exact absurd hok Hif
    wp_for_post
    ok_post (R' ++ [W8 27] ++ WriteReply.enc m) HR2
  wp_if_destruct
  · -- a RMWReply
    wp_apply (wire.gryffproto.RMWReply.wp_Unmarshal «$r0_ptr» _ v'.r' (connRSt tc la ra eof ed) _
      (R' ++ [W8 23])) $$ [Hrd «$r0»] as %e2 Hres2
    · iframe Hrd «$r0»; iframe #
      iapply wire.readNext_true _ _ _ _ RMWReply.nextOk (fun _ => trivial)
    icases Hres2 with (⟨%He2, %m, -, Hm, Hrd⟩ | ⟨%He2, -, %vv, %R2, Hm, Hrd⟩)
    rotate_left
    · rcases e2 with ei | _
      · wp_auto
        drop_unknown
        wp_for_post
        drop_post
      · exact absurd rfl He2
    subst He2
    wp_auto_lc 2
    have hsh : replyShape (W8 23 :: RMWReply.enc m) := Or.inr (Or.inr ⟨m, rfl⟩)
    have HR2 : repliesOk (R' ++ [W8 23] ++ RMWReply.enc m) := by
      simpa using repliesOk_snoc HR hsh
    wp_if_destruct
    rotate_left
    · skip_loop HR2
    have hA := Hif
    wp_if_destruct
    rotate_left
    · skip_loop HR2
    try wp_auto
    by_cases hok : m.OK' = W8 1
    rotate_left
    · wp_if_destruct
      · exact absurd Hif hok
      drop_unknown
      wp_for_post
      drop_post
    -- the reply: the operation's commit
    ihave #Hlb' : sentLb (Gg := hG.goose_globalGS) cn false (u32Le v'.id' ++
        (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i))) $$ []
    · rw [← Hsent3]; iexact Hlb
    iapply fupd_wp
    imod netN.ownReader_protoNow _ _ _ _ _ _ ⊤ $$ Hrd with ⟨Hrd, #Hpp⟩
    ihave #Hdone := reply_opDone γ (replicaOf c) cn v'.id' (v'.seq' + W32 1) .done
      (body ++ reqMsg v'.id' (v'.seq' + W32 1) (examples.gryffnet.toRI i)) R'
      (W8 23 :: RMWReply.enc m) hhsp HR hsh (Or.inr (Or.inr ⟨m, rfl, hA, hok, rfl⟩))
      $$ [Hlb' Hpp]
    · iframe Hlb'
      rw [show R' ++ W8 23 :: RMWReply.enc m = R' ++ [W8 23] ++ RMWReply.enc m by simp]
      iexact Hpp
    imod op_end (GF := GF) γ.proto (sint.Z v'.id') (sint.Z (v'.seq' + W32 1))
      (examples.gryffnet.toRI i) .done _ ⊤ (by intro x _; exact CoPset.subseteq_top x ‹_›)
      $$ [Hpend Hdone] with ⟨HQ, Hturn⟩
    · iframe Hpend Hdone
      iexact HgI
    imod lc_fupd_elim_later $$ Hlc1 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    imodintro
    icases HQ with ⟨%σ, %σ', HQ⟩
    wp_if_destruct
    rotate_left
    · exact absurd hok Hif
    wp_for_post
    ok_post (R' ++ [W8 23] ++ RMWReply.enc m) HR2
  -- another opcode: the stream cannot be read on
  drop_unknown
  wp_for_post
  drop_post

end op

end Perennial.gryff
