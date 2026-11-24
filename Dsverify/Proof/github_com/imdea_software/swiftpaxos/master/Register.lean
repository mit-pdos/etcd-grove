/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Register.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`m.Register(args, reply)` (internal spec and proof): the riskiest step of the master group,
the lock invariant `master.lockInv` with the write-once membership.
-/
module

public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Addr
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Printf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.RegisterDefs
public import Proof.fmt.SprintfPure
public import Perennial.Proof.fmt.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
  Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions]

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [dlog.Assumptions]

set_option maxHeartbeats 4000000 in
theorem master.Master.Register.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    master.Master.Register.spec := fun m γc γm N args reply ip port cc k rv => by
  wp_start as ⟨#Hm, Hargs, Hreply, #Hc, %Hk⟩
  unfold master.isMaster
  iNamed Hm
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  unfold master.lockInv
  iNamed HR
  icases master.lists_read $$ Hlists with ⟨%dq, HnlF, Hnl, Hback⟩
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #ip, interface.mkOk go.int #port]
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_auto
  wp_apply _root_.Perennial.EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%s:%d"
      [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      _ _ _ _ (by fmt_encode) (by fmt_fits) (.str _ _ _ (.int _ _ _ _
      (.int port) .nil)) $$ [$Hasl] as %str ⟨-, %Hs⟩
  have Hs := master.sprintf_str_d ip port str Hs
  ihave %Hcc := confIs_agree γc cc c $$ [Hc Hconf]
  · iframe Hc Hconf
  subst Hcc
  obtain ⟨hk5, hip, hport⟩ := master.addrPort_replica Hk.1
  rw [master.decimal_addrPort ip port (by subst hport; word)] at Hs
  subst Hs
  ipersist master
  ipersist args
  ipersist reply
  ipersist addrPort
  rename_i key_ptr
  irename : (key_ptr ↦ Perennial.zero_val w64 : IProp netDistGF) => ikey
  ihave %Hnllen := ownSlice_len _ _ _ $$ Hnl
  -- the search: `index` is the caller's position, or `nlen` if absent
  wp_join iprop(∃ idx : w64, "index" ∷ index_ptr ↦ idx ∗ "Hnl" ∷ nl ↦*{dq} nodes ∗
      "%Hidx" ∷ ⌜(0 ≤ sint.Z idx ∧ nodes[sint.nat idx]? = some (sp.addrPort ip port)) ∨
        (idx = nl.len ∧ sp.addrPort ip port ∉ nodes)⌝)
    at next with [index Hnl i ikey ap] as ⟨%idx, index, Hnl, %Hidx⟩
  · ihave HI : (∃ (j kv : w64) (apv : GoString),
        "i" ∷ i_ptr ↦ j ∗ "ikey" ∷ key_ptr ↦ kv ∗ "ap" ∷ ap_ptr ↦ apv ∗
        "index" ∷ index_ptr ↦ nl.len ∗ "Hnl" ∷ nl ↦*{dq} nodes ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nl.len ∧
          sp.addrPort ip port ∉ nodes.take (sint.nat j)⌝ : IProp netDistGF) $$ [i ikey ap index Hnl]
    · iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp
    wp_for HI
    wp_if_destruct
    · have Hlt : sint.nat j < nodes.length := by word
      list_elem nodes (sint.nat j) as x
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nl.len from ⟨Hj.1, Hif⟩, _root_.and_self,
        ↓reduceIte]
      wp_apply wp_load_slice_index nl (sint.Z j) nodes dq x Hj.1 $$ [Hnl] as Hnl
      · iframe; ipureintro; rw [show (sint.Z j).toNat = sint.nat j from rfl]; exact Hx_lookup
      wp_if_destruct
      · wp_for_post
        iframe
        ipureintro
        exact ⟨rfl, Or.inl ⟨Hj.1, Hx_lookup⟩⟩
      · wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
        exact ⟨Hj.2.2, fun h => Hif (by rw [h])⟩
    · iframe
      ipureintro
      refine Or.inr ⟨rfl, ?_⟩
      have := Hj.2.2
      rwa [List.take_of_length_le (by word)] at this
  -- back to the registrations' resources
  ihave Hlists := Hback $$ HnlF Hnl
  have hmem : sp.addrPort ip port ∈ replicaAddrs.take N := by
    rw [← HN.1]
    exact List.mem_iff_getElem?.mpr ⟨k, by rw [List.getElem?_take_of_lt Hk.2]; exact Hk.1⟩
  -- the registration (the caller's address added if absent)
  wp_join iprop(∃ (nl al pl : GoSlice) (nodes addrs : List GoString) (ports : List w64)
      (leaders : List Bool) (lats : List w64) (nlen idx : w64),
      nlen_ptr ↦ nlen ∗ index_ptr ↦ idx ∗
      master.lists m γm N nl al pl nodes addrs ports ∗
      leaderS ↦* leaders ∗ latS ↦* lats ∗
      args ↦ replica.defs.RegisterArgs.mk ip port ∗
      ⌜master.regOk N nodes addrs ports ∧ leaders.length = N ∧ lats.length = N ∧
        sint.nat nlen = nodes.length ∧ 0 ≤ sint.Z nlen ∧ 0 ≤ sint.Z idx ∧
        nodes[sint.nat idx]? = some (sp.addrPort ip port) ∧ (fi = true → nodes.length = N)⌝)
    with [nlen index Hlists Hleaders Hlats Hargs]
    as ⟨%nl', %al', %pl', %nodes', %addrs', %ports', %leaders', %lats', %nlen', %idx', nlen,
      index, Hlists, Hleaders, Hlats, Hargs, %Hr⟩
  · -- absent: appended
    have Hnot : sp.addrPort ip port ∉ nodes := by
      rcases Hidx with h | h
      · rw [List.getElem?_eq_none (by word)] at h
        cases h.2
      · exact h.2
    have hlt := master.regOk_lt Hwf.1 hmem Hnot
    unfold master.lists
    rw [if_neg (by omega)]
    icases Hlists with ⟨HnlF, HalF, HplF, Hnl, Hal, Hpl, Hcnl, Hcal, Hcpl, %Hcaps, Hauth⟩
    ihave %Hallen := ownSlice_len _ _ _ $$ Hal
    ihave %Hpllen := ownSlice_len _ _ _ $$ Hpl
    obtain ⟨hal, hpl, -, -, -, -⟩ := Hwf.1
    have hNz : sint.Z (W64 (N : Int)) = N := by
      have := HN.2; word
    have hnl : sint.Z nl.len < sint.Z nl.cap := by rw [Hcaps.1, hNz]; word
    have hal' : sint.Z al.len < sint.Z al.cap := by rw [Hcaps.2.1, hNz]; word
    have hpl' : sint.Z pl.len < sint.Z pl.cap := by rw [Hcaps.2.2, hNz]; word
    have heqa : al.len = nl.len := by word
    have heqp : pl.len = nl.len := by word
    have hc1 : sint.Z nl.cap = N := by rw [Hcaps.1, hNz]
    have hc2 : sint.Z al.cap = N := by rw [Hcaps.2.1, hNz]
    have hc3 : sint.Z pl.cap = N := by rw [Hcaps.2.2, hNz]
    have hreg := master.regOk_snoc Hwf.1 hmem Hnot
    iapply fupd_wp
    imod master.write_if γm (nodes ++ [sp.addrPort ip port]) (nodes.length + 1 = N)
      ⟨hreg.2.2.2.2.1, fun a ha => List.mem_of_mem_take (hreg.2.2.2.2.2 a ha)⟩ $$ Hauth with HW
    imodintro
    icases master.slice_extend nl nodes hnl $$ [$Hnl $Hcnl] with ⟨%y1, Hnl, Hcnl⟩
    icases master.slice_extend al addrs hal' $$ [$Hal $Hcal] with ⟨%y2, Hal, Hcal⟩
    icases master.slice_extend pl ports hpl' $$ [$Hpl $Hcpl] with ⟨%y3, Hpl, Hcpl⟩
    wp_auto
    rw [if_pos (master.bounds_ext _ _ Hnllen.2 hnl)]
    wp_auto
    rw [if_pos (master.bounds_last _ _ Hnllen.2 hnl)]
    wp_apply wp_store_slice_index $$ [$Hnl] as Hnl
    · ipureintro; simp; word
    rw [master.set_last _ _ _ _ (by word), heqa, heqp]
    rw [heqa] at hal'
    rw [heqp] at hpl'
    rw [if_pos (master.bounds_ext _ _ Hnllen.2 hal')]
    wp_auto
    rw [if_pos (master.bounds_last _ _ Hnllen.2 hal')]
    wp_apply wp_store_slice_index $$ [$Hal] as Hal
    · ipureintro; simp; word
    rw [master.set_last _ _ _ _ (by word)]
    rw [if_pos (master.bounds_ext _ _ Hnllen.2 hpl')]
    wp_auto
    rw [if_pos (master.bounds_last _ _ Hnllen.2 hpl')]
    wp_apply wp_store_slice_index $$ [$Hpl] as Hpl
    · ipureintro; simp; word
    rw [master.set_last _ _ _ _ (by word)]
    ihave %Hldlen := ownSlice_len _ _ _ $$ Hleaders
    ihave %Hltlen := ownSlice_len _ _ _ $$ Hlats
    have hld : sint.Z nl.len < sint.Z leaderS.len := by
      have := Hwf.2.1; word
    have hlt' : sint.Z nl.len < sint.Z latS.len := by
      have := Hwf.2.2.2.1; word
    rw [if_pos (show 0 ≤ sint.Z nl.len ∧ sint.Z nl.len < sint.Z leaderS.len from ⟨Hnllen.2, hld⟩)]
    wp_apply wp_store_slice_index $$ [$Hleaders] as Hleaders
    · ipureintro; word
    rw [if_pos (show 0 ≤ sint.Z nl.len ∧ sint.Z nl.len < sint.Z latS.len from ⟨Hnllen.2, hlt'⟩)]
    wp_apply wp_store_slice_index $$ [$Hlats] as Hlats
    · ipureintro; word
    rw [if_pos (master.bounds_last _ _ Hnllen.2 hnl)]
    wp_apply wp_load_slice_index _ (sint.Z nl.len) _ _ (sp.addrPort ip port) (by word) $$ [Hnl]
      as Hnl
    · iframe; ipureintro
      rw [List.getElem?_append_right (by word), show (sint.Z nl.len).toNat - nodes.length = 0 by word]
      rfl
    rw [if_pos (show 0 ≤ sint.Z nl.len ∧ sint.Z nl.len < sint.Z latS.len from ⟨Hnllen.2, hlt'⟩)]
    wp_apply wp_load_slice_index _ (sint.Z nl.len) _ _ (W64 0) (by word) $$ [Hlats] as Hlats
    · iframe; ipureintro
      rw [List.getElem?_set_self (by word)]
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.int #nl.len, interface.mkOk go.string #(sp.addrPort ip port),
        interface.mkOk go.float64 #(W64 0)]
    isplitr
    · ipureintro; rfl
    iintro %psl ⟨-, -⟩
    wp_auto
    iapply wp_fupd
    wp_apply master.wp_Printf wp_Printf $$ [$Hlg $Hquiet]
    have hpure : master.regOk N (nodes ++ [sp.addrPort ip port]) (addrs ++ [ip]) (ports ++ [port]) ∧
        (leaders.set (sint.Z nl.len).toNat false).length = N ∧
        (lats.set (sint.Z nl.len).toNat (W64 0)).length = N ∧
        sint.nat (nl.len + W64 1) = (nodes ++ [sp.addrPort ip port]).length ∧
        0 ≤ sint.Z (nl.len + W64 1) ∧ 0 ≤ sint.Z nl.len ∧
        (nodes ++ [sp.addrPort ip port])[sint.nat nl.len]? = some (sp.addrPort ip port) ∧
        (fi = true → (nodes ++ [sp.addrPort ip port]).length = N) := by
      refine ⟨hreg, by simp [Hwf.2.1], by simp [Hwf.2.2.2.1], ?_, by word, Hnllen.2, ?_, ?_⟩
      · simp; word
      · rw [List.getElem?_append_right (by word), show sint.nat nl.len - nodes.length = 0 by word]
        rfl
      · intro hfi; have := Hwf.2.2.2.2 hfi; omega
    by_cases hfull : nodes.length + 1 = N
    · rw [if_pos hfull]
      ipersist HnlF
      ipersist HalF
      ipersist HplF
      ipersist Hnl
      ipersist Hal
      ipersist Hpl
      ihave Hlists := master.lists_full m γm N _ _ _ _ _ _ (by simp; omega) $$ HnlF HalF HplF Hnl
        Hal Hpl HW
      imodintro
      isplitr
      · ipureintro; rfl
      iexists (slice.slice nl GoString (W64 0) (nl.len + W64 1)),
        (slice.slice al GoString (W64 0) (nl.len + W64 1)),
        (slice.slice pl w64 (W64 0) (nl.len + W64 1)), nodes ++ [sp.addrPort ip port],
        addrs ++ [ip], ports ++ [port], leaders.set (sint.Z nl.len).toNat false,
        lats.set (sint.Z nl.len).toNat (W64 0), nl.len + W64 1, nl.len
      unfold master.lists
      iframe
      ipureintro
      exact hpure
    · rw [if_neg hfull]
      ihave Hlists := master.lists_partial m γm N _ _ _ _ _ _ (by simp; omega)
        (by simp only [slice.slice]; refine ⟨?_, ?_, ?_⟩ <;> word) $$ HnlF HalF HplF Hnl
        Hal Hpl Hcnl Hcal Hcpl HW
      imodintro
      isplitr
      · ipureintro; rfl
      iexists (slice.slice nl GoString (W64 0) (nl.len + W64 1)),
        (slice.slice al GoString (W64 0) (nl.len + W64 1)),
        (slice.slice pl w64 (W64 0) (nl.len + W64 1)), nodes ++ [sp.addrPort ip port],
        addrs ++ [ip], ports ++ [port], leaders.set (sint.Z nl.len).toNat false,
        lats.set (sint.Z nl.len).toNat (W64 0), nl.len + W64 1, nl.len
      unfold master.lists
      iframe
      ipureintro
      exact hpure
  · -- present: unchanged
    rcases Hidx with Hidx | Hidx
    · iframe
      ipureintro
      exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.2.1, by word, by word, Hidx.1, Hidx.2, Hwf.2.2.2.2⟩
    · exact absurd Hidx.1 Hif
  -- the reply
  ipersist index
  wp_join iprop(∃ (rv' : replica.defs.RegisterReply) (leaders2 : List Bool),
      reply ↦ rv' ∗ leaderS ↦* leaders2 ∗ latS ↦* lats' ∗
      master.lists m γm N nl' al' pl' nodes' addrs' ports' ∗
      ⌜leaders2.length = N⌝ ∗
      (if rv'.Ready' then ∃ nodes : List GoString, rv'.NodeList' ↦*□ nodes ∗
          (∃ fr, sp.cfg γc γm nodes.length fr nodes) ∗
          ⌜nodes[rv'.ReplicaId'.toNat]? = some (sp.addrPort ip port)⌝
        else ⌜rv' = { rv with Ready' := false }⌝))
    with [Hreply Hleaders Hlats Hlists]
    as ⟨%rv', %leaders2, Hreply, Hleaders, Hlats, Hlists, %Hl2, Hrep⟩
  · -- ready
    have hfull : nodes'.length = N := by
      have := Hr.2.2.2.1; have := HN.2; word
    ihave Hl := Hlists
    unfold master.lists
    rw [if_pos hfull]
    icases Hl with ⟨#HnlF, #HalF, #HplF, #Hnl, #Hal, #Hpl, #Hmem⟩
    wp_auto
    unfold config.plain
    icases Hplain with ⟨%cv, %pi, #Hcv, -, %Hcvp⟩
    iStructNamed Hcv
    rw [Hcvp.2.2.2.1]
    wp_auto
    ihave %Hltl := ownSlice_len _ _ _ $$ Hlats
    ihave %Hldl := ownSlice_len _ _ _ $$ Hleaders
    have hN := HN.2
    ihave HI : (∃ (j f ld : w64), "i" ∷ i_ptr ↦ j ∗ "minLatency" ∷ minLatency_ptr ↦ f ∗
        "leader" ∷ leader_ptr ↦ ld ∗ "Hlats" ∷ latS ↦* lats' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z leaderS.len⌝ : IProp netDistGF)
      $$ [i minLatency leader Hlats]
    · iexists _, _, _
      iframe
      ipureintro; word
    wp_for HI
    wp_if_destruct
    · have hj : (sint.Z j).toNat < lats'.length := by have := Hr.2.2.1; word
      list_elem lats' (sint.Z j).toNat as lj
      rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z latS.len by have := Hr.2.2.1; word)]
      wp_apply wp_load_slice_index _ (sint.Z j) _ _ lj Hj.1 $$ [Hlats] as Hlats
      · iframe; ipureintro; exact Hlj_lookup
      generalize (float64Leb lj f && !float64Eq lj f) = blt
      cases blt
      · wp_auto
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro; word
      · wp_auto
        rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z latS.len by have := Hr.2.2.1; word)]
        wp_apply wp_load_slice_index _ (sint.Z j) _ _ lj Hj.1 $$ [Hlats] as Hlats
        · iframe; ipureintro; exact Hlj_lookup
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro; word
    · have hidx : sint.Z idx' < sint.Z leaderS.len := by
        have := Hr.2.2.2.2.2.2.1
        have h2 : sint.nat idx' < nodes'.length := (List.getElem?_eq_some_iff.mp this).1
        have := Hr.2.1; word
      have hcfg : ∃ fr, True := ⟨true, trivial⟩
      ihave #Hcfg := sp.cfg_intro (γc := γc) (γm := γm) cc nodes' $$ [$Hconf $Hmem]
      · ipureintro; exact ⟨by rw [hfull, HN.1], by rw [HN.1]; exact master.regOk_nodeOf Hr.1⟩
      wp_if_destruct
      · rw [if_pos (show 0 ≤ sint.Z idx' ∧ sint.Z idx' < sint.Z leaderS.len from ⟨Hr.2.2.2.2.2.1, hidx⟩)]
        wp_apply wp_store_slice_index $$ [$Hleaders] as Hleaders
        · ipureintro; word
        isplitr
        · ipureintro; trivial
        iexists _, _
        iframe
        simp only [↓reduceIte]
        isplitr
        · iframe HnlF HalF HplF Hnl Hal Hpl Hmem
        isplitr
        · ipureintro; simp [Hr.2.1]
        iexists nodes'
        iframe Hnl
        isplitr
        · iexists _; rw [hfull, ← HN.1]; iexact Hcfg
        ipureintro
        have := Hr.2.2.2.2.2.2.1
        rwa [show sint.nat idx' = idx'.toNat by have := Hr.2.2.2.2.2.1; word] at this
      · isplitr
        · ipureintro; trivial
        iexists _, _
        iframe
        simp only [↓reduceIte]
        isplitr
        · iframe HnlF HalF HplF Hnl Hal Hpl Hmem
        isplitr
        · ipureintro; exact Hr.2.1
        iexists nodes'
        iframe Hnl
        isplitr
        · iexists _; rw [hfull, ← HN.1]; iexact Hcfg
        ipureintro
        have := Hr.2.2.2.2.2.2.1
        rwa [show sint.nat idx' = idx'.toNat by have := Hr.2.2.2.2.2.1; word] at this
  · -- not ready
    iexists _, leaders'
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    exact ⟨Hr.2.1, trivial⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
  · inext
    iexists nl', al', pl', nodes', addrs', ports', leaders2, alive, lats', fi
    iframe
    ipureintro
    exact ⟨Hr.1, Hl2, Hwf.2.2.1, Hr.2.2.1, Hr.2.2.2.2.2.2.2⟩
  iapply HΦ
  iexists rv'
  iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
