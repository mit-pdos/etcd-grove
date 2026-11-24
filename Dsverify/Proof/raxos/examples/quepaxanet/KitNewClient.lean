/-
`newClient(addrs, cfgs, c, false)` (`kit.go`), client machine `c`'s QuePaxa client (the lab's
`Kit/NewClient.lean`, re-based): it waits for the configuration (`awaitConf` on its configuration
address), makes its `Sys` with one `replica` per replica of the configuration (`replica_init`) and
the lock invariant `sysInv` from its share `clientRes` (the registry counter's half at 0, its
tickets, `ticketsOf_perm`), listens at its address (retrying), starts `accept` and connects to
every replica (retrying). The library specs are parameters.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitOp

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure raxos.msg

theorem clientAddr_port (c : Nat) : portAddr (7600 + (1 + c)) = clientAddr c := by
  unfold clientAddr; congr 1; omega

theorem proxyAddr_port (k : Nat) : portAddr (7600 + (6 + k)) = proxyAddr k := by
  unfold proxyAddr; congr 1; omega

theorem nc_idx (j : w64) (asl : GoSlice) (hj1 : 1 ≤ uint.nat j) (hj5 : uint.nat j ≤ 5)
    (hl : 12 = sint.nat asl.len) (hl0 : 0 ≤ sint.Z asl.len) :
    (0 ≤ sint.Z (W64 6 + j) ∧ sint.Z (W64 6 + j) < sint.Z asl.len) ∧
      (sint.Z (W64 6 + j)).toNat = 6 + uint.nat j := by
  constructor
  · constructor <;> word
  · word

theorem one_c_idx (c : Nat) (hc : c < 6) (asl : GoSlice) (hl : 12 = sint.nat asl.len)
    (hl0 : 0 ≤ sint.Z asl.len) :
    (0 ≤ sint.Z (W64 1 + W64 (c : Int)) ∧ sint.Z (W64 1 + W64 (c : Int)) < sint.Z asl.len) ∧
      (sint.Z (W64 1 + W64 (c : Int))).toNat = 1 + c := by
  constructor
  · constructor <;> word
  · word

theorem name_w64 [GooseExts] (c : Nat) : W64 21 + W64 (c : Int) = W64 ((21 + c : Nat) : Int) := by
  word

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Client `c`'s address carries the client port's protocols. -/
theorem clientProto_of_shared (γ : QNames) (c : Nat) (hc : c < 6) :
    sharedRes (GF := GF) γ ⊢ addrProto (clientAddr c) (clientInProto γ c) silentProto := by
  unfold sharedRes netProtos
  iintro ⟨-, -, ⟨-, -, #Hcs, -⟩, -⟩
  iapply (BigSepL.bigSepL_mem (Φ := fun c : Nat => addrProto (Gg := Gg) (clientAddr c)
    (clientInProto (GF := GF) γ c) silentProto) (List.mem_range.2 hc))
  iexact Hcs

end ghost

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj] [_root_.Perennial.bufio.Assumptions]
variable [_root_.Perennial.io.Assumptions] [time.Assumptions]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions] [pb : hyp.PbHyp GF]
variable [QpBufioDeps GF]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

theorem wp_newClient (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specOk (GF := GF) (hG := hG))
    (γ : QNames) (c : Nat) (hc : c < 6) (asl csl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ clientRes γ c ∗ asl ↦*□ addrsL ∗ csl ↦*□ cfgAddrsL }}
      (App (App (App (App (Val (@! raxos.examples.quepaxanet.newClient)) (Val #asl)) (Val #csl))
        (Val #(W64 (c : Int)))) (Val #false))
    {{ (s : Loc), RET #s; isSysL γ c s }} := by
  wp_start as ⟨Hres, #Hasl, #Hcsl⟩
  unfold clientRes
  icases Hres with ⟨Hcnt, Htix, #Hsh⟩
  wp_auto
  wp_apply (wp_make_bag1 (confP γ)) as %ch ⟨%γc, #Hch⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
  have hidx : 0 ≤ sint.Z (W64 1 + W64 (c : Int)) ∧ sint.Z (W64 1 + W64 (c : Int)) < sint.Z csl.len := by
    simp [cfgAddrsL] at Hcl; constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hidx)]
  wp_apply wp_load_slice_index csl (sint.Z (W64 1 + W64 (c : Int))) cfgAddrsL _
    (portAddr (7640 + (1 + c))) hidx.1 $$ [Hcsl] as -
  · iframe Hcsl; ipureintro
    rw [show (sint.Z (W64 1 + W64 (c : Int))).toNat = 1 + c by word]
    exact cfgAddrsL_get _ (by omega)
  ihave #Hpr := confProto_of_shared γ (1 + c) (by omega) $$ Hsh
  wp_apply wp_fork $$ []
  · wp_apply wp_awaitConf_of wp_Listen wp_Accept wp_Read wp_Write wp_Close wp_ReadFull γ _ ch γc
      $$ [$Hpkg $Hpr $Hch]
    itrivial
  wp_apply (wp_bag_receive γc ch (confP γ)) $$ [$Hch] as %v Hv
  unfold confP
  icases Hv with ⟨%cf, ⟨%Hv, %hcf⟩, -⟩
  subst Hv
  wp_apply wp_registerProto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string _) as %wm Hwm
  wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string _) as %am Ham
  irename conf => Hconf
  irename c => Hcv
  irename s => Hs
  irename «$r0» => Hsys
  icases typedPointsto_split _ _ _ $$ Hsys with Hsys
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hsys with ⟨conf, c, name, checks, mu, waiting, answered, replicas, next, -⟩
  have hn : cf.n = 3 ∨ cf.n = 5 := hcf.1
  ihave HI : (∃ (j : w64) (rsl : GoSlice) (rls : List Loc), "i" ∷ i_ptr ↦ j ∗
      "replicas" ∷ structFieldRef raxos.examples.quepaxanet.Sys go!"replicas" «$r0_ptr» ↦ rsl ∗
      "Hrsl" ∷ rsl ↦* rls ∗ "Hcap" ∷ ownSliceCap Loc rsl (DFrac.own 1) ∗
      "Hreps" ∷ repsOk γ c rls ∗ "%Hj" ∷ ⌜uint.nat j = rls.length + 1 ∧ rls.length ≤ cf.n⌝ :
      IProp GF) $$ [i replicas]
  · iexists W64 1, slice.nil, []
    iframe i replicas
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · unfold repsOk; iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  ihave %Hal := ownSlice_len _ _ _ $$ Hasl
  have hal : addrsL.length = 12 := rfl
  wp_for HI
  wp_if_destruct
  · have hj1 : 1 ≤ uint.nat j := by omega
    have hjn : uint.nat j ≤ cf.n := by
      have h' : uint.Z (W64 (cf.n : Int)) = cf.n := by rcases hn with h | h <;> rw [h] <;> rfl
      rw [h'] at Hif; word
    have hj5 : uint.nat j ≤ 5 := by omega
    obtain ⟨hidx, hidx'⟩ := nc_idx j asl hj1 hj5 (by rw [← hal]; exact Hal.1) Hal.2
    rw [ite_eq_left_of_eq_true _ _ (eq_true hidx)]
    rw [name_w64 c]
    wp_apply wp_load_slice_index asl (sint.Z (W64 6 + j)) addrsL _ (proxyAddr (uint.nat j)) hidx.1
      $$ [Hasl] as -
    · iframe Hasl; ipureintro
      rw [hidx', addrsL_get _ (by omega), proxyAddr_port]
    imod replica_init γ c (uint.nat j) hc ⟨hj1, hj5⟩ «$sl0_ptr» $$ «$sl0» Hsh with #Hrep
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply (wp_slice_append (V := Loc) rsl rls _ [«$sl0_ptr»] (DFrac.own 1)) $$ [Hrsl Hcap Hsl]
      as %rsl' ⟨Hrsl, Hcap, -⟩
    · iframe Hrsl Hcap Hsl
    wp_for_post
    iframe
    iexists j + W64 1, rsl', rls ++ [«$sl0_ptr»]
    iframe Hrsl Hcap i replicas
    isplitl [Hreps]
    · unfold repsOk
      iapply BigSepL.bigSepL_snoc.2
      iframe Hreps
      rw [show rls.length + 1 = uint.nat j by omega]
      iexact Hrep
    ipureintro
    simp only [List.length_append, List.length_singleton]
    constructor
    · word
    · omega
  · have hlen : rls.length = cf.n := by
      have h' : uint.Z (W64 (cf.n : Int)) = cf.n := by rcases hn with h | h <;> rw [h] <;> rfl
      rw [h'] at Hif
      have h1 : uint.Z j = (rls.length : Int) + 1 := by have := Hj.1; word
      have := Hj.2
      omega
    rw [name_w64 c]
    ipersist name
    ipersist c
    ipersist checks
    ipersist replicas
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hrsl with #Hrsl
    ihave Htix := (BigSepL.bigSepL_perm (ticketsOf_perm c)).1 $$ Htix
    imod sync.init_Mutex (sysInv γ c «$r0_ptr») ⊤ _ $$ mu [waiting Hwm next Hcnt Htix] with #Hmu
    · inext
      unfold sysInv ticketsFrom waitChans
      iexists wm, ∅, 0
      iframe waiting Hwm Htix
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; iempintro
      isplitl [next]
      · iExactEq next; rfl
      isplitr
      · ipureintro; omega
      unfold cntHalf; iexact Hcnt
    ihave #Hsys : isSysL γ c «$r0_ptr» $$ [Hreps]
    · unfold isSysL sysFields
      iexists rsl, rls
      iframe name c checks replicas Hrsl Hmu Hsh
      isplitl []
      · ipureintro; exact ⟨hc, by omega⟩
      iexact Hreps
    imodintro
    obtain ⟨hidx2, hidx2'⟩ := one_c_idx c hc asl (by rw [← hal]; exact Hal.1) Hal.2
    rw [ite_eq_left_of_eq_true _ _ (eq_true hidx2)]
    wp_apply wp_load_slice_index asl (sint.Z (W64 1 + W64 (c : Int))) addrsL _ (clientAddr c)
      hidx2.1 $$ [Hasl] as -
    · iframe Hasl; ipureintro
      rw [hidx2', addrsL_get _ (by omega), clientAddr_port]
    ihave #Hcp := clientProto_of_shared γ c hc $$ Hsh
    ihave %Hok := addrTok_ok (clientAddr c) $$ [Hcp]
    · iapply addrProto_tok $$ Hcp
    have wp_L := net.Listen.spec_addrOk wp_Listen
    wp_apply wp_L go!"tcp" net.tcpNet_tcp (clientAddr c) as %li %err Hres
    · isplitr
      · ipureintro; exact Hok
      iapply listen_au $$ Hcp
    ihave HLs : (∃ (lv' err' : GoInterface), "l" ∷ l_ptr ↦ lv' ∗ "err" ∷ err_ptr ↦ err' ∗
        "Hl" ∷ ((⌜err' = interface.nil⌝ ∗ ∃ l, net.isListener lv' l ∗
            netLis (extLocalGS netExt (L := hG.goose_localGS)) l (clientAddr c) true ∗
            netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l (clientAddr c)) ∨
          ⌜err' ≠ interface.nil⌝) : IProp GF) $$ [l err Hres]
    · iexists li, err
      iframe l err
      icases Hres with (H | ⟨%x, %ex, -, #Herr, -⟩)
      · ileft; iexact H
      · iright
        ihave %Hne := net.opErr_netErr _ _ _ _ _ $$ Herr
        obtain ⟨pe, rfl⟩ := Hne
        ipureintro; simp
    wp_for HLs
    icases Hl with (⟨%He, %lv, #Hli, Hl, #Hla⟩ | %Hne)
    · subst He
      wp_auto
      rw [if_neg (by
          intro h
          have h' := of_decide_eq_true h
          exact absurd (go.IntoValInj.intoVal_inj (V := Bool) h') (by decide)),
        if_pos (by simp)]
      wp_auto
      wp_apply wp_fork $$ [Hl]
      · wp_apply wp_accept wp_Accept wp_Read wp_Close wp_NewReader γ c «$r0_ptr» lv' lv $$ [Hl]
        · iframe Hsys Hcp Hli Hl Hla
        itrivial
      ihave %Hrl := ownSlice_len _ _ _ $$ Hrsl
      ihave HI2 : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "r" ∷ (∃ rl : Loc, r_ptr ↦ rl) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rsl.len⌝ : IProp GF) $$ [i r]
      · iexists W64 0
        iframe i
        isplitl [r]
        · iexists _; iexact r
        ipureintro; constructor <;> word
      wp_for HI2
      wp_if_destruct
      · have Hif' : sint.Z j < sint.Z rsl.len := by
          first | exact Hif | (have h := go.IntoValInj.intoVal_inj (V := Bool) Hif; simpa using h)
        have hidx : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rsl.len := ⟨Hj.1, Hif'⟩
        simp only [hidx, _root_.and_self, ↓reduceIte]
        list_elem rls (sint.Z j).toNat as rl
        wp_apply wp_load_slice_index rsl (sint.Z j) rls DFrac.discard rl hidx.1 $$ [Hrsl] as -
        · iframe Hrsl; ipureintro; exact Hrl_lookup
        iunfold repsOk at Hreps
        icases (BigSepL.bigSepL_lookup_acc (Φ := fun i rl => iprop(isReplica γ c (i + 1) rl))
          Hrl_lookup).1 $$ Hreps with ⟨#Hrep, Hback⟩
        ihave Hreps := Hback $$ Hrep
        have hset : rls.set (sint.Z j).toNat rl = rls := by
          obtain ⟨h, he⟩ := List.getElem?_eq_some_iff.1 Hrl_lookup
          rw [← he, List.set_getElem_self]
        rw [hset]
        icases r with ⟨%rl0, r⟩
        wp_auto
        ihave HI3 : ("Hrep" ∷ isReplica γ c ((sint.Z j).toNat + 1) rl : IProp GF) $$ []
        · iexact Hrep
        wp_for HI3
        wp_apply wp_tryConnect wp_Dial wp_Write wp_Close γ c _ rl $$ [Hrep] as %ok -
        · iframe Hrep
        cases ok
        · rw [if_pos (by simp)]
          wp_auto
          wp_apply time.wp_Sleep
          wp_for_post
          iframe
          iexact Hrep
        · rw [if_neg (by
            intro h
            have h' := of_decide_eq_true h
            exact absurd (go.IntoValInj.intoVal_inj (V := Bool) h') (by decide)), if_pos (by simp)]
          wp_for_post
          iframe
          isplitl [Hreps]
          · unfold repsOk; iexact Hreps
          iexists j + W64 1
          iframe
          isplitl [r]
          · iexists _; iexact r
          ipureintro; word
      · iapply HΦ; iexact Hsys
    · rcases err' with ie | _
      · simp only
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (by simp)]
        wp_auto
        wp_apply time.wp_Sleep
        rw [ite_eq_left_of_eq_true _ _ (eq_true hidx2)]
        wp_apply wp_load_slice_index asl (sint.Z (W64 1 + W64 (c : Int))) addrsL _ (clientAddr c)
          hidx2.1 $$ [Hasl] as -
        · iframe Hasl; ipureintro
          rw [hidx2', addrsL_get _ (by omega), clientAddr_port]
        wp_apply wp_L go!"tcp" net.tcpNet_tcp (clientAddr c) as %li2 %err2 Hres2
        · isplitr
          · ipureintro; exact Hok
          iapply listen_au $$ Hcp
        wp_for_post
        iframe
        iexists li2, err2
        iframe
        icases Hres2 with (H | ⟨%x, %ex, -, #Herr, -⟩)
        · ileft; iexact H
        · iright
          ihave %Hne := net.opErr_netErr _ _ _ _ _ $$ Herr
          obtain ⟨pe, rfl⟩ := Hne
          ipureintro; simp
      · exact absurd rfl Hne

end proof

end raxos.examples.quepaxanet
end Perennial
