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
    sorry

end proof

end raxos.examples.quepaxanet
end Perennial
