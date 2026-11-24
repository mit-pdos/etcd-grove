/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Client/Conn.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md), restated for the kit's client on remote and `Net/`.

* `replica_addrProto`: client `c`'s replica's port has Gryff's wire protocols (from the start's
  `lisProto` of its wildcard listener, `lisProto_addr`).
* `unusedIds_split`: the next unused Gryff client id of client `c`, with its turn token.
* `clientStream_hs`: a client's handshake alone is an allowed dialer's stream.
* `wp_connect` (`sys.connect()`): dial client `c`'s replica (`DialTimeout`, `dial_au`); on success a
  fresh Gryff client id bound to the new connection (`clientConnAt_intro`), the reader and the
  writer over the connection (`net.conn_readerOk`, `net.conn_streamWriterOk`), the handshake
  buffered (`connOk`).
* `wp_drop` (`sys.drop()`): close the connection and forget it.
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.KitSpecs
public import Dsverify.Proof.gryff.N.NetSpecs
public import Dsverify.Proof.gryff.N.ClientConn
public import Perennial.Proof.encoding.binary.Results
public import GooseLang.Ext.Net.Decide

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.netN

attribute [local instance] GooseGlobalGS.gooseInvGS

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

theorem portAddr_ok (k : Nat) (hk : k < 3) :
    addrOk (portAddr k) = true ∧ lisAccepts (lisAddrOf (portAddr k)) (portAddr k) := by
  rcases k with _ | _ | _ | k
  · exact ⟨by decide, lisAcceptsB_iff.1 (by decide)⟩
  · exact ⟨by decide, lisAcceptsB_iff.1 (by decide)⟩
  · exact ⟨by decide, lisAcceptsB_iff.1 (by decide)⟩
  · omega

/-- Client `c`'s replica's port has Gryff's wire protocols. -/
theorem replica_addrProto (γ : GryffNames GF) (c : Nat) :
    examples.gryffnet.replicaLises γ ⊢
      addrProto (Gg := hG.goose_globalGS) (replicaOf c) (gryffWireP γ (replicaOf c))
        (gryffWireQ γ (replicaOf c)) := by
  iintro #H
  unfold examples.gryffnet.replicaLises
  have hk : c % 3 < 3 := Nat.mod_lt _ (by decide)
  ihave #Hk := BigSepL.bigSepL_mem (Φ := fun k => replicaLis (GF := GF) γ k)
    (show c % 3 ∈ [0, 1, 2] by
      rcases h : c % 3 with _ | _ | _ | n
      · simp
      · simp
      · simp
      · omega) $$ H
  unfold replicaLis replicaOf
  obtain ⟨hok, hacc⟩ := portAddr_ok (c % 3) hk
  iapply lisProto_addr _ _ _ _ hok hacc $$ Hk

/-- The next unused id of client `c` (generation `gen < 5`), with its turn token. -/
theorem unusedIds_split (γ : GryffNames GF) (c gen : Nat) (h : gen < 5) :
    unusedIds γ c gen ⊣⊢
      (idTok γ (gid c gen) ∗ turnTok (GF := GF) γ.proto (c + 6 * gen) 0) ∗
        unusedIds γ c (gen + 1) := by
  unfold unusedIds
  have e : List.range' gen (5 - gen) = gen :: List.range' (gen + 1) (5 - (gen + 1)) := by
    rw [show 5 - gen = (5 - (gen + 1)) + 1 by omega, List.range'_succ]
  rw [e]
  exact BigSepL.bigSepL_cons

/-- A client's handshake alone is an allowed dialer's stream of a replica's port. -/
theorem clientStream_hs (γ : GryffNames GF) (a : GoString) (cid : Nat) (hs : w32)
    (hhs : hs < peerMark) (last : Int) :
    clientConnAt γ hs cid ⊢ □ gryffWireP γ a cid (u32Le hs) := by
  iintro #Hcc
  iintro !>
  unfold gryffWireP
  iright
  iexists u32Le hs ++ []
  isplitr
  · ipureintro; simp
  iintro !>
  unfold dialStream
  iexists hs, []
  isplitr
  · ipureintro; rfl
  iright
  isplitr
  · ipureintro; exact hhs
  iframe Hcc
  iexists last
  iapply clientReqsOk_nil

theorem ed_of_poll :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨-, ⟨%ed, #Hd⟩, -⟩
  iexists ed
  iexact Hd

theorem eof_of_io [_root_.Perennial.io.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      ∃ eof : GoInterface, globalAddr _root_.Perennial.io.EOF ↦□ eof := by
  iintro #Hio
  ihave #Heof := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold errors.newVar at Heof
  icases Heof with ⟨%x, #Hx, -⟩
  iexists _
  iexact Hx

theorem gid_lt_peerMark (c g : Nat) (hc : c < 6) (hg : g < 5) : gid c g < peerMark := by
  unfold gid peerMark
  have : c + 6 * g < 30 := by omega
  word

end laws

section conn
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [wire.BufioSpecs GF]
variable [net.Assumptions] [net.FieldAssumptions] [nS : NetSpecs GF]

set_option goose.wp.extras true

/-- `sys.connect()`: see the file header. -/
theorem wp_connect (γ : GryffNames GF) (c : Nat) (sp mu cl : Loc) (v : examples.gryffnet.client)
    (hc : c < 6) (hgen : uint.nat v.gen' < 4) (hconn : v.conn' = interface.nil)
    (hseq : 0 ≤ sint.Z v.seq') :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ sysFixed c sp mu cl ∗
        □ protoInvs γ ∗ examples.gryffnet.replicaLises γ ∗ cl ↦ v ∗
        unusedIds γ c (uint.nat v.gen') }}
      (App (Val (sp @!! go.GoType.PointerType examples.gryffnet.Sys.ty @!! go!"connect"))
        (Val #()))
    {{ (b : Bool), RET #b;
        if b then ∃ v' : examples.gryffnet.client, cl ↦ v' ∗
          ⌜uint.nat v'.gen' = uint.nat v.gen' + 1 ∧ v'.seq' = v.seq'⌝ ∗
          unusedIds γ c (uint.nat v.gen' + 1) ∗ connOk γ c v'
        else cl ↦ v ∗ unusedIds γ c (uint.nat v.gen') }} := by
  wp_start as ⟨#Hfix, #Hinv, #Hlis, Hp, Hids⟩
  iunfold sysFixed at Hfix
  icases Hfix with ⟨%ads, #Hmu, #Hcf, #Haddrs, #Hads, #Hcl⟩
  ihave %Hadsl := ownSlice_len _ _ _ $$ Hads
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  ihave ⟨%ed, #Hed⟩ := ed_of_poll $$ Hpoll
  ihave ⟨%eof, #Heof⟩ := eof_of_io $$ Hio
  ihave #Hni : Perennial.net.isInit $$ []
  · with_unfolding_all iapply isPkgInit_access (PROP := IProp GF) pkg_id.net $$ Hnet
  icases Hni with ⟨-, -, %pt, #Het⟩
  ihave #Hap := replica_addrProto γ c $$ Hlis
  wp_auto
  have hads4 : sint.Z ads.len = 4 := by
    obtain ⟨h1, h2⟩ := Hadsl
    have h3 : sint.nat ads.len = 4 := by simpa [serverAddrs] using h1.symm
    have h4 : (sint.Z ads.len).toNat = 4 := h3
    have h5 := Int.toNat_of_nonneg h2
    rw [h4] at h5
    exact h5.symm
  have hidx : sint.Z (W64 1 + W64 (c : Int) % W64 3) = ((1 + c % 3 : Nat) : Int) := by word
  rw [if_pos ⟨by omega, by omega⟩]
  wp_apply wp_load_slice_index ads _ serverAddrs _ (replicaOf c) (by omega) $$ [Hads] as -
  · iframe Hads; ipureintro
    rw [hidx, Int.toNat_natCast]
    have hk : c % 3 < 3 := Nat.mod_lt _ (by decide)
    unfold serverAddrs replicaOf
    rcases h : c % 3 with _ | _ | _ | n <;> first | rfl | omega
  have haok : addrOk (replicaOf c) = true :=
    (portAddr_ok (c % 3) (Nat.mod_lt _ (by decide))).1
  wp_apply (nS.dialTimeout go!"tcp" Perennial.net.tcpNet_tcp (replicaOf c) _ _ ed iprop(True)
      (fun cn => iprop(connEnd cn false (gryffWireP γ (replicaOf c)) (gryffWireQ γ (replicaOf c))
        [] [] ∗ connFresh cn false))) $$ [] as %cv %derr Hres
  · iframe Het Hed
    isplitr
    · ipureintro; exact haok
    isplit
    · itrivial
    · iapply dial_au $$ Hap
  icases Hres with (⟨%Hderr, %cid, #Hcc, Hend, -⟩ | ⟨-, %x, %e, -, #Hop, -⟩)
  rotate_left
  · -- the dial failed
    ihave %Hne : ⌜derr ≠ interface.nil⌝ $$ [Hop]
    · iunfold Perennial.net.opErr at Hop
      icases Hop with ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩
      ipureintro; rw [Herr]; exact fun h => by cases h
    obtain ⟨ie, rfl⟩ : ∃ ie, derr = interface.ok ie := by
      cases derr with
      | nil => exact absurd rfl Hne
      | ok ie => exact ⟨ie, rfl⟩
    wp_auto
    iapply HΦ $$ %false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hp Hids
  subst Hderr
  iunfold Perennial.net.isConn at Hcc
  icases Hcc with ⟨%tc, %la, %ra, %Hcv, #Hown⟩
  subst Hcv
  wp_auto
  -- the reader
  iunfold connEnd at Hend
  icases Hend with ⟨Hsend, Hrecv⟩
  ihave #Hrok := Perennial.net.conn_readerOk nS.read tc cid false (replicaOf c) la ra eof ed
    (gryffWireQ γ (replicaOf c)) $$ [$Hio $Hown $Heof $Hed]
  ihave Hrecv := recvTok_L $$ Hrecv
  rw [show (interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #tc : GoInterface) =
    GoInterface.ok (Perennial.net.connIface tc) from rfl]
  wp_apply wire.wp_NewReader (netN.connRSt tc eof la ra ed) _ []
    (Perennial.net.connIface_ne_bufioReader tc) $$ [$Hbufio $Hrok $Hrecv] as %br Hrd
  -- the id, bound to the connection
  have hgen5 : uint.nat v.gen' < 5 := by omega
  have hid : W32 (uint.Z (W64 (c : Int) + W64 6 * v.gen')) = gid c (uint.nat v.gen') := by
    unfold gid; word
  have hidZ : sint.Z (gid c (uint.nat v.gen')) = ((c + 6 * uint.nat v.gen' : Nat) : Int) := by
    unfold gid; word
  have hhs := gid_lt_peerMark c (uint.nat v.gen') hc hgen5
  ihave ⟨⟨Hidt, Hturn⟩, Hids⟩ := (unusedIds_split γ c (uint.nat v.gen') hgen5).1 $$ Hids
  iapply fupd_wp
  imod clientConnAt_intro γ (gid c (uint.nat v.gen')) cid $$ [$Hinv $Hidt] with #Hcca
  imodintro
  ihave #HP1 := clientStream_hs γ (replicaOf c) cid (gid c (uint.nat v.gen')) hhs
    (sint.Z v.seq') $$ Hcca
  -- the writer
  ihave #Hwok := Perennial.net.conn_streamWriterOk nS.write tc cid false (replicaOf c) la ra ed
    (gryffWireP γ (replicaOf c)) (gryffWireP_closed γ (replicaOf c)) $$ [$Hown $Hed]
  ihave #HP0 : □ gryffWireP γ (replicaOf c) cid [] $$ []
  · iintro !>; unfold gryffWireP; ileft; ipureintro; rfl
  wp_apply wire.wp_NewWriter_room (connWSt tc la ra ed) _ _ [] rfl
    (Perennial.net.connIface_ne_bufioWriter tc) $$ [$Hbufio $Hwok $Hsend $HP0] as %bw Hwr
  have e0 : arrayIndexRef w8 (sint.Z (W64 0)) b_ptr = b_ptr := go.arrayIndexRef_0 _ _
  have e4 : (W64 4 - W64 0 : w64) = W64 4 := rfl
  rw [e0, e4]
  ihave Hb := slice_array b_ptr _ _ (by decide) $$ b
  rw [show (zero_val (GoArray w8 4)).arr = [W8 0, W8 0, W8 0, W8 0] ++ [] from rfl]
  rw [hid]
  wp_apply encoding.binary.wp_LittleEndian_PutUint32 _ [W8 0, W8 0, W8 0, W8 0] []
    (gid c (uint.nat v.gen')) rfl $$ [$Hbin $Hb] as Hb
  isimp at Hp
  ihave #HQ2 : □ gryffWireP γ (replicaOf c) cid ([] ++ [] ++ (u32Le (gid c (uint.nat v.gen')) ++ []))
    $$ []
  · simp only [List.nil_append, List.append_nil]; iexact HP1
  rw [e0, e4]
  wp_apply wire.wp_Write_room bw _ _ _ [] [] 4096 _ (DFrac.own 1) _ (by simp [u32Le_length])
    $$ [$Hwr $HQ2 $Hb] as ⟨-, Hwr⟩
  iapply HΦ $$ %true
  simp only [↓reduceIte]
  iexists _
  iframe Hp
  isplitr
  · ipureintro; constructor
    · show uint.nat (v.gen' + 1#64) = uint.nat v.gen' + 1; word
    · rfl
  iframe Hids
  iunfold connOk
  ihave Hwr := wire.writerRoom_mono _ _ _ _ _ _ _ 1 (by simp [u32Le_length]) $$ Hwr
  iexists tc, cid, replicaOf c, la, ra, eof, ed, [], [], [],
    ([] ++ (u32Le (gid c (uint.nat v.gen')) ++ [])), 0
  rw [show sint.Z (gid c (uint.nat v.gen')) = (c : Int) + 6 * ((uint.nat v.gen' : Nat) : Int) by
    rw [hidZ]; push_cast; rfl]
  iframe Hrd Hwok Hwr Hcca Hturn Hown Heof Hed
  isplitr
  · ipureintro
    have hg1 : uint.nat (v.gen' + 1#64) = uint.nat v.gen' + 1 := by word
    refine ⟨rfl, rfl, ?_, ?_, by simp, ?_, ⟨[], rfl, by simp⟩⟩
    · show 1 ≤ uint.nat (v.gen' + 1#64)
      omega
    · show gid c (uint.nat v.gen') = gid c (uint.nat (v.gen' + 1#64) - 1)
      rw [hg1, Nat.add_sub_cancel]
    · show (0 : Int) ≤ sint.Z v.seq' + 1
      omega
  iapply clientReqsOk_nil

/-- A connection writer's connection is the library's (`connIs`, what `Close` needs). -/
theorem writerRoom_connIs (bw : Loc) (wr : wire.WSt GF) (cn : Nat) (P : Proto GF)
    (Q : List w8 → IProp GF) (sent pend : List w8) (room : Nat) :
    wire.writerRoom bw wr (sendTok (Gg := hG.goose_globalGS) cn false P) Q sent pend room ⊢
      wire.writerRoom bw wr (sendTok (Gg := hG.goose_globalGS) cn false P) Q sent pend room ∗
        connIs (Gg := hG.goose_globalGS) cn := by
  unfold wire.writerRoom wire.ownWriter
  iintro ⟨Hw, %Hr⟩
  ihave ⟨Hw, #Hc⟩ := EtcdGrove.bufio.ownBufWriter_fact bw wr.wi
    (sendTok (Gg := hG.goose_globalGS) cn false P) Q wr.Ew wr.sz sent pend interface.nil (fun _ => connIs (Gg := hG.goose_globalGS) cn)
    (fun w => persistent_entails_left (sendTok_connIs cn false P w)) $$ Hw
  iframe Hw Hc
  ipureintro; exact Hr

/-- `sys.drop()`: see the file header. -/
theorem wp_drop (c : Nat) (sp mu cl : Loc) (v : examples.gryffnet.client) (tc : Loc) (cn : Nat)
    (a : GoString) (la ra : GoInterface)
    (hconn : v.conn' = interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #tc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ sysFixed c sp mu cl ∗
        cl ↦ v ∗ Perennial.net.connAt tc cn false a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val (sp @!! go.GoType.PointerType examples.gryffnet.Sys.ty @!! go!"drop")) (Val #()))
    {{ RET #(); cl ↦ { v with conn' := interface.nil } }} := by
  wp_start as ⟨#Hfix, Hp, #Hcat, #Hcis⟩
  iunfold sysFixed at Hfix
  icases Hfix with ⟨%ads, #Hmu, #Hcf, #Haddrs, #Hads, #Hcl⟩
  wp_auto
  rw [hconn]
  wp_auto
  wp_apply (netN.NetSpecs.close (GF := GF) tc cn false a la ra
    (fun res => iprop(⌜∃ st d st' d', CloseOutcome st d res st' d'⌝))) $$ [] as %e -
  · iframe Hcat
    imod close_au cn false $$ Hcis with ⟨%st, %d, He, Hd, Hk⟩
    imodintro
    iexists st, d
    iframe He Hd
    iintro %res %st' %d' %Hc He Hd
    imod Hk $$ %res %st' %d' %Hc He Hd with -
    imodintro
    ipureintro; exact ⟨st, d, st', d', Hc⟩
  try wp_auto
  iapply HΦ
  iexact Hp

end conn

end Perennial.gryff
