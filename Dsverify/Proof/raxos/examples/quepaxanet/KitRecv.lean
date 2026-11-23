/-
Client machine `c`'s receiver of the replicas' answers (`kit.go`'s `Sys.receive`, `Sys.accept`; the
lab's `Kit/{RecvParse,RecvLoop,RecvAccept}.lean`, re-based on `Net/` and the landed `bufio`): a
connection accepted at the client's address `clientAddr c` carries `clientInProto γ c` (a proxy's
handshake, then answer frames, each a fit batch with one result `r` and `opAns`), read through a
`*bufio.Reader`; every answer is delivered (`wp_deliver`). The parsing is `Proxy/NetFrames.lean`'s
(`frs`, `after_frames`, `frs_head`, `prefix_le8`, `prefix_enc`), at the client port's protocol.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitSys

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
open EtcdGrove (bufio.ownBufReader)

/-! ## The client port's stream -/

section frames
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The answers' facts. -/
def ansL (γ : QNames) (L : List Batch) : IProp GF :=
  iprop([∗list] b ∈ L, ∃ r, ⌜b.cmds = [r]⌝ ∗ opAns γ b.id r)

instance ansL_persistent (γ : QNames) (L : List Batch) : Persistent (ansL (GF := GF) γ L) := by
  unfold ansL opAns opDone; infer_instance

/-- What client `c`'s reader end has read is a prefix of a handshake and answer frames. -/
theorem cl_prefix (γ : QNames) (c cn : Nat) (W : List w8) :
    protoPrefix (clientInProto (GF := GF) γ c) cn W ⊢
      (⌜W = []⌝ ∨ ∃ (k : Nat) (L : List Batch), ⌜W <+: raxos.hs k ++ frs L ∧
        ∀ b ∈ L, batchFit b⌝ ∗ ansL γ L) := by
  iintro Hp
  unfold protoPrefix
  icases Hp with (%h | ⟨%ext, %hp, #HP⟩)
  · ileft; ipureintro; exact h
  · unfold clientInProto
    icases HP with ⟨%k, %L, %hL, #Hs⟩
    iright
    iexists k, L
    unfold ansL
    iframe Hs
    ipureintro
    exact ⟨hp.trans hL.2.1, hL.2.2⟩

/-- Four bytes read are a handshake. -/
theorem cl_hs (γ : QNames) (c cn : Nat) (d : List w8) (hd : d.length = 4) :
    protoPrefix (clientInProto (GF := GF) γ c) cn d ⊢ ⌜∃ k, d = raxos.hs k⌝ := by
  iintro Hp
  ihave Hp := cl_prefix γ c cn d $$ Hp
  icases Hp with (%h | ⟨%k, %L, %hL, -⟩)
  · subst h; simp at hd
  ipureintro
  refine ⟨k, ?_⟩
  exact List.IsPrefix.eq_of_length (List.prefix_of_prefix_length_le hL.1 (List.prefix_append _ _)
    (by simp [raxos.hs, hd])) (by simp [raxos.hs, hd])

/-- The stream after the handshake `hs n` and whole frames `A`, starting with `hs n`. -/
theorem cl_frames (γ : QNames) (c cn n : Nat) (W : List w8) (hW : raxos.hs n <+: W) :
    protoPrefix (clientInProto (GF := GF) γ c) cn W ⊢
      (⌜W = []⌝ ∨ ∃ L : List Batch, ⌜W <+: raxos.hs n ++ frs L ∧ ∀ b ∈ L, batchFit b⌝ ∗ ansL γ L) := by
  iintro Hp
  ihave Hp := cl_prefix γ c cn W $$ Hp
  icases Hp with (%h | ⟨%k, %L, %hL, #Hs⟩)
  · ileft; ipureintro; exact h
  have he : raxos.hs n = raxos.hs k :=
    hs_eq_of_prefix (hW.trans hL.1) (List.prefix_append _ _)
  iright
  iexists L
  iframe Hs
  ipureintro
  rw [he]
  exact hL

/-- The length after a frame's code byte is below `2^63` (`unmarshalB`'s bound). -/
theorem cl_len (γ : QNames) (c cn n : Nat) (A : List Batch)
    (hA : ∀ b ∈ A, (encBatch b).length < 2 ^ 63) :
    ⊢@{IProp GF} □ (∀ d, protoPrefix (clientInProto γ c) cn ((raxos.hs n ++ frs A ++ [W8 1]) ++ d) -∗
      ⌜d.length = 8 → leNum d < 2 ^ 63⌝) := by
  iintro !> %d HI
  ihave Hp := cl_frames γ c cn n _ (by simp only [List.append_assoc]; exact List.prefix_append _ _)
    $$ HI
  icases Hp with (%h | ⟨%L, %hL, -⟩)
  · simp at h
  ipureintro
  intro hd
  have h2 : raxos.hs n ++ frs A ++ (W8 1 :: d) <+: raxos.hs n ++ frs L := by
    simpa [List.append_assoc] using hL.1
  obtain ⟨-, h3⟩ := after_frames A L _ hA hL.2 h2
  obtain ⟨b', hb', -, h4⟩ := frs_head L A.length _ _ h3
  have h5 := prefix_le8 (e := []) hd (by rw [List.append_nil, List.append_assoc] at *; exact h4)
  have hb'L := (hL.2 b' (List.mem_of_getElem? hb')).2
  rw [h5, leNum_le8 _ (by omega)]
  exact hb'L

/-- A whole frame read after the handshake and the frames `A`: the answer `b'`, fit, with its
result's `opAns`. -/
theorem cl_frame (γ : QNames) (c cn n : Nat)
    (A : List Batch) (bs : List w8) (hA : ∀ b ∈ A, (encBatch b).length < 2 ^ 63)
    (hbs : bs.length < 2 ^ 63) :
    protoPrefix (clientInProto (GF := GF) γ c) cn
        ((raxos.hs n ++ frs A ++ [W8 1]) ++ (le8 bs.length ++ bs)) ⊢
      ∃ b', ⌜encBatch b' = bs ∧ batchFit b' ∧
          (raxos.hs n ++ frs A ++ [W8 1]) ++ (le8 bs.length ++ bs) = raxos.hs n ++ frs (A ++ [b'])⌝ ∗
        ∃ r, ⌜b'.cmds = [r]⌝ ∗ opAns γ b'.id r := by
  iintro HI
  ihave Hp := cl_frames γ c cn n _ (by simp only [List.append_assoc]; exact List.prefix_append _ _)
    $$ HI
  icases Hp with (%h | ⟨%L, %hL, #Hs⟩)
  · simp at h
  have h2 : raxos.hs n ++ frs A ++ (W8 1 :: (le8 bs.length ++ bs ++ [])) <+:
      raxos.hs n ++ frs L := by
    simpa [List.append_assoc] using hL.1
  obtain ⟨-, h3⟩ := after_frames A L _ hA hL.2 h2
  obtain ⟨b', hb', -, h4⟩ := frs_head L A.length _ _ h3
  have hb'L := hL.2 b' (List.mem_of_getElem? hb')
  have he : bs = encBatch b' := prefix_enc (by omega) (by have := hb'L.2; omega) h4
  unfold ansL
  ihave #Hb := BigSepL.bigSepL_lookup hb' $$ Hs
  iexists b'
  iframe Hb
  ipureintro
  refine ⟨he.symm, hb'L, ?_⟩
  subst he; simp [frs_append, frs_cons, frs_nil, frame, List.append_assoc]

end frames

section recv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [net.FieldAssumptions] [_root_.Perennial.bufio.Assumptions]
variable [_root_.Perennial.io.Assumptions]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions] [pb : hyp.PbHyp GF]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

theorem fourBytes_eq {d : List w8} (h : d.length = 4) : ∃ a b c e : w8, d = [a, b, c, e] := by
  match d, h with
  | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl⟩

set_option hygiene false in
/-- The end of `receive`: close the connection, reset the client's connection to the replica that
sent its name. -/
macro "recv_end" : tactic => `(tactic| (
  wp_apply wp_Close t cn true (clientAddr c) la ra (fun _ => iprop(True)) $$ [] as %e -
  · iframe Hca
    imod close_au cn true $$ Hcis with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd' Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
    imodintro
    itrivial
  iunfold sysFields at Hf
  icases Hf with ⟨-, -, -, #Hrs, #Hrls⟩
  ihave %Hrl := ownSlice_len _ _ _ $$ Hrls
  (try wp_auto)
  wp_if_destruct
  · wp_if_destruct
    · have hidx : 0 ≤ sint.Z (frm - W64 1) ∧ sint.Z (frm - W64 1) < sint.Z rs.len := by
        constructor <;> word
      simp only [hidx, _root_.and_self, ↓reduceIte]
      list_elem rls (sint.Z (frm - W64 1)).toNat as rl
      wp_apply wp_load_slice_index rs (sint.Z (frm - W64 1)) rls DFrac.discard rl hidx.1 $$ [Hrls] as -
      · iframe Hrls; ipureintro; exact Hrl_lookup
      iunfold repsOk at Hreps
      ihave #Hrep := BigSepL.bigSepL_lookup (Φ := fun i rl => iprop(isReplica γ c (i + 1) rl))
        Hrl_lookup $$ Hreps
      wp_apply wp_reset wp_Close γ c ((sint.Z (frm - W64 1)).toNat + 1) rl $$ []
      · iframe Hrep; (try iexact Hpkg)
      wp_end
    · wp_end
  · wp_end))

set_option maxHeartbeats 1600000 in
/-- `s.receive(c)` on a connection accepted at client `c`'s address (it ends when the connection
does). -/
theorem wp_receive (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specOk (GF := GF) (hG := hG))
    (γ : QNames) (c : Nat) (s : Loc) (t : Loc) (cn : Nat) (la ra : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ isSysL γ c s ∗
        net.connAt t cn true (clientAddr c) la ra ∗ connIs cn ∗
        recvTokL cn true (clientInProto γ c) [] }}
      (App (Val (s @!! go.GoType.PointerType raxos.examples.quepaxanet.Sys.ty @!! go!"receive"))
        (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t)))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hsys, #Hca, #Hcis, Hr⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
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
  ihave #Hrok := net.conn_readerOk wp_Read t cn true (clientAddr c) la ra _ ed (clientInProto γ c)
    $$ [$Hio $Hca $Heof $Hed]
  wp_auto
  rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t =
    GoInterface.ok (net.connIface t) from rfl]
  wp_apply wp_NewReader (net.connIface t) (fun _ m => 0 < m)
      (recvTokL (Gg := hG.goose_globalGS) cn true (clientInProto γ c)) _ []
    $$ [$Hbufio $Hrok $Hr] as %br Hbr
  · isplitr
    · ipureintro; exact net.connIface_ne_bufioReader t
    iapply EtcdGrove.bufio.preUpTo_of_pure
    intro r m hm _; exact hm
  ihave #Hbrok := EtcdGrove.bufio.ownBufReader_readerOk EtcdGrove.bufio.Reader.Read.wp_proofOk
    br (net.connIface t) (fun _ m => 0 < m) (recvTokL (Gg := hG.goose_globalGS) cn true (clientInProto γ c)) _
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h4 : W64 4 - W64 0 = W64 4 := rfl
  rw [h0, go.arrayIndexRef_0, h4]
  ihave Hsl := slice_array hs_ptr 4 _ (by decide) $$ hs
  rw [show interface.mkOk (go.GoType.PointerType Perennial.bufio.Reader.ty) #br =
    GoInterface.ok (EtcdGrove.bufio.readerIface br) from rfl]
  wp_apply (_root_.Perennial.io.wp_ReadFull (EtcdGrove.bufio.readerIface br)
      (fun R m => 0 < m → (fun (_ : List w8) (m : Nat) => 0 < m) R m)
      (bufio.ownBufReader br (net.connIface t) (fun _ m => 0 < m)
        (recvTokL (Gg := hG.goose_globalGS) cn true (clientInProto γ c)) _)
      (EtcdGrove.bufio.errE _) [] _ _ _ _) $$ [Hbr Hsl]
    as %n %e1 ⟨%d1, %Hd1, Hsl, Hbr, #Hres⟩
  · iframe Hbrok Heof Hueof Hbr Hsl
    ipureintro; intro ys hys hm; exact hm
  cases e1 with
  | ok i1 =>
    wp_auto
    wp_apply wp_Close t cn true (clientAddr c) la ra (fun _ => iprop(True)) $$ [] as %e -
    · iframe Hca
      imod close_au cn true $$ Hcis with ⟨%st, %dd, Hst, Hdd, Hcl⟩
      imodintro
      iexists st, dd
      iframe Hst Hdd
      iintro %res %st' %d' %Hd' Hst Hdd
      imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
      imodintro
      itrivial
    wp_end
  | nil =>
  ihave %Hd4' : ⌜d1.length = (zero_val (GoArray w8 4)).arr.length⌝ $$ [Hres]
  · iunfold _root_.Perennial.io.readFullRes at Hres
    icases Hres with (%h | ⟨%e, %h, -⟩)
    · ipureintro; exact h.1
    · exfalso
      obtain ⟨-, hne, h1, h2⟩ := h
      by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe ∧ d1 ≠ []
      · exact absurd (h1 hc) (by intro h; cases h)
      · exact hne (h2 hc).symm
  have Hd4 : d1.length = 4 := by rw [Hd4']; rfl
  rw [show (zero_val (GoArray w8 4)).arr.drop d1.length = [] by rw [Hd4]; rfl, List.append_nil,
    List.nil_append] at *
  ihave ⟨Hbr, #Hpp⟩ := net.connReader_proto br _ _ cn true (clientInProto γ c) _ _ $$ Hbr
  wp_auto
  ihave %Hk := cl_hs γ c cn d1 Hd4 $$ Hpp
  obtain ⟨k, rfl⟩ := Hk
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := encoding.binary.isInit_access $$ Hbin
  icases Hle with ⟨#Hle, -⟩
  rw [h0, go.arrayIndexRef_0, h4]
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ (W8 (k / 256 % 256)) (by word) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  (try wp_auto)
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ (W8 (k % 256)) (by word) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  (try wp_auto)
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ (W8 (k / 256 % 256)) (by word) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  (try wp_auto)
  generalize W64 (uint.Z (W16 (uint.Z (W8 (↑k % 256))) ||| W16 (uint.Z (W8 (↑k / 256 % 256))) <<<
    W64 8)) = frm
  iunfold isSysL at Hsys
  icases Hsys with ⟨%rs, %rls, %Hcl, #Hf, #Hmu, #Hreps, #Hsh⟩
  ihave #Hsys' : isSysL γ c s $$ []
  · iunfold isSysL; iexists rs, rls; iframe Hf Hmu Hreps Hsh; ipureintro; exact Hcl
  ihave HI : (∃ A : List Batch,
      "Hbr" ∷ bufio.ownBufReader br (net.connIface t) (fun _ m => 0 < m)
        (recvTokL (Gg := hG.goose_globalGS) cn true (clientInProto γ c))
        (net.connReadE (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe) la ra ed)
        (raxos.hs k ++ frs A) ∗
      "%HA" ∷ ⌜∀ b ∈ A, (encBatch b).length < 2 ^ 63⌝ : IProp GF) $$ [Hbr]
  · iexists []
    simp only [frs_nil, List.append_nil]
    iframe
    ipureintro; simp
  irename «from» => Hfrm
  wp_for HI
  wp_apply EtcdGrove.bufio.Reader.ReadByte.wp_proof br _ _ _ _ (raxos.hs k ++ frs A) $$ Hbr
    as %cd %e1 Hres
  icases Hres with (⟨%He, Hbr⟩ | ⟨%He, -, -, Hbr⟩)
  · subst He
    by_cases hcd : cd = W8 1
    · subst hcd
      wp_auto
      ihave #Hlen := cl_len γ c cn k A HA
      wp_apply (unmarshal_bounded «$r0_ptr» br _ _
          (recvTokL (Gg := hG.goose_globalGS) cn true (clientInProto γ c)) _ _
          (protoPrefix (clientInProto γ c) cn) (fun _ => inferInstance)
          (fun r => recvTokL_proto cn true _ r)
          (fun x y => protoPrefix_le (List.prefix_append x y))) $$ [«$r0» Hbr]
        as %e2 ⟨%data, Hbr, Hres⟩
      · iframe «$r0» Hbr Hlen
        ipureintro; intro r m hm; exact hm
      icases Hres with (%He | ⟨%bs, %b, ⟨%He, %Hdata, %Huniq, %Hbs⟩, Hrep⟩)
      · cases e2 with
        | nil => exact absurd rfl He
        | ok ie =>
          wp_auto
          wp_for_post
          recv_end
      subst He Hdata
      ihave ⟨Hbr, #Hpp2⟩ := net.connReader_proto br _ _ cn true (clientInProto γ c) _ _ $$ Hbr
      wp_auto
      ihave ⟨%b', ⟨%Heb, %Hok, %Heq⟩, %r, %Hr, #Hans⟩ := cl_frame γ c cn k A bs HA Hbs $$ Hpp2
      obtain rfl : b = b' := Huniq b' Hok.1 Heb
      ihave Hrep := Hrep $$ %(⟨b, Hok.1, Heb⟩ : ∃ b0, batchOk b0 ∧ encBatch b0 = bs)
      rw [Heq]
      wp_apply wp_deliver γ c s frm _ b $$ [Hrep]
      · iframe Hrep Hsys'
        unfold ansOk; iexists r; iframe Hans; ipureintro; exact ⟨Hr, Hok⟩
      wp_for_post
      iframe
      iexists A ++ [b]
      iframe
      ipureintro
      intro b0 hb0
      rcases List.mem_append.1 hb0 with h | h
      · exact HA b0 h
      · rw [List.mem_singleton.1 h]; exact Hok.2
    · wp_auto
      wp_if_destruct
      · exfalso; apply hcd; rfl
      · wp_for_post
        recv_end
  · cases e1 with
    | nil => exact absurd rfl He
    | ok ie =>
      wp_auto
      wp_for_post
      recv_end

/-- `s.accept(l)` on a listener at client `c`'s address (it never returns). -/
theorem wp_accept (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specOk (GF := GF) (hG := hG))
    (γ : QNames) (c : Nat) (s : Loc) (li : GoInterface) (lv : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ isSysL γ c s ∗
        addrProto (clientAddr c) (clientInProto γ c) silentProto ∗ net.isListener li lv ∗
        netLis (extLocalGS netExt (L := hG.goose_localGS)) lv (clientAddr c) true ∗
        netLisAt (extLocalGS netExt (L := hG.goose_localGS)) lv (clientAddr c) }}
      (App (Val (s @!! go.GoType.PointerType raxos.examples.quepaxanet.Sys.ty @!! go!"accept"))
        (Val #li))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hsys, #Hpr, #Hli, Hl, #Hla⟩
  iunfold net.isListener at Hli
  icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  have wp_A := net.Listener.Accept.spec_addrOk wp_Accept
  wp_auto
  ihave HI : ("Hl" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) lv (clientAddr c) true :
    IProp GF) $$ [Hl]
  · iframe
  wp_for HI
  wp_apply wp_A t lv x (clientAddr c)
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) lv (clientAddr c) true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) lv (clientAddr c) true ∗
        connEnd (Gg := hG.goose_globalGS) cn true silentProto (clientInProto γ c) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn true))
      $$ [Hl]
    as %cv %err (⟨%Herr, %cn, #Hcv, Hl, Hend, -⟩ | ⟨%kk, Hl, #Herr⟩)
  · iframe Hlt Hla
    iapply accept_au (clientAddr c) (clientInProto γ c) silentProto _ lv true $$ Hpr Hl
  · subst Herr
    iunfold net.isConn at Hcv
    icases Hcv with ⟨%tc, %la, %ra, %Hcv, #Hconn⟩
    subst Hcv
    iunfold connEnd at Hend
    icases Hend with ⟨Hs, Hr⟩
    ihave #HcIs := sendTok_connIs cn true _ _ $$ Hs
    ihave Hr := recvTok_L cn true _ _ $$ Hr
    wp_auto
    wp_apply wp_fork $$ [Hr]
    · wp_apply wp_receive wp_Read wp_Close wp_NewReader γ c s tc cn la ra $$ [Hr]
      · iframe Hsys Hconn HcIs Hr
      itrivial
    wp_for_post
    iframe
  · ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_for_post
    iframe

end recv

end raxos.examples.quepaxanet
end Perennial
