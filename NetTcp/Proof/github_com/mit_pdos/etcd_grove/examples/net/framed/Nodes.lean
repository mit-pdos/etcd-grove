/-
The proofs of `examples/net/framed`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: the loop's invariant: the server has read `sent` from the up direction (its reader
  half, `rcvdAll`), which the dialer has written (`sentLb`), and written back exactly `sent` (its
  half of the view, `srvView`). An iteration reads a header `[h]` and `h` bytes (`wire.ReadFull`
  through `wire.read_acc`), which extend `sent`, and writes them back (`server_write_au`: what it
  writes is in what it has read); any failure breaks the loop, and the close follows.
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's protocol).
* `exchange`: the client's end with `out` written up and as many bytes read down; the writes of the
  header `[len(req)]` and of `req` (`wire.write_au`), then the full reads of the reply's header and
  payload. Both are lower bounds of the server's bytes, so prefixes of the client's own
  `out ++ [len(req)] ++ req` (`client_check`): the reply's header is `len(req)` and the reply `req`,
  so the check does not panic, and the end has again read as many bytes as it has written.
* `Call`: the dial (`dial_both_au`, the deposit `framed_deposit`), three `exchange`s, the close.
* `SendJunk`: the dial, a write of its own bytes, the close.
* `Server`, `Client`, `Junk`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.Defs
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.Forever
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Accept
public import Perennial.Proof.io

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap DirNames dirInv sentAll
  sentLb rcvdAll readP)

namespace github_com.mit_pdos.etcd_grove.examples.net.framed

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.framed

/-- A one-element list that is a prefix of `l :: r` is `[l]`. -/
theorem prefix_one {α : Type} {got : List α} {l : α} {r : List α} (h : got <+: l :: r)
    (hl : got.length = 1) : got = [l] := by
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hl
  obtain ⟨t, ht⟩ := h
  simp only [List.singleton_append, List.cons.injEq] at ht
  rw [ht.1]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : framed.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `wire.readP` before any byte of the call is read. -/
theorem readP_nil (γ : DirNames) (c : Nat) (s : Bool) (st : TcpEnd) (R : List w8) :
    tcpEnd G c s st ∗ rcvdAll (Gg := hG.goose_globalGS) γ R ∗ sentLb γ R ⊢ readP γ c s st R [] := by
  unfold readP; rw [List.append_nil]

/-- `client_check`, its update under a node's invariants. -/
theorem client_check' (γm : GName) (cn : Nat) (γ : FNames) (out resp : List w8) :
    ⊢ inv framedN (framedState (Gg := hG.goose_globalGS) γm) -∗ framedName γm cn γ -∗
      sentAll γ.u out -∗ sentLb γ.d resp ={⊤}=∗ ⌜resp <+: out⌝ ∗ sentAll γ.u out :=
  client_check γm cn γ out resp

theorem wp_serveConn
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn framedInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Hr, #Hlb0, Hv, #Hname⟩, #Heof⟩
  subst Hct
  ihave #HinvU := framed_upInv' γm cn γ $$ HInv Hname
  ihave #HinvD := framed_downInv γm cn γ $$ HInv Hname
  wp_auto
  ihave HI : (∃ (sent : List w8),
      "Hend" ∷ tcpEnd G cn true TcpEnd.fresh ∗ "Hr" ∷ rcvdAll γ.u sent ∗
      "#Hlb" ∷ sentLb γ.u sent ∗ "Hv" ∷ srvView γ.v sent : IProp GF) $$ [Hend Hr Hv]
  · iexists []
    iframe Hend Hr Hv Hlb0
  wp_for HI
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %hdr ⟨Hhdr, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      hdr _ (readP γ.u cn true TcpEnd.fresh sent) eof $$ [Hhdr Hend Hr]
    as %ok ⟨%got1, %bs1, HP, Hhdr, %Hres1⟩
  · iframe Hhdr Heof
    isplitr
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hr]
    · iapply readP_nil
      iframe Hend Hr Hlb
    · iapply wire.read_acc framedN cn true γ.u TcpEnd.fresh sent $$ HinvU
  unfold readP
  icases HP with ⟨Hend, Hr, #Hlb1⟩
  cases ok
  · -- the read failed: break, then close
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply close_drop_au framedN cn true γ.d _ $$ HinvD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨Hlen1, -, Hgot1⟩ := Hres1
  have Hgot1 := Hgot1 rfl
  subst Hgot1
  (try simp only [↓reduceIte])
  wp_auto
  ihave %Hhl := ownSlice_len $$ Hhdr
  obtain ⟨h, rfl⟩ : ∃ h, got1 = [h] := List.length_eq_one_iff.1 (by simpa using Hlen1)
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z hdr.len by simp at Hhl; word)]
  wp_apply wp_load_slice_index hdr (sint.Z (W64 0)) [h] (DFrac.own 1) h (by decide) $$ [Hhdr]
    as Hhdr
  · iframe Hhdr
    ipureintro; rfl
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 (uint.Z h))) as %pl ⟨Hpl, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      pl _ (readP γ.u cn true TcpEnd.fresh (sent ++ [h])) eof $$ [Hpl Hend Hr]
    as %ok ⟨%got2, %bs2, HP, Hpl, %Hres2⟩
  · iframe Hpl Heof
    isplitr
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hr]
    · iapply readP_nil
      iframe Hend Hr Hlb1
    · iapply wire.read_acc framedN cn true γ.u TcpEnd.fresh (sent ++ [h]) $$ HinvU
  unfold readP
  icases HP with ⟨Hend, Hr, #Hlb2⟩
  cases ok
  · -- the read failed: break, then close
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply close_drop_au framedN cn true γ.d _ $$ HinvD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨-, -, Hgot2⟩ := Hres2
  have Hgot2 := Hgot2 rfl
  subst Hgot2
  (try simp only [↓reduceIte])
  wp_auto
  -- echo the header
  wp_apply wp_Write t cn true srvAddr hdr [h] (DFrac.own 1)
      (fun k ok => iprop(tcpEnd G cn true TcpEnd.fresh ∗ srvView γ.v (sent ++ [h].take k) ∗
        ⌜∃ d d', WriteOutcome TcpEnd.fresh d [h] k ok d'⌝))
      $$ [Hhdr Hend Hv]
    as %n %err ⟨%k, %okw, ⟨Hend, Hv, %Hwr⟩, Hhdr, %Hn⟩
  · iframe Hc Hhdr
    iapply server_write_au γm cn γ sent [h] ((sent ++ [h]) ++ got2) TcpEnd.fresh
      (List.prefix_append _ _) $$ HInv Hname Hv Hlb2 Hend
  obtain ⟨-, Hnil, Herr⟩ := Hn
  cases okw
  · -- the write failed: break, then close
    obtain ⟨pe, rfl⟩ := Herr rfl
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply close_drop_au framedN cn true γ.d _ $$ HinvD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  rw [Hnil rfl]
  obtain ⟨d, d', Hwr⟩ := Hwr
  obtain rfl := wire.writeOutcome_ok Hwr
  rw [show List.take [h].length [h] = [h] from rfl]
  wp_auto
  -- echo the payload
  wp_apply wp_Write t cn true srvAddr pl got2 (DFrac.own 1)
      (fun k ok => iprop(tcpEnd G cn true TcpEnd.fresh ∗
        srvView γ.v ((sent ++ [h]) ++ got2.take k) ∗
        ⌜∃ d d', WriteOutcome TcpEnd.fresh d got2 k ok d'⌝))
      $$ [Hpl Hend Hv]
    as %n' %err' ⟨%k', %okw', ⟨Hend, Hv, %Hwr'⟩, Hpl, %Hn'⟩
  · iframe Hc Hpl
    iapply server_write_au γm cn γ (sent ++ [h]) got2 ((sent ++ [h]) ++ got2) TcpEnd.fresh
      (List.prefix_refl _) $$ HInv Hname Hv Hlb2 Hend
  obtain ⟨-, Hnil', Herr'⟩ := Hn'
  cases okw'
  · -- the write failed: break, then close
    obtain ⟨pe, rfl⟩ := Herr' rfl
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply close_drop_au framedN cn true γ.d _ $$ HinvD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  rw [Hnil' rfl]
  obtain ⟨d2, d2', Hwr'⟩ := Hwr'
  obtain rfl := wire.writeOutcome_ok Hwr'
  rw [List.take_of_length_le (Nat.le_refl got2.length)]
  wp_auto
  wp_for_post
  iframe
  iexists (sent ++ [h]) ++ got2
  iframe Hend Hr Hv Hlb2


theorem wp_Serve
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases framedInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HInv⟩
  (try wp_auto)
  wp_apply wp_Listen srvAddr $$ Hplan as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | %Herr)
  · -- listening: the accept loop
    subst Herr
    unfold net.isListener
    icases Hli with ⟨%t, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    ihave HI : ("Hlis" ∷ tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true :
      IProp GF) $$ [Hlis]
    · iexact Hlis
    wp_for HI
    wp_apply wp_Accept t l srvAddr
        (tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%Herr, Hlis⟩)
    · iframe Hlt Hla
      iapply wire.accept_lis_au addrN srvAddr (connProto γm) _ l true $$ HaddrInv Hlis
    · -- a connection: serve it
      subst Herr
      wp_auto
      wp_apply wp_serveConn wp_ReadFull wp_Write wp_Close γm c cn eof $$ [Hproto]
      · iframe Hinvs Hc Hproto Heof
      wp_for_post
      iframe
    · -- a failure: go on
      obtain ⟨pe, rfl⟩ := Herr
      wp_auto
      wp_for_post
      iframe
  · -- not listening: return
    obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial

theorem wp_exchange
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (γ : FNames) (req : GoSlice) (reqbs : List w8)
    (st : TcpEnd) (out : List w8) (eof : GoInterface) (hreq : reqbs.length < 256) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ framedName γm cn γ ∗
        net.isConn c cn false srvAddr ∗ req ↦* reqbs ∗ tcpEnd G cn false st ∗
        sentAll γ.u out ∗ rcvdAll γ.d out ∗ sentLb γ.d out ∗ globalAddr io.EOF ↦□ eof }}
      (App (App (Val (@! exchange)) (Val #c)) (Val #req))
    {{ (ok : Bool), RET #ok; ∃ out' : List w8, tcpEnd G cn false st ∗ sentAll γ.u out' ∗
        if ok then rcvdAll γ.d out' ∗ sentLb γ.d out' else True }} := by
  unfold net.isConn framedInvs
  wp_start as ⟨⟨#HaddrInv, #HInv⟩, #Hname, ⟨%t, %Hct, #Hc⟩, Hreq, Hend, Hout, Hr, #Hlb0, #Heof⟩
  subst Hct
  ihave #HinvU := framed_upInv γm cn γ $$ HInv Hname
  ihave #HinvD := framed_downInv' γm cn γ $$ HInv Hname
  ihave %Hrl := ownSlice_len $$ Hreq
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %hdr ⟨Hhdr, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hhl := ownSlice_len $$ Hhdr
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z hdr.len by simp at Hhl; word)]
  wp_apply wp_store_slice_index hdr (sint.Z (W64 0)) _ (W8 (sint.Z req.len)) $$ [Hhdr] as Hhdr
  · iframe Hhdr
    ipureintro; simp
  rw [show (List.replicate 1 (zero_val w8)).set 0 (W8 (sint.Z req.len)) =
    [W8 (sint.Z req.len)] from rfl]
  generalize hl : W8 (sint.Z req.len) = l
  wp_auto
  -- the header
  wp_apply wp_Write t cn false srvAddr hdr [l] (DFrac.own 1)
      (fun k ok => iprop(tcpEnd G cn false st ∗ sentAll γ.u (out ++ [l].take k) ∗
        ⌜∃ d d', WriteOutcome st d [l] k ok d'⌝)) $$ [Hhdr Hend Hout]
    as %n %err ⟨%k, %okw, ⟨Hend, Hout, %Hwr⟩, Hhdr, %Hn⟩
  · iframe Hc Hhdr
    iapply wire.write_au framedN cn false γ.u st out [l] $$ HinvU Hend Hout
  obtain ⟨-, Hnil, Herr⟩ := Hn
  cases okw
  · obtain ⟨pe, rfl⟩ := Herr rfl
    wp_auto
    iapply HΦ
    iexists _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  rw [Hnil rfl]
  obtain ⟨d, d', Hwr⟩ := Hwr
  obtain rfl := wire.writeOutcome_ok Hwr
  rw [show List.take [l].length [l] = [l] from rfl]
  wp_auto
  -- the request
  wp_apply wp_Write t cn false srvAddr req reqbs (DFrac.own 1)
      (fun k ok => iprop(tcpEnd G cn false st ∗ sentAll γ.u ((out ++ [l]) ++ reqbs.take k) ∗
        ⌜∃ d d', WriteOutcome st d reqbs k ok d'⌝)) $$ [Hreq Hend Hout]
    as %n' %err' ⟨%k', %okw', ⟨Hend, Hout, %Hwr'⟩, Hreq, %Hn'⟩
  · iframe Hc Hreq
    iapply wire.write_au framedN cn false γ.u st (out ++ [l]) reqbs $$ HinvU Hend Hout
  obtain ⟨-, Hnil', Herr'⟩ := Hn'
  cases okw'
  · obtain ⟨pe, rfl⟩ := Herr' rfl
    wp_auto
    iapply HΦ
    iexists _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  rw [Hnil' rfl]
  obtain ⟨d, d', Hwr'⟩ := Hwr'
  obtain rfl := wire.writeOutcome_ok Hwr'
  rw [List.take_of_length_le (Nat.le_refl reqbs.length)]
  wp_auto
  -- the reply's header
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %rhdr ⟨Hrhdr, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
      rhdr _ (readP γ.d cn false st out) eof $$ [Hrhdr Hend Hr]
    as %ok ⟨%got1, %bs1, HP, Hrhdr, %Hres1⟩
  · iframe Hrhdr Heof
    isplitr
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hr]
    · iapply readP_nil
      iframe Hend Hr Hlb0
    · iapply wire.read_acc framedN cn false γ.d st out $$ HinvD
  unfold readP
  icases HP with ⟨Hend, Hr, #HlbA⟩
  cases ok
  · wp_auto
    iapply HΦ
    iexists _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  obtain ⟨Hlen1, -, Hgot1⟩ := Hres1
  have Hgot1 := Hgot1 rfl
  subst Hgot1
  (try simp only [↓reduceIte])
  imod client_check' γm cn γ _ (out ++ got1) $$ HInv Hname Hout HlbA with ⟨%HpA, Hout⟩
  have hbs1 : got1 = [l] := by
    rw [List.append_assoc] at HpA
    exact prefix_one ((List.prefix_append_right_inj out).1 HpA) (by simpa using Hlen1)
  subst hbs1
  wp_auto
  ihave %Hhl' := ownSlice_len $$ Hrhdr
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rhdr.len by
    simp at Hhl'; word)]
  wp_apply wp_load_slice_index rhdr (sint.Z (W64 0)) [l] (DFrac.own 1) l (by decide) $$ [Hrhdr]
    as Hrhdr
  · iframe Hrhdr
    ipureintro; rfl
  (try wp_auto)
  -- the reply: as many bytes as the request has
  have hn : sint.nat (W64 (uint.Z l)) = reqbs.length := by
    rw [← hl, Hrl.1]; simp only [Hrl.1] at hreq; word
  wp_apply (wp_slice_make2 (V := w8) (W64 (uint.Z l))) as %resp ⟨Hresp, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
      resp _ (readP γ.d cn false st (out ++ [l])) eof $$ [Hresp Hend Hr]
    as %ok ⟨%got2, %bs2, HP, Hresp, %Hres2⟩
  · iframe Hresp Heof
    isplitr
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hr]
    · iapply readP_nil
      iframe Hend Hr HlbA
    · iapply wire.read_acc framedN cn false γ.d st (out ++ [l]) $$ HinvD
  unfold readP
  icases HP with ⟨Hend, Hr, #HlbB⟩
  cases ok
  · wp_auto
    iapply HΦ
    iexists _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  obtain ⟨Hlen2, -, Hgot2⟩ := Hres2
  have Hgot2 := Hgot2 rfl
  subst Hgot2
  (try simp only [↓reduceIte])
  imod client_check' γm cn γ _ ((out ++ [l]) ++ got2) $$ HInv Hname Hout HlbB with ⟨%HpB, Hout⟩
  have hbs2 : got2 = reqbs := by
    have hp := (List.prefix_append_right_inj (out ++ [l])).1 HpB
    exact hp.eq_of_length (by rw [Hlen2, List.length_replicate, hn])
  subst hbs2
  wp_auto
  wp_apply wp_bytes_to_string resp got2 (DFrac.own 1) $$ Hresp as Hresp
  (try wp_auto)
  wp_apply wp_bytes_to_string req got2 (DFrac.own 1) $$ Hreq as Hreq
  (try wp_auto)
  iapply HΦ
  iexists (out ++ [l]) ++ got2
  simp only [↓reduceIte]
  iframe Hend Hout Hr HlbB


theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases framedInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => dialerProto γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hd⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply dial_both_au addrN srvAddr (connProto γm) (fun cn => dialerProto γm cn) $$ HaddrInv
      iintro %cn #Hat Hd Ha
      iapply framed_deposit γm cn $$ HInv Hat Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold dialerProto
    icases Hd with ⟨%γ, Hend, Hout, Hr, #Hlb0, #Hname⟩
    ihave #HinvU := framed_upInv γm cn γ $$ HInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"a") TcpEnd.fresh [] eof
        (by decide) $$ [Hsl Hend Hout Hr]
      as %ok1 ⟨%out1, Hend, Hout, Hres1⟩
    · iframe Hinvs Hname Hsl Hend Hout Hr Hlb0 Heof
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    cases ok1
    · -- the first exchange failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_drop_au framedN cn false γ.u _ $$ HinvU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hres1 with ⟨Hr, #Hlb1⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"bcd") TcpEnd.fresh out1 eof
        (by decide) $$ [Hsl Hend Hout Hr]
      as %ok2 ⟨%out2, Hend, Hout, Hres2⟩
    · iframe Hinvs Hname Hsl Hend Hout Hr Hlb1 Heof
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    cases ok2
    · -- the second exchange failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_drop_au framedN cn false γ.u _ $$ HinvU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hres2 with ⟨Hr, #Hlb2⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"hello") TcpEnd.fresh out2 eof
        (by decide) $$ [Hsl Hend Hout Hr]
      as %ok3 ⟨%out3, Hend, -, -⟩
    · iframe Hinvs Hname Hsl Hend Hout Hr Hlb2 Heof
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend]
      as %err' ⟨%ok', -, -⟩
    · iframe Hca
      iapply close_drop_au framedN cn false γ.u _ $$ HinvU Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial


theorem wp_SendJunk
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! SendJunk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases framedInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => dialerProto γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hd⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply dial_both_au addrN srvAddr (connProto γm) (fun cn => dialerProto γm cn) $$ HaddrInv
      iintro %cn #Hat Hd Ha
      iapply framed_deposit γm cn $$ HInv Hat Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold dialerProto
    icases Hd with ⟨%γ, Hend, Hout, -, -, #Hname⟩
    ihave #HinvU := framed_upInv γm cn γ $$ HInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗
          sentAll γ.u ([] ++ (go!"\x09xyz").take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d (go!"\x09xyz") k ok d'⌝))
        $$ [Hsl Hend Hout]
      as %n %err ⟨%k, %okw, ⟨Hend, -, -⟩, Hsl, -⟩
    · iframe Hca Hsl
      iapply wire.write_au framedN cn false γ.u TcpEnd.fresh [] _ $$ HinvU Hend Hout
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hca
      iapply close_drop_au framedN cn false γ.u _ $$ HinvU Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial

/-- `io.EOF`'s value, from the package's initialization. -/
theorem eof_init :
    isPkgInit (PROP := IProp GF) pkg ⊢ ∃ eof : GoInterface, globalAddr io.EOF ↦□ eof := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  iexists _
  iexact Heof

theorem wp_Server
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! Server)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_ReadFull wp_Write wp_Close γm eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

theorem wp_Client
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! Client)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Call wp_Dial wp_ReadFull wp_Write wp_Close γm h eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

theorem wp_Junk
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! Junk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  (try wp_auto)
  wp_apply wp_SendJunk wp_Dial wp_Write wp_Close γm h $$ []
  · iframe Hinvs Hplan
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.net.framed
end Perennial
