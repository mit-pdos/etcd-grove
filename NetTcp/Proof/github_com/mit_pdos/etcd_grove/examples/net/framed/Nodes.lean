/-
The proofs of `examples/net/framed`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: the loop's invariant: the server has read `sent`, a prefix of the dialer's bytes
  (`tcpOutLb`, its end's read count `sent.length`), and written back exactly `sent` (its half of the
  connection's ghost variable, `srvView`). An iteration reads a header `[h]` and `h` bytes, which
  extend `sent` (`tcpOutLb_valid`), and writes them back (`server_write_au`: what it writes is in
  what it has read); any failure breaks the loop, and the close follows (`server_close_au`).
* `Serve`: `Listen`, then the accept loop (`wire.accept_au`: each accepted connection's protocol).
* `exchange`: the client's end with `out` written and as many bytes read (a prefix `sent0` of the
  server's); the writes of the header `[len(req)]` and of `req`, then the full reads of the reply's
  header and payload. Both are prefixes of the server's bytes, so of the client's own
  `out ++ [len(req)] ++ req` (`client_check`): the reply's header is `len(req)` and the reply `req`,
  so the check does not panic, and the end has again read as many bytes as it has written.
* `Call`: the dial (`wire.dial_au`, the deposit `framed_deposit`), three `exchange`s, the close.
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
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap)

namespace github_com.mit_pdos.etcd_grove.examples.net.framed

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.framed

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : framed.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- Of two comparable lists, the shorter is a prefix of the longer. -/
theorem prefix_of_le {α : Type} {a b : List α} (h : a <+: b ∨ b <+: a)
    (hl : a.length ≤ b.length) : a <+: b := by
  rcases h with h | h
  · exact h
  · rw [h.eq_of_length (Nat.le_antisymm h.length_le hl)]
    exact List.prefix_refl _

/-- A write that succeeded wrote all its bytes and left the end's state as it was. -/
theorem writeRes_ok {st st' : TcpEnd} {bs : GoString} {k : Nat} (h : WriteRes st bs k true st') :
    k = bs.length ∧ st' = st := by
  rcases h with ⟨-, -, h, -⟩ | ⟨-, ⟨hk, -, hst⟩ | ⟨-, h, -⟩⟩
  · cases h
  · exact ⟨hk, hst⟩
  · cases h

/-- The bytes after the `n` first of a prefix `a` of `O`, of length `n + m`. -/
theorem drop_of_prefix {α : Type} {a O : List α} (hp : a <+: O) (n m : Nat)
    (hl : a.length = n + m) : a.drop n = (O.drop n).take m := by
  rw [List.prefix_iff_eq_take.1 hp, hl, List.drop_take, Nat.add_sub_cancel_left]

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
  wp_start as ⟨⟨#HaddrInv, #HInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Hv, #Hname⟩, #Heof⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn true srvAddr $$ Hc
  imod tcpOutLb_nil (G (GF := GF)) cn false srvAddr $$ Hat with #Hlb0
  wp_auto
  ihave HI : (∃ (st : TcpEnd) (sent : GoString),
      "Hend" ∷ tcpEnd G cn true st sent.length ∗ "#Hlb" ∷ tcpOutLb G cn false sent ∗
      "Hv" ∷ srvView G γ sent : IProp GF) $$ [Hend Hv]
  · iexists TcpEnd.fresh, []
    iframe Hend Hv Hlb0
  wp_for HI
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %hdr ⟨Hhdr, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      hdr _ st sent.length sent eof rfl $$ [Hhdr Hend]
    as %ok ⟨%st1, %r1, %bs1, Hend, Hhdr, %Hlen1, Hres⟩
  · simp only [Bool.not_true]
    iframe Hhdr Hend Heof Hlb
    unfold net.isConn
    iexists t
    iframe Hc
    ipureintro; rfl
  cases ok
  · -- the read failed: break, then close
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st1 _ $$ HInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  simp only [↓reduceIte]
  icases Hres with ⟨%sent1, #Hlb1, %Hs1⟩
  obtain ⟨rfl, rfl, hsl1, hsd1⟩ := Hs1
  wp_auto
  ihave %Hhl := ownSlice_len $$ Hhdr
  obtain ⟨h, rfl⟩ : ∃ h, bs1 = [h] := List.length_eq_one_iff.1 (by simpa using Hlen1)
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z hdr.len by simp at Hhl; word)]
  wp_apply wp_load_slice_index hdr (sint.Z (W64 0)) [h] (DFrac.own 1) h (by decide) $$ [Hhdr]
    as Hhdr
  · iframe Hhdr
    ipureintro; rfl
  (try wp_auto)
  -- the header extends what was read
  icases tcpOutLb_valid _ cn false sent sent1 $$ Hlb Hlb1 with %Hpre1
  have hs1 : sent1 = sent ++ [h] := by
    have hp : sent <+: sent1 := prefix_of_le Hpre1 (by simp at hsl1; omega)
    rw [← hsd1]; exact (List.prefix_iff_eq_append.1 hp).symm
  subst hs1
  wp_apply (wp_slice_make2 (V := w8) (W64 (uint.Z h))) as %pl ⟨Hpl, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      pl _ st1 _ (sent ++ [h]) eof hsl1 $$ [Hpl Hend]
    as %ok ⟨%st2, %r2, %bs2, Hend, Hpl, %Hlen2, Hres⟩
  · simp only [Bool.not_true]
    iframe Hpl Hend Heof Hlb1
    unfold net.isConn
    iexists t
    iframe Hc
    ipureintro; rfl
  cases ok
  · -- the read failed: break, then close
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st2 _ $$ HInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  simp only [↓reduceIte]
  icases Hres with ⟨%sent2, #Hlb2, %Hs2⟩
  obtain ⟨rfl, rfl, hsl2, hsd2⟩ := Hs2
  icases tcpOutLb_valid _ cn false (sent ++ [h]) sent2 $$ Hlb1 Hlb2 with %Hpre2
  have hs2 : sent2 = (sent ++ [h]) ++ bs2 := by
    have hp : sent ++ [h] <+: sent2 :=
      prefix_of_le Hpre2 (by rw [hsl2, ← hsl1]; exact Nat.le_add_right _ _)
    rw [← hsd2, ← hsl1]; exact (List.prefix_iff_eq_append.1 hp).symm
  subst hs2
  rw [← hsl2]
  wp_auto
  -- echo the header
  wp_apply wp_Write t cn true srvAddr hdr [h] (DFrac.own 1)
      (fun k ok => iprop(∃ st3, ⌜WriteRes st2 [h] k ok st3⌝ ∗
        tcpEnd G cn true st3 (sent ++ [h] ++ bs2).length ∗ srvView G γ (sent ++ [h].take k)))
      $$ [Hhdr Hend Hv]
    as %n %err ⟨%k, %okw, ⟨%st3, %Hwr, Hend, Hv⟩, Hhdr, %Hn⟩
  · iframe Hc Hhdr
    iapply server_write_au γm cn γ sent [h] (sent ++ [h] ++ bs2) st2 _ (List.prefix_append _ _)
      $$ HInv Hname Hv Hlb2 Hend
  obtain ⟨-, Hnil, Herr⟩ := Hn
  cases okw
  · -- the write failed: break, then close
    obtain ⟨pe, rfl⟩ := Herr rfl
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st3 _ $$ HInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  rw [Hnil rfl]
  obtain ⟨rfl, hst3⟩ := writeRes_ok Hwr
  subst st3
  rw [show List.take [h].length [h] = [h] from rfl]
  wp_auto
  -- echo the payload
  wp_apply wp_Write t cn true srvAddr pl bs2 (DFrac.own 1)
      (fun k ok => iprop(∃ st4, ⌜WriteRes st2 bs2 k ok st4⌝ ∗
        tcpEnd G cn true st4 (sent ++ [h] ++ bs2).length ∗
        srvView G γ ((sent ++ [h]) ++ bs2.take k)))
      $$ [Hpl Hend Hv]
    as %n' %err' ⟨%k', %okw', ⟨%st4, %Hwr', Hend, Hv⟩, Hpl, %Hn'⟩
  · iframe Hc Hpl
    iapply server_write_au γm cn γ (sent ++ [h]) bs2 (sent ++ [h] ++ bs2) st2 _
      (List.prefix_refl _) $$ HInv Hname Hv Hlb2 Hend
  obtain ⟨-, Hnil', Herr'⟩ := Hn'
  cases okw'
  · -- the write failed: break, then close
    obtain ⟨pe, rfl⟩ := Herr' rfl
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st4 _ $$ HInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  rw [Hnil' rfl]
  obtain ⟨rfl, hst4⟩ := writeRes_ok Hwr'
  subst st4
  rw [List.take_of_length_le (Nat.le_refl bs2.length)]
  wp_auto
  wp_for_post
  iframe
  iexists st2, sent ++ [h] ++ bs2
  iframe Hend Hv Hlb2


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
  wp_apply wp_Listen srvAddr $$ Hplan as %li %err (⟨%Herr, %l, #Hli, Hlis⟩ | %Herr)
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
    wp_apply wp_Accept t l srvAddr true
        (tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%Herr, Hlis⟩)
    · iframe Hlt Hlis
      isplit
      · iintro Hl; iexact Hl
      · imod wire.accept_au addrN srvAddr (connProto γm) $$ HaddrInv with ⟨%S, Hp, Hk⟩
        imodintro
        iexists S
        iframe Hp
        iintro %cn %HcS Hp
        imod Hk $$ %cn %HcS Hp with Hproto
        imodintro
        iintro Hl -
        iframe Hl Hproto
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

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp : GoString) :
    ⊢ inv framedN (framedState (G (GF := GF)) γm) -∗ framedName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp ={⊤}=∗
      ⌜resp <+: out⌝ ∗ tcpOut G cn false out f :=
  client_check γm cn γ out f resp

theorem wp_exchange
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (γ : GName) (req : GoSlice) (reqbs : GoString)
    (st : TcpEnd) (out sent0 : GoString) (eof : GoInterface)
    (hreq : reqbs.length < 256) (hsent0 : sent0.length = out.length) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ framedName G γm cn γ ∗
        net.isConn c cn false srvAddr ∗ req ↦* reqbs ∗ tcpEnd G cn false st out.length ∗
        tcpOut G cn false out false ∗ tcpOutLb G cn true sent0 ∗ globalAddr io.EOF ↦□ eof }}
      (App (App (Val (@! exchange)) (Val #c)) (Val #req))
    {{ (ok : Bool), RET #ok; ∃ (st' : TcpEnd) (r' : Nat) (out' : GoString),
        tcpEnd G cn false st' r' ∗ tcpOut G cn false out' false ∗
        if ok then ∃ sent', tcpOutLb G cn true sent' ∗ ⌜sent'.length = r' ∧ r' = out'.length⌝
        else True }} := by
  unfold net.isConn framedInvs
  wp_start as ⟨⟨#HaddrInv, #HInv⟩, #Hname, ⟨%t, %Hct, #Hc⟩, Hreq, Hend, Hout, #Hlb0, #Heof⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn false srvAddr $$ Hc
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
      (fun k ok => iprop(∃ st', ⌜WriteRes st [l] k ok st'⌝ ∗ tcpEnd G cn false st' out.length ∗
        tcpOut G cn false (out ++ [l].take k) false)) $$ [Hhdr Hend Hout]
    as %n %err ⟨%k, %okw, ⟨%st1, %Hwr, Hend, Hout⟩, Hhdr, %Hn⟩
  · iframe Hc Hhdr
    iapply wire.owned_write_au cn false st out.length out false [l] $$ Hend Hout
  obtain ⟨-, Hnil, Herr⟩ := Hn
  cases okw
  · obtain ⟨pe, rfl⟩ := Herr rfl
    wp_auto
    iapply HΦ
    iexists st1, out.length, _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  rw [Hnil rfl]
  obtain ⟨rfl, hst1⟩ := writeRes_ok Hwr
  subst st1
  rw [show List.take [l].length [l] = [l] from rfl]
  wp_auto
  -- the request
  wp_apply wp_Write t cn false srvAddr req reqbs (DFrac.own 1)
      (fun k ok => iprop(∃ st', ⌜WriteRes st reqbs k ok st'⌝ ∗ tcpEnd G cn false st' out.length ∗
        tcpOut G cn false ((out ++ [l]) ++ reqbs.take k) false)) $$ [Hreq Hend Hout]
    as %n' %err' ⟨%k', %okw', ⟨%st2, %Hwr', Hend, Hout⟩, Hreq, %Hn'⟩
  · iframe Hc Hreq
    iapply wire.owned_write_au cn false st out.length (out ++ [l]) false reqbs $$ Hend Hout
  obtain ⟨-, Hnil', Herr'⟩ := Hn'
  cases okw'
  · obtain ⟨pe, rfl⟩ := Herr' rfl
    wp_auto
    iapply HΦ
    iexists st2, out.length, _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  rw [Hnil' rfl]
  obtain ⟨rfl, hst2⟩ := writeRes_ok Hwr'
  subst st2
  rw [List.take_of_length_le (Nat.le_refl reqbs.length)]
  wp_auto
  -- the reply's header
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %rhdr ⟨Hrhdr, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
      rhdr _ st out.length sent0 eof hsent0 $$ [Hrhdr Hend]
    as %ok ⟨%st1, %r1, %bs1, Hend, Hrhdr, %Hlen1, Hres⟩
  · simp only [Bool.not_false]
    iframe Hrhdr Hend Heof Hlb0
    unfold net.isConn
    iexists t
    iframe Hc
    ipureintro; rfl
  cases ok
  · wp_auto
    iapply HΦ
    iexists st1, r1, _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  simp only [↓reduceIte]
  icases Hres with ⟨%sentA, #HlbA, %HsA⟩
  obtain ⟨rfl, rfl, hslA, hsdA⟩ := HsA
  imod client_check' γm cn γ _ false sentA $$ HInv Hname Hout HlbA with ⟨%HpA, Hout⟩
  have hO : List.drop out.length (out ++ [l] ++ reqbs) = l :: reqbs := by simp
  have hbs1 : bs1 = [l] := by
    rw [← hsdA, drop_of_prefix HpA out.length 1 (by simpa using hslA), hO]; rfl
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
      resp _ st1 _ sentA eof hslA $$ [Hresp Hend]
    as %ok ⟨%st2, %r2, %bs2, Hend, Hresp, %Hlen2, Hres⟩
  · simp only [Bool.not_false]
    iframe Hresp Hend Heof HlbA
    unfold net.isConn
    iexists t
    iframe Hc
    ipureintro; rfl
  cases ok
  · wp_auto
    iapply HΦ
    iexists st2, r2, _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  simp only [↓reduceIte]
  icases Hres with ⟨%sentB, #HlbB, %HsB⟩
  obtain ⟨rfl, rfl, hslB, hsdB⟩ := HsB
  imod client_check' γm cn γ _ false sentB $$ HInv Hname Hout HlbB with ⟨%HpB, Hout⟩
  have hbs2 : bs2 = reqbs := by
    have hO' : List.drop (out.length + 1) (out ++ [l] ++ reqbs) = reqbs := by simp
    rw [← hsdB, show (List.replicate 1 (zero_val w8)).length = 1 from rfl,
      drop_of_prefix HpB (out.length + 1) reqbs.length (by rw [hslB, List.length_replicate, List.length_replicate, hn]), hO',
      List.take_of_length_le (Nat.le_refl _)]
  subst hbs2
  wp_auto
  wp_apply wp_bytes_to_string resp bs2 (DFrac.own 1) $$ Hresp as Hresp
  (try wp_auto)
  wp_apply wp_bytes_to_string req bs2 (DFrac.own 1) $$ Hreq as Hreq
  (try wp_auto)
  iapply HΦ
  iexists st2, _, out ++ [l] ++ bs2
  iframe Hend Hout
  simp only [↓reduceIte]
  iexists sentB
  iframe HlbB
  ipureintro
  refine ⟨hslB, ?_⟩
  rw [List.length_replicate, List.length_replicate, hn]
  simp only [List.length_append, List.length_cons, List.length_nil]


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
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, framedName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm)
        (fun cn => iprop(∃ γ, framedName G γm cn γ)) $$ HaddrInv
      iintro %cn #Hat Ha
      iapply framed_deposit γm cn $$ HInv Hat Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    ihave #Hat := net.connAt_conn t cn false srvAddr $$ Hca
    imod tcpOutLb_nil (G (GF := GF)) cn true srvAddr $$ Hat with #Hlb0
    unfold tcpFreshEnd
    icases Hd with ⟨Hend, Hout⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"a") TcpEnd.fresh [] [] eof
        (by decide) rfl
        $$ [Hsl Hend Hout]
      as %ok1 ⟨%st1, %r1, %out1, Hend, Hout, Hres1⟩
    · iframe Hinvs Hname Hsl Hend Hout Hlb0 Heof
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    cases ok1
    · -- the first exchange failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout]
        as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hres1 with ⟨%sent1, #Hlb1, %Hs1⟩
    obtain ⟨hs1, rfl⟩ := Hs1
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"bcd") st1 out1 sent1 eof
        (by decide) hs1 $$ [Hsl Hend Hout]
      as %ok2 ⟨%st2, %r2, %out2, Hend, Hout, Hres2⟩
    · iframe Hinvs Hname Hsl Hend Hout Hlb1 Heof
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    cases ok2
    · -- the second exchange failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout]
        as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hres2 with ⟨%sent2, #Hlb2, %Hs2⟩
    obtain ⟨hs2, rfl⟩ := Hs2
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"hello") st2 out2 sent2 eof
        (by decide) hs2 $$ [Hsl Hend Hout]
      as %ok3 ⟨%st3, %r3, %out3, Hend, Hout, -⟩
    · iframe Hinvs Hname Hsl Hend Hout Hlb2 Heof
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout]
      as %err' ⟨%ok', -, -⟩
    · iframe Hca
      iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
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
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, framedName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm)
        (fun cn => iprop(∃ γ, framedName G γm cn γ)) $$ HaddrInv
      iintro %cn #Hat Ha
      iapply framed_deposit γm cn $$ HInv Hat Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold tcpFreshEnd
    icases Hd with ⟨Hend, Hout⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(∃ st', ⌜WriteRes TcpEnd.fresh (go!"\x09xyz") k ok st'⌝ ∗
          tcpEnd G cn false st' 0 ∗ tcpOut G cn false ([] ++ (go!"\x09xyz").take k) false))
        $$ [Hsl Hend Hout]
      as %n %err ⟨%k, %okw, ⟨%st', -, Hend, Hout⟩, Hsl, -⟩
    · iframe Hca Hsl
      iapply wire.owned_write_au cn false _ 0 [] false _ $$ Hend Hout
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
    · iframe Hca
      iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
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
