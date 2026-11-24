/-
The proofs of `examples/net/framed`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: the loop's invariant: the server has read `sent` from the up direction (its reader
  half, `rcvdAll`), which the dialer has written (`sentLb`), and written back exactly `sent` (its
  half of the view, `srvView`). An iteration reads a header `[h]` and `h` bytes (`wire.ReadFull`
  through `wire.read_acc`), which extend `sent`, and writes them back, each `Write` through the
  writer predicate `srvWriteP` and the accessor `srv_write_acc` (each step `server_write_au`: what
  it writes is in what it has read); any failure breaks the loop, and the close follows.
* `Serve`: `Listen` (of `SrvAddr` itself, at the server's host in the plan: `listenAt_self`), then
  the accept loop (`wire.accept_lis_au`: each accepted connection's protocol, an abandoned dial's
  too, on which the server reads EOF and stops).
* Errors: every failure, whatever its kind (`closed`, `timeout`, `sys`; a `Write` that fails after
  some of its steps appended bytes included), is a non-nil `*OpError` (`net.resErr_netErr`), so the
  code's `err != nil` test takes the failure branch, which stops writing; success (`res = none`)
  has `err = nil`, and a `Write` that succeeds wrote all its bytes (`net.Conn.Write.spec`'s post,
  `res = none → w = bs`). `poll.ErrDeadlineExceeded`'s value (`wire.ed_init`) is a parameter of
  every `Write` and `ReadFull`.
* `exchange`: the client's end with `out` written up and as many bytes read down; the writes of the
  header `[len(req)]` and of `req` (`wire.writeP`, `wire.write_acc`: each step extends the writer's
  `sentAll`), then the full reads of the reply's header and
  payload. Both are lower bounds of the server's bytes, so prefixes of the client's own
  `out ++ [len(req)] ++ req` (`client_check`): the reply's header is `len(req)` and the reply `req`,
  so the check does not panic, and the end has again read as many bytes as it has written.
* `Call`: the dial (`wire.dial_both_au`, the deposit `framed_deposit`, or `framed_deposit_ab` for
  an abandoned dial, after which the client returns), three `exchange`s, the close.
* `SendJunk`: the dial (as `Call`'s), a write of its own bytes, the close.

The commands' `main`s (`cmd/<node>/Main.lean`) call `Serve`, `Call` and `SendJunk`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.Defs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Perennial.Proof.io
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv DirNames dirInv sentAll sentLb rcvdAll readP writeP)

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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : framed.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `wire.readP` before any byte of the call is read. -/
theorem readP_nil (γ : DirNames) (c : Nat) (s : Bool) (st : NetEnd) (R : List w8) :
    netEnd G c s st ∗ rcvdAll (Gg := hG.goose_globalGS) γ R ∗ sentLb γ R ⊢ readP γ c s st R [] := by
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
    (γm : GName) (c : GoInterface) (cn : Nat) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn framedInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HInv⟩, ⟨%t, %la, %ra, %Hct, #Hc⟩, ⟨%γ, Hend, Hr, #Hlb0, Hv, #Hname⟩, #Heof, #Hed⟩
  subst Hct
  ihave #HinvU := framed_upInv' γm cn γ $$ HInv Hname
  ihave #HinvD := framed_downInv γm cn γ $$ HInv Hname
  wp_auto
  ihave HI : (∃ (sent : List w8),
      "Hend" ∷ netEnd G cn true NetEnd.fresh ∗ "Hr" ∷ rcvdAll γ.u sent ∗
      "#Hlb" ∷ sentLb γ.u sent ∗ "Hv" ∷ srvView γ.v sent : IProp GF) $$ [Hend Hr Hv]
  · iexists []
    iframe Hend Hr Hv Hlb0
  wp_for HI
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %hdr ⟨Hhdr, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      hdr _ (readP γ.u cn true NetEnd.fresh sent) eof ed $$ [Hhdr Hend Hr]
    as %ok ⟨%got1, %bs1, HP, Hhdr, %Hres1⟩
  · iframe Hhdr Heof Hed
    isplitr
    · unfold net.isConn
      iexists t, la, ra
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hr]
    · iapply readP_nil
      iframe Hend Hr Hlb
    · iapply wire.read_acc framedN cn true γ.u NetEnd.fresh sent $$ HinvU
  unfold readP
  icases HP with ⟨Hend, Hr, #Hlb1⟩
  cases ok
  · -- the read failed: break, then close
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend] as %err ⟨%res', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au framedN cn true γ.d _ $$ HinvD Hend
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
      pl _ (readP γ.u cn true NetEnd.fresh (sent ++ [h])) eof ed $$ [Hpl Hend Hr]
    as %ok ⟨%got2, %bs2, HP, Hpl, %Hres2⟩
  · iframe Hpl Heof Hed
    isplitr
    · unfold net.isConn
      iexists t, la, ra
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hr]
    · iapply readP_nil
      iframe Hend Hr Hlb1
    · iapply wire.read_acc framedN cn true γ.u NetEnd.fresh (sent ++ [h]) $$ HinvU
  unfold readP
  icases HP with ⟨Hend, Hr, #Hlb2⟩
  cases ok
  · -- the read failed: break, then close
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend] as %err ⟨%res', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au framedN cn true γ.d _ $$ HinvD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨-, -, Hgot2⟩ := Hres2
  have Hgot2 := Hgot2 rfl
  subst Hgot2
  (try simp only [↓reduceIte])
  wp_auto
  -- echo the header
  wp_apply wp_Write t cn true srvAddr la ra hdr [h] (DFrac.own 1) ed
      (fun w _ => srvWriteP γ cn NetEnd.fresh sent w) $$ [Hhdr Hend Hv]
    as %n %err ⟨%w, %res, HP, Hhdr, %Hw, #Herr⟩
  · iframe Hc Hhdr Hed
    isplitl [Hend Hv]
    · iapply srvWriteP_init
      iframe Hend Hv
    · iapply srv_write_acc γm cn γ sent [h] ((sent ++ [h]) ++ got2) NetEnd.fresh
        (List.prefix_append _ _) $$ HInv Hname Hlb2
  unfold srvWriteP
  icases HP with ⟨Hend, Hv⟩
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hre
  cases res
  case some ek =>
    -- the write failed: break, then close
    obtain ⟨pe, rfl⟩ := Hre.2 (Option.some_ne_none _)
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend] as %err ⟨%res', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au framedN cn true γ.d _ $$ HinvD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain rfl := Hre.1 rfl
  obtain rfl := Hw.2.2.1 rfl
  wp_auto
  -- echo the payload
  wp_apply wp_Write t cn true srvAddr la ra pl got2 (DFrac.own 1) ed
      (fun w _ => srvWriteP γ cn NetEnd.fresh (sent ++ [h]) w) $$ [Hpl Hend Hv]
    as %n' %err' ⟨%w', %res, HP, Hpl, %Hw', #Herr'⟩
  · iframe Hc Hpl Hed
    isplitl [Hend Hv]
    · iapply srvWriteP_init
      iframe Hend Hv
    · iapply srv_write_acc γm cn γ (sent ++ [h]) got2 ((sent ++ [h]) ++ got2) NetEnd.fresh
        (List.prefix_refl _) $$ HInv Hname Hlb2
  unfold srvWriteP
  icases HP with ⟨Hend, Hv⟩
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr' with %Hre
  cases res
  case some ek =>
    -- the write failed: break, then close
    obtain ⟨pe, rfl⟩ := Hre.2 (Option.some_ne_none _)
    wp_auto
    wp_for_post
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend] as %err ⟨%res', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au framedN cn true γ.d _ $$ HinvD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain rfl := Hre.1 rfl
  have Hw'e := Hw'.2.2.1 rfl
  subst w'
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
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗
        ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hplan, #Heof, #Hed⟩
  icases framedInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HInv⟩
  (try wp_auto)
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp srvAddr $$ []
    as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, %ex, -, #Herr, -⟩)
  · iframe %Hplan
    iapply wire.listen_au addrN srvAddr _ $$ HaddrInv
  · -- listening: the accept loop
    subst Herr
    unfold net.isListener
    icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true :
      IProp GF) $$ [Hlis]
    · iexact Hlis
    wp_for HI
    wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x srvAddr
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%k, Hlis, #Herr⟩)
    · iframe Hlt Hla
      iapply wire.accept_lis_au addrN srvAddr (connProto γm) _ l true $$ HaddrInv Hlis
    · -- a connection: serve it
      subst Herr
      wp_auto
      wp_apply wp_serveConn wp_ReadFull wp_Write wp_Close γm c cn eof ed $$ [Hproto]
      · iframe Hinvs Hc Hproto Heof Hed
      wp_for_post
      iframe
    · -- a failure: go on
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hre
      obtain ⟨pe, rfl⟩ := Hre.2 (Option.some_ne_none _)
      wp_auto
      wp_for_post
      iframe
  · -- not listening: return
    icases net.opErr_netErr _ _ _ _ _ $$ Herr with %Hre
    obtain ⟨pe, rfl⟩ := Hre
    wp_auto
    iapply HΦ
    itrivial

theorem wp_exchange
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (γ : FNames) (req : GoSlice) (reqbs : List w8)
    (st : NetEnd) (out : List w8) (eof ed : GoInterface) (hreq : reqbs.length < 256) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ framedName γm cn γ ∗
        net.isConn c cn false srvAddr ∗ req ↦* reqbs ∗ netEnd G cn false st ∗
        sentAll γ.u out ∗ rcvdAll γ.d out ∗ sentLb γ.d out ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (App (Val (@! exchange)) (Val #c)) (Val #req))
    {{ (ok : Bool), RET #ok; ∃ out' : List w8, netEnd G cn false st ∗ sentAll γ.u out' ∗
        if ok then rcvdAll γ.d out' ∗ sentLb γ.d out' else True }} := by
  unfold net.isConn framedInvs
  wp_start as ⟨⟨#HaddrInv, #HInv⟩, #Hname, ⟨%t, %la, %ra, %Hct, #Hc⟩, Hreq, Hend, Hout, Hr, #Hlb0, #Heof, #Hed⟩
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
  wp_apply wp_Write t cn false srvAddr la ra hdr [l] (DFrac.own 1) ed
      (writeP γ.u cn false st out) $$ [Hhdr Hend Hout]
    as %n %err ⟨%w, %res, HP, Hhdr, %Hw, #Herr⟩
  · iframe Hc Hhdr Hed
    isplitl [Hend Hout]
    · iapply wire.writeP_init
      iframe Hend Hout
    · iapply wire.write_acc framedN cn false γ.u st out [l] $$ HinvU
  unfold writeP
  icases HP with ⟨Hend, Hout, -⟩
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hre
  cases res
  case some ek =>
    obtain ⟨pe, rfl⟩ := Hre.2 (Option.some_ne_none _)
    wp_auto
    iapply HΦ
    iexists _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  obtain rfl := Hre.1 rfl
  obtain rfl := Hw.2.2.1 rfl
  wp_auto
  -- the request
  wp_apply wp_Write t cn false srvAddr la ra req reqbs (DFrac.own 1) ed
      (writeP γ.u cn false st (out ++ [l])) $$ [Hreq Hend Hout]
    as %n' %err' ⟨%w', %res, HP, Hreq, %Hw', #Herr'⟩
  · iframe Hc Hreq Hed
    isplitl [Hend Hout]
    · iapply wire.writeP_init
      iframe Hend Hout
    · iapply wire.write_acc framedN cn false γ.u st (out ++ [l]) reqbs $$ HinvU
  unfold writeP
  icases HP with ⟨Hend, Hout, -⟩
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr' with %Hre
  cases res
  case some ek =>
    obtain ⟨pe, rfl⟩ := Hre.2 (Option.some_ne_none _)
    wp_auto
    iapply HΦ
    iexists _
    iframe Hend Hout
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  obtain rfl := Hre.1 rfl
  have Hw'e := Hw'.2.2.1 rfl
  subst w'
  wp_auto
  -- the reply's header
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %rhdr ⟨Hrhdr, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
      rhdr _ (readP γ.d cn false st out) eof ed $$ [Hrhdr Hend Hr]
    as %ok ⟨%got1, %bs1, HP, Hrhdr, %Hres1⟩
  · iframe Hrhdr Heof Hed
    isplitr
    · unfold net.isConn
      iexists t, la, ra
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
      resp _ (readP γ.d cn false st (out ++ [l])) eof ed $$ [Hresp Hend Hr]
    as %ok ⟨%got2, %bs2, HP, Hresp, %Hres2⟩
  · iframe Hresp Heof Hed
    isplitr
    · unfold net.isConn
      iexists t, la, ra
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
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof, #Hed⟩
  icases framedInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HInv⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => dialerProto γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hd⟩ | ⟨-, %x, -, #Herr⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_both_au addrN srvAddr (connProto γm) (fun cn => dialerProto γm cn) $$
        HaddrInv [] []
      · iintro %cn #Hat Hd Ha
        iapply framed_deposit γm cn $$ HInv Hat Hd Ha
      · iintro %cn #Hat He Hd Ha
        iapply framed_deposit_ab γm cn $$ HInv Hat He Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    unfold dialerProto
    icases Hd with ⟨%γ, Hend, Hout, Hr, #Hlb0, #Hname⟩
    ihave #HinvU := framed_upInv γm cn γ $$ HInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"a") NetEnd.fresh [] eof ed
        (by decide) $$ [Hsl Hend Hout Hr]
      as %ok1 ⟨%out1, Hend, Hout, Hres1⟩
    · iframe Hinvs Hname Hsl Hend Hout Hr Hlb0 Heof Hed
      unfold net.isConn
      iexists t, la, ra
      iframe Hca
      ipureintro; rfl
    cases ok1
    · -- the first exchange failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au framedN cn false γ.u _ $$ HinvU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hres1 with ⟨Hr, #Hlb1⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"bcd") NetEnd.fresh out1 eof ed
        (by decide) $$ [Hsl Hend Hout Hr]
      as %ok2 ⟨%out2, Hend, Hout, Hres2⟩
    · iframe Hinvs Hname Hsl Hend Hout Hr Hlb1 Heof Hed
      unfold net.isConn
      iexists t, la, ra
      iframe Hca
      ipureintro; rfl
    cases ok2
    · -- the second exchange failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au framedN cn false γ.u _ $$ HinvU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hres2 with ⟨Hr, #Hlb2⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_exchange wp_ReadFull wp_Write γm _ cn γ sl (go!"hello") NetEnd.fresh out2 eof ed
        (by decide) $$ [Hsl Hend Hout Hr]
      as %ok3 ⟨%out3, Hend, -, -⟩
    · iframe Hinvs Hname Hsl Hend Hout Hr Hlb2 Heof Hed
      unfold net.isConn
      iexists t, la, ra
      iframe Hca
      ipureintro; rfl
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err' ⟨%res', -, -⟩
    · iframe Hca
      iapply wire.close_drop_au framedN cn false γ.u _ $$ HinvU Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hre
    obtain ⟨pe, rfl⟩ := Hre.2 (Option.some_ne_none _)
    wp_auto
    iapply HΦ
    itrivial


theorem wp_SendJunk
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ framedInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! SendJunk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Hed⟩
  icases framedInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HInv⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => dialerProto γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hd⟩ | ⟨-, %x, -, #Herr⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_both_au addrN srvAddr (connProto γm) (fun cn => dialerProto γm cn) $$
        HaddrInv [] []
      · iintro %cn #Hat Hd Ha
        iapply framed_deposit γm cn $$ HInv Hat Hd Ha
      · iintro %cn #Hat He Hd Ha
        iapply framed_deposit_ab γm cn $$ HInv Hat He Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    unfold dialerProto
    icases Hd with ⟨%γ, Hend, Hout, -, -, #Hname⟩
    ihave #HinvU := framed_upInv γm cn γ $$ HInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr la ra sl _ (DFrac.own 1) ed
        (writeP γ.u cn false NetEnd.fresh []) $$ [Hsl Hend Hout]
      as %n %err ⟨%w, %res, HP, Hsl, -, -⟩
    · iframe Hca Hsl Hed
      isplitl [Hend Hout]
      · iapply wire.writeP_init
        iframe Hend Hout
      · iapply wire.write_acc framedN cn false γ.u NetEnd.fresh [] _ $$ HinvU
    unfold writeP
    icases HP with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%res', -, -⟩
    · iframe Hca
      iapply wire.close_drop_au framedN cn false γ.u _ $$ HinvU Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hre
    obtain ⟨pe, rfl⟩ := Hre.2 (Option.some_ne_none _)
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

end proof

end github_com.mit_pdos.etcd_grove.examples.net.framed
end Perennial
