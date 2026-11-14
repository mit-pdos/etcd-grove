/-
The proofs of `examples/net/duplex`'s functions, over the specs of `net` and `wire` (hypotheses,
linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: a loop of `Read`s into a 16-byte buffer, each read's bytes written back
  (`server_write_au`: they follow the server's bytes in the dialer's), until a failure or EOF;
  then the close (`server_close_au`). The server thread owns its end.
* `Serve`: `Listen`, then the accept loop (`wire.accept_au`).
* `writeAll`: the writer goroutine, the bytes 1..4 one at a time (`cli_write_au`).
* `Call`: the dial (`wire.dial_au`, the deposit `dup_deposit`), the client's end put in its
  invariant (`cliInv_alloc`), `writeAll` forked, then four `wire.ReadFull`s of one byte through the
  reader's accessor (`cli_read_acc`), each checked (`client_check`: the byte at position `i - 1`
  is `i`), and the close (`cli_close_au`).
* `Server`, `Client`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Defs
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFullNew
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

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.duplex

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : duplex.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (γ γr γw : GName) (resp : GoString) :
    ⊢ inv srvN (srvState (G (GF := GF)) γm) -∗ srvName G γm cn γ -∗
      inv cliN (cliInv G cn γr γw) -∗ tcpOutLb G cn true resp ={⊤}=∗ ⌜resp <+: dseq⌝ :=
  client_check γm cn γ γr γw resp

/-- A server-side close, its end's state dropped. -/
theorem wp_srvClose (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (t : Loc) (cn : Nat) (γ : GName) (st : TcpEnd) (r : Nat) :
    {{ inv srvN (srvState (G (GF := GF)) γm) ∗ srvName G γm cn γ ∗ net.connAt t cn true srvAddr ∗
        tcpEnd G cn true st r }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hinv, #Hname, #Hc, Hend⟩ HΦ
  wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok, -, -⟩
  · iframe Hc
    iapply server_close_au γm cn γ st r $$ Hinv Hname Hend
  iapply HΦ
  itrivial

theorem wp_serveConn
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ dupInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn dupInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HsrvInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Hh, #Hname⟩, #Heof⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn true srvAddr $$ Hc
  imod tcpOutLb_nil (G (GF := GF)) cn false srvAddr $$ Hat with #Hlb0
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 16)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hlen0 := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  have Hbl16 : sint.Z buf.len = 16 := by
    obtain ⟨h1, h2⟩ := Hlen0
    simp only [List.length_replicate] at h1
    word
  ihave HI : (∃ (st : TcpEnd) (sR : GoString) (bs : List w8),
      "Hend" ∷ tcpEnd G cn true st sR.length ∗ "Hh" ∷ half G γ sR ∗
      "#Hlb" ∷ tcpOutLb G cn false sR ∗ "Hbuf" ∷ buf ↦* bs ∗ "%Hbl" ∷ ⌜bs.length = 16⌝ : IProp GF)
      $$ [Hend Hh Hbuf]
  · iexists TcpEnd.fresh, [], _
    iframe Hend Hh Hlb0 Hbuf
    ipureintro; rfl
  wp_for HI
  wp_apply wp_Read t cn true srvAddr buf bs eof
      (fun res => ReadPost (G (GF := GF)) cn true buf.len st sR.length res) $$ [Hbuf Hend]
    as %k %err ⟨%bs1, %code, %bs', HQ, Hbuf, %Hout⟩
  · iframe Hc Hbuf Heof
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    iexists st, sR.length
    iframe Hend
    iintro %res Hpost
    imod Hcl
    imodintro
    iexact Hpost
  iunfold ReadPost at HQ
  icases HQ with (⟨%Hr, Hend⟩ | ⟨%Hr, Hend⟩ | ⟨%bs2, %sent2, %Hr, #Hlb2, Hend⟩ |
    ⟨%sent2, %Hr, #Hfin, Hend⟩)
  · -- a failure: break, close
    obtain ⟨rfl, rfl⟩ := wire.readRes_inj Hr
    rcases Hout with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, -, rfl, ⟨pe, rfl⟩, rfl⟩
    · cases h0
    · cases h1
    wp_auto
    wp_for_post
    (try wp_auto)
    wp_apply wp_srvClose wp_Close γm t cn γ _ _ $$ [Hend] as %err' -
    · iframe HsrvInv Hname Hc Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- an empty buffer: not with 16 bytes
    obtain ⟨-, hz, -⟩ := Hr
    exfalso
    rw [hz] at Hbl16
    exact absurd Hbl16 (by decide)
  · -- bytes: write them back
    obtain ⟨hcl, hb1, hbn, hsl2, hsd2, hres⟩ := Hr
    obtain ⟨rfl, rfl⟩ := wire.readRes_inj hres
    rcases Hout with ⟨-, hk', rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h0, -⟩
    · have hbn' : bs1.length ≤ 16 := by
        have : BitVec.toNat buf.len = 16 := by word
        omega
      have hk : sint.nat k = bs1.length := by rw [hk', Hbl]; omega
      have hk0 : sint.Z (W64 0) < sint.Z k := by
        have : (0 : Int) < sint.Z k := by
          have := hk; word
        simpa using this
      rw [decide_eq_true hk0]
      wp_auto
      have hkl : sint.Z k ≤ sint.Z buf.len := by
        have : (sint.nat k : Int) ≤ 16 := by omega
        rw [Hbl16]; word
      rw [ite_eq_left ⟨by decide, by word, Int.le_trans hkl Hwf.2⟩]
      icases (ownSlice_split_all k buf _ _ ⟨by word, hkl⟩).1 $$ Hbuf with ⟨Hb1, Hb2⟩
      have htk : (List.take bs.length bs1 ++ List.drop bs1.length bs).take (sint.nat k) = bs1 := by
        rw [hk, Hbl, List.take_of_length_le hbn', List.take_left' rfl]
      isimp only [htk] at Hb1
      rw [show (!true) = false from rfl]
      icases tcpOutLb_valid _ cn false sR sent2 $$ Hlb Hlb2 with %Hpre
      have hsent : sent2 = sR ++ bs1 := by
        have hp : sR <+: sent2 := by
          rcases Hpre with h | h
          · exact h
          · have := h.length_le; omega
        obtain ⟨tl, rfl⟩ := hp
        rw [← hsd2, List.drop_left]
      (try wp_auto)
      wp_apply wp_Write t cn true srvAddr (slice.slice buf w8 (W64 0) k) bs1 (DFrac.own 1)
          (fun kw ok => iprop(∃ st'', ⌜WriteRes st bs1 kw ok st''⌝ ∗
            tcpEnd G cn true st'' (List.length sR + bs1.length) ∗ half G γ (sR ++ bs1.take kw)))
          $$ [Hb1 Hend Hh]
        as %n %werr ⟨%kw, %okw, ⟨%st'', %Hwr, Hend, Hh⟩, Hb1, %Hn⟩
      · iframe Hc Hb1
        iapply server_write_au γm cn γ sR bs1 sent2 st _ (by rw [hsent]; exact List.prefix_refl _)
          $$ HsrvInv Hname Hh Hlb2 Hend
      obtain ⟨-, Hnil, Herr⟩ := Hn
      ihave Hbuf := wire.buf_rejoin buf k _ _ (by rw [hk]) ⟨by word, hkl⟩ $$ Hb1 Hb2
      cases okw
      · -- the write failed: break, close
        obtain ⟨pe, rfl⟩ := Herr rfl
        wp_auto
        wp_for_post
        (try wp_auto)
        wp_apply wp_srvClose wp_Close γm t cn γ _ _ $$ [Hend] as %err' -
        · iframe HsrvInv Hname Hc Hend
        (try wp_auto)
        iapply HΦ
        itrivial
      · rw [Hnil rfl]
        obtain ⟨rfl, rfl⟩ : kw = bs1.length ∧ st'' = st := by
          rcases Hwr with ⟨h, -, h', -⟩ | ⟨-, ⟨hk1, -, hst⟩ | ⟨-, h', -⟩⟩
          · cases h'
          · exact ⟨hk1, hst⟩
          · cases h'
        rw [List.take_length, ← hsent]
        wp_auto
        wp_for_post
        iframe HΦ c buf
        iexists _, sent2,
          (bs1 ++ List.drop (sint.nat k) (List.take bs.length bs1 ++ List.drop bs1.length bs))
        rw [hsl2]
        iframe Hend Hh Hlb2 Hbuf
        ipureintro
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
    · cases h1
    · exact absurd rfl h0
  · -- EOF
    obtain ⟨hcl, hsl2, hres⟩ := Hr
    obtain ⟨rfl, rfl⟩ := wire.readRes_inj hres
    rcases Hout with ⟨h0, -⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, h1, -⟩
    · cases h0
    · cases err with
      | nil =>
        -- a nil `io.EOF` would not end the loop: it goes on
        wp_auto
        wp_for_post
        iframe HΦ c buf
        iexists st, sR, bs'
        iframe Hend Hh Hlb Hbuf
        ipureintro; exact Hbl
      | ok i =>
        wp_auto
        wp_for_post
        (try wp_auto)
        wp_apply wp_srvClose wp_Close γm t cn γ _ _ $$ [Hend] as %err' -
        · iframe HsrvInv Hname Hc Hend
        (try wp_auto)
        iapply HΦ
        itrivial
    · exact absurd rfl h1

theorem wp_Serve
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ dupInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases dupInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HsrvInv⟩
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
      wp_apply wp_serveConn wp_Read wp_Write wp_Close γm c cn eof $$ [Hproto]
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

theorem wp_writeAll
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (c : GoInterface) (cn : Nat) (γr γw : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn false srvAddr ∗
        inv cliN (cliInv G cn γr γw) ∗ half G γw (0 : Nat) }}
      (App (Val (@! writeAll)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %Hct, #Hc⟩, #Hinv, Hw⟩
  subst Hct
  wp_auto
  ihave HI : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j + 1) ∗ "Hw" ∷ half G γw j ∗ "%Hj" ∷ ⌜j ≤ 4⌝ :
      IProp GF) $$ [i Hw]
  · iexists 0
    rw [show W64 (((0 : Nat) : Int) + 1) = W64 1 from rfl]
    iframe i Hw
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · -- the body: write the byte `j + 1`
    have hj4 : j < 4 := by
      have : sint.Z (W64 (↑j + 1)) = (j : Int) + 1 := by word
      have h4 : sint.Z (W64 4) = 4 := rfl
      omega
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %b ⟨Hb, -⟩
    · ipureintro; decide
    (try wp_auto)
    ihave %Hbl := ownSlice_len $$ Hb
    have Hbl1 : sint.Z b.len = 1 := by
      obtain ⟨h1, h2⟩ := Hbl
      simp only [List.length_replicate] at h1
      word
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
      rw [Hbl1]; decide)]
    wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ _ $$ [$Hb] as Hb
    · ipureintro; decide
    (try wp_auto)
    have Hset : (List.replicate 1 (zero_val w8)).set 0 (W8 (sint.Z (W64 (↑j + 1)))) =
        [W8 (↑j + 1)] := by
      rw [show sint.Z (W64 (↑j + 1)) = ↑j + 1 by word]; rfl
    isimp only [Hset] at Hb
    wp_apply wp_Write t cn false srvAddr b [W8 (↑j + 1)] (DFrac.own 1)
        (fun k ok => iprop(half G γw (j + k) ∗ ⌜ok = true → k = 1⌝)) $$ [Hb Hw]
      as %n %err ⟨%k, %okw, ⟨Hw, %Hk⟩, Hb, %Hn⟩
    · iframe Hc Hb
      iapply cli_write_au cn γr γw j hj4 $$ Hinv Hw
    obtain ⟨-, Hnil, Herr⟩ := Hn
    cases okw
    · -- the write failed: return
      obtain ⟨pe, rfl⟩ := Herr rfl
      wp_auto
      wp_for_post
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil rfl]
    obtain rfl := Hk rfl
    wp_auto
    wp_for_post
    (try wp_auto)
    iframe HΦ c
    iexists j + 1
    rw [show W64 (↑j + 1) + W64 1 = W64 (↑(j + 1) + 1) by word]
    iframe i Hw
    ipureintro; omega
  · -- the loop ends
    (try wp_auto)
    iapply HΦ
    itrivial

/-- `cliInv_alloc`, its update under a node's invariants. -/
theorem cliInv_alloc' (cn : Nat) :
    tcpFreshEnd (G (GF := GF)) cn false ={⊤}=∗ ∃ γr γw, inv cliN (cliInv G cn γr γw) ∗
      half G γr (0 : Nat) ∗ half G γw (0 : Nat) :=
  cliInv_alloc cn

theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ dupInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases dupInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HsrvInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, srvName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm) (fun cn => iprop(∃ γ, srvName G γm cn γ))
        $$ HaddrInv
      iintro %cn #Hat Ha
      iapply dup_deposit γm cn $$ HsrvInv Hat Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    ihave #Hat := net.connAt_conn t cn false srvAddr $$ Hca
    imod cliInv_alloc' cn $$ Hd with ⟨%γr, %γw, #Hcli, Hr, Hw⟩
    ihave #Hacc := cli_read_acc cn γr γw $$ Hcli
    imod tcpOutLb_nil (G (GF := GF)) cn true srvAddr $$ Hat with #Hlb0
    wp_auto
    wp_apply wp_fork $$ [Hw]
    · wp_apply wp_writeAll wp_Write _ cn γr γw $$ [Hw]
      · iframe Hcli Hw
        unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      itrivial
    (try wp_auto)
    ihave HI : (∃ (j : Nat) (sj : GoString), "i" ∷ i_ptr ↦ W64 (j + 1) ∗ "Hr" ∷ half G γr j ∗
        "#Hlb" ∷ tcpOutLb G cn true sj ∗ "%Hj" ∷ ⌜sj.length = j ∧ j ≤ 4⌝ : IProp GF) $$ [i Hr]
    · iexists 0, []
      rw [show W64 (((0 : Nat) : Int) + 1) = W64 1 from rfl]
      iframe i Hr Hlb0
      ipureintro; exact ⟨rfl, by omega⟩
    wp_for HI
    wp_if_destruct
    · -- the body: read the byte `j + 1`
      obtain ⟨Hsj, Hj4⟩ := Hj
      have hj4 : j < 4 := by
        have : sint.Z (W64 (↑j + 1)) = (j : Int) + 1 := by word
        have h4 : sint.Z (W64 4) = 4 := rfl
        omega
      wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %b ⟨Hb, -⟩
      · ipureintro; decide
      (try wp_auto)
      wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
          srvAddr b _ (half G γr) j sj eof Hsj $$ [Hb Hr]
        as %ok ⟨%r', %bs', Hr, Hb, %Hlen, Hres⟩
      · simp only [Bool.not_false]
        iframe Hb Heof Hlb Hr Hacc
        unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      cases ok
      · -- the read failed: break
        wp_auto
        wp_for_post
        wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [] as %err' ⟨%ok', -, -⟩
        · iframe Hca
          iapply cli_close_au cn γr γw $$ Hcli
        (try wp_auto)
        iapply HΦ
        itrivial
      · simp only [↓reduceIte]
        icases Hres with ⟨%sent, #Hsent, %Hs⟩
        obtain ⟨rfl, hsl, hsd⟩ := Hs
        imod client_check' γm cn γ γr γw sent $$ HsrvInv Hname Hcli Hsent with %Hpre
        simp only [List.length_replicate] at hsl Hlen
        have hsent : sent = dseq.take (j + 1) := by
          have := List.prefix_iff_eq_take.1 Hpre
          rw [hsl] at this; exact this
        have hb : bs' = [W8 (↑j + 1)] := by
          rw [← hsd, hsent]
          match j, hj4 with
          | 0, _ => rfl
          | 1, _ => rfl
          | 2, _ => rfl
          | 3, _ => rfl
        subst hb
        wp_auto
        ihave %Hbl := ownSlice_len $$ Hb
        have Hbl1 : sint.Z b.len = 1 := by
          obtain ⟨h1, h2⟩ := Hbl
          simp only [List.length_singleton] at h1
          word
        rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
          rw [Hbl1]; decide)]
        wp_apply wp_load_slice_index b (sint.Z (W64 0)) [W8 (↑j + 1)] (DFrac.own 1) (W8 (↑j + 1))
            (by decide) $$ [$Hb] as Hb
        · ipureintro; rfl
        (try wp_auto)
        rw [show sint.Z (W64 (↑j + 1)) = ↑j + 1 by word]
        simp only [decide_true, Bool.not_true]
        wp_auto
        wp_for_post
        (try wp_auto)
        iframe HΦ c
        iexists j + 1, sent
        rw [show W64 (↑j + 1) + W64 1 = W64 (↑(j + 1) + 1) by word]
        simp only [List.length_replicate]
        iframe i Hr Hsent
        ipureintro; exact ⟨hsl, by omega⟩
    · -- the loop ends: close
      (try wp_auto)
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply cli_close_au cn γr γw $$ Hcli
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
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ dupInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! Server)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_Read wp_Write wp_Close γm eof $$ []
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
    {{ isPkgInit (PROP := IProp GF) pkg ∗ dupInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! Client)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Call wp_Dial wp_ReadFull wp_Write wp_Close γm h eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.net.duplex
end Perennial
