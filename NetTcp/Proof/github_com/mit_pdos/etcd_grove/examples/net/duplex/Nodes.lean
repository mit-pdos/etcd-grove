/-
The proofs of `examples/net/duplex`'s functions, over the specs of `net` and `wire` (hypotheses,
linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: a loop of `Read`s into a 16-byte buffer (`wire.read_au` on the up-direction: what
  the server read, the dialer wrote), each read's bytes written back (`server_write_au`: the
  server's bytes stay those it read), until a failure or EOF; then the close (`wire.close_au` on
  the down-direction). The server thread owns its end.
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`).
* `writeAll`: the writer goroutine, the bytes 1..4 one at a time (`cli_write_au`).
* `Call`: the dial (`dial_au2`, the deposit `dup_deposit`), the client's end put in its invariant
  (`cliInv_alloc`), `writeAll` forked, then four `wire.ReadFull`s of one byte through the reader's
  accessor (`cli_read_acc`), each checked (`client_check`: the byte at position `i - 1` is `i`),
  and the close (`cli_close_au`).
* `Server`, `Client`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Defs
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
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap dirInv sentAll sentLb
  rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.duplex

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : duplex.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `buf` rejoined from its two parts at `k`. -/
theorem buf_rejoin (buf : GoSlice) (k : w64) (xs ys : List w8) (hx : xs.length = sint.nat k)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len) :
    slice.slice buf w8 (W64 0) k ↦* xs -∗ slice.slice buf w8 k buf.len ↦* ys -∗
      (buf ↦* (xs ++ ys) : IProp GF) := by
  iintro H1 H2
  iapply (ownSlice_trivial_slice buf (DFrac.own 1) (xs ++ ys)).2
  iapply ownSlice_combine k buf (DFrac.own 1) xs ys (W64 0) buf.len
    ⟨by rw [hx]; word, by decide, hk.1, hk.2⟩ $$ H1 H2

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (γ : DupNames) (γw : GName) (resp : List w8) :
    ⊢ inv srvN (srvState (Gg := hG.goose_globalGS) γm) -∗ srvName γm cn γ -∗
      inv cliN (cliInv cn γ γw) -∗ sentLb (Gg := hG.goose_globalGS) γ.down resp ={⊤}=∗
      ⌜resp <+: dseq⌝ :=
  client_check γm cn γ γw resp

/-- `cliInv_alloc`, its update under a node's invariants. -/
theorem cliInv_alloc' (cn : Nat) (γ : DupNames) :
    tcpEnd (G (GF := GF)) cn false TcpEnd.fresh -∗ sentAll (Gg := hG.goose_globalGS) γ.up [] ={⊤}=∗
      ∃ γw, inv cliN (cliInv cn γ γw) ∗ half G γw (0 : Nat) :=
  cliInv_alloc cn γ

/-- `wire.close_au`, its update under a node's invariants. -/
theorem close_au' (N : Namespace) (c : Nat) (s : Bool) (γ : wire.DirNames) (st : TcpEnd) :
    ⊢ inv N (dirInv (Gg := hG.goose_globalGS) c s γ) -∗ tcpEnd (G (GF := GF)) c s st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c s d ∗
        ∀ ok st' d', ⌜CloseOutcome st0 d ok st' d'⌝ -∗ tcpEnd G c s st' -∗ tcpDir G c s d'
          ={∅,⊤}=∗ tcpEnd G c s st' ∗ ⌜∃ d d', CloseOutcome st d ok st' d'⌝ :=
  wire.close_au N c s γ st

/-- `wire.read_au` for the acceptor's end (the direction towards it, the dialer's), its update
under a node's invariants. -/
theorem read_au' (N : Namespace) (c : Nat) (γ : wire.DirNames) (st : TcpEnd) (R : List w8)
    (n : Nat) :
    ⊢ inv N (dirInv (Gg := hG.goose_globalGS) c false γ) -∗ tcpEnd (G (GF := GF)) c true st -∗
      rcvdAll (Gg := hG.goose_globalGS) γ R -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c true st0 ∗ tcpDir G c false d ∗
        ∀ r d', ⌜ReadOutcome st0 d n r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G c true st0 -∗
          tcpDir G c false d' ={∅,⊤}=∗ tcpEnd G c true st ∗
            rcvdAll (Gg := hG.goose_globalGS) γ (R ++ r.got) ∗
            sentLb (Gg := hG.goose_globalGS) γ (R ++ r.got) ∗
            ⌜∃ d d', ReadOutcome st d n r d' ∧ r ≠ .wait⌝ :=
  wire.read_au N c true γ st R n

/-- A server-side close, its end's state dropped. -/
theorem wp_srvClose (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (t : Loc) (cn : Nat) (γ : DupNames) (st : TcpEnd) :
    {{ inv srvN (dirInv (Gg := hG.goose_globalGS) cn true γ.down) ∗
        net.connAt t cn true srvAddr ∗ tcpEnd G cn true st }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hdir, #Hc, Hend⟩ HΦ
  wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok, -, -⟩
  · iframe Hc
    imod close_au' srvN cn true γ.down st $$ Hdir Hend with ⟨%st0, %d, Hend, Hd, Hk⟩
    imodintro
    iexists st0, d
    iframe Hend Hd
    iintro %ok %st' %d' %Hcl Hend Hd
    imod Hk $$ %ok %st' %d' %Hcl Hend Hd with -
    imodintro
    itrivial
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
  wp_start as ⟨⟨#HaddrInv, #HsrvInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, #Hname, Hend, Hh, Hr, #Hlb0⟩, #Heof⟩
  subst Hct
  ihave #HdU := dup_dirInv_up γm cn γ $$ HsrvInv Hname
  ihave #HdD := dup_dirInv_down γm cn γ $$ HsrvInv Hname
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
  have Hbn16 : buf.len.toNat = 16 := by word
  ihave HI : (∃ (R : List w8) (bs : List w8),
      "Hend" ∷ tcpEnd G cn true TcpEnd.fresh ∗ "Hh" ∷ half G γ.m R ∗
      "Hr" ∷ rcvdAll (Gg := hG.goose_globalGS) γ.up R ∗
      "#Hlb" ∷ sentLb (Gg := hG.goose_globalGS) γ.up R ∗ "Hbuf" ∷ buf ↦* bs ∗
      "%Hbl" ∷ ⌜bs.length = 16⌝ : IProp GF)
      $$ [Hend Hh Hr Hbuf]
  · iexists [], _
    iframe Hend Hh Hr Hlb0 Hbuf
    ipureintro; simp
  wp_for HI
  wp_apply wp_Read t cn true srvAddr buf bs eof
      (fun r => iprop(tcpEnd G cn true TcpEnd.fresh ∗
        rcvdAll (Gg := hG.goose_globalGS) γ.up (R ++ r.got) ∗
        sentLb (Gg := hG.goose_globalGS) γ.up (R ++ r.got) ∗
        ⌜∃ d d', ReadOutcome TcpEnd.fresh d buf.len.toNat r d' ∧ r ≠ .wait⌝)) $$ [Hbuf Hend Hr]
    as %k %err ⟨%r, %bs', ⟨Hend, Hr, #Hlb2, %Hro⟩, Hbuf, %Hout⟩
  · iframe Hc Hbuf Heof
    simp only [Bool.not_true]
    iapply read_au' srvN cn γ.up TcpEnd.fresh R buf.len.toNat $$ HdU Hend Hr
  obtain ⟨d, d', Hro, Hnw⟩ := Hro
  have Hgl := readOutcome_got_le Hro
  rw [Hbn16] at Hgl
  cases r with
  | bytes bs1 =>
    simp only [ReadRes.got] at Hgl
    obtain ⟨hk', rfl, rfl⟩ := Hout
    rw [Hbl, Nat.min_eq_right Hgl] at hk'
    isimp only [ReadRes.got] at Hr Hlb2
    by_cases hb0 : bs1 = []
    · -- nothing read: go on
      subst hb0
      have hk0 : ¬ (sint.Z (W64 0) < sint.Z k) := by
        have : sint.Z k ≤ 0 := by simp at hk'; word
        simpa using this
      rw [decide_eq_false hk0]
      wp_auto
      wp_for_post
      iframe HΦ c buf
      iexists R ++ [], _
      rw [List.append_nil]
      iframe Hend Hh Hr Hlb2 Hbuf
      ipureintro; simp [Hbl]
    · -- bytes: write them back
      have hbl1 : 0 < bs1.length := List.length_pos_iff.2 hb0
      have hk0 : sint.Z (W64 0) < sint.Z k := by
        have : (0 : Int) < sint.Z k := by
          have := hk'; word
        simpa using this
      rw [decide_eq_true hk0]
      wp_auto
      have hkl : sint.Z k ≤ sint.Z buf.len := by
        have : (sint.nat k : Int) ≤ 16 := by omega
        rw [Hbl16]; word
      rw [ite_eq_left ⟨by decide, by word, Int.le_trans hkl Hwf.2⟩]
      icases (ownSlice_split_all k buf _ _ ⟨by word, hkl⟩).1 $$ Hbuf with ⟨Hb1, Hb2⟩
      have htk : (List.take bs.length bs1 ++ List.drop bs1.length bs).take (sint.nat k) =
          bs1 := by
        rw [hk', Hbl, List.take_of_length_le Hgl, List.take_left' rfl]
      isimp only [htk] at Hb1
      (try wp_auto)
      wp_apply wp_Write t cn true srvAddr (slice.slice buf w8 (W64 0) k) bs1 (DFrac.own 1)
          (fun kw ok => iprop(tcpEnd G cn true TcpEnd.fresh ∗ half G γ.m (R ++ bs1.take kw) ∗
            ⌜∃ d d', WriteOutcome TcpEnd.fresh d bs1 kw ok d'⌝)) $$ [Hb1 Hend Hh]
        as %n %werr ⟨%kw, %okw, ⟨Hend, Hh, %Hwr⟩, Hb1, %Hn⟩
      · iframe Hc Hb1
        iapply server_write_au γm cn γ R bs1 TcpEnd.fresh $$ HsrvInv Hname Hh Hlb2 Hend
      obtain ⟨-, Hnil, Herr⟩ := Hn
      ihave Hbuf := buf_rejoin buf k _ _ (by rw [hk']) ⟨by word, hkl⟩ $$ Hb1 Hb2
      cases okw
      · -- the write failed: break, close
        obtain ⟨pe, rfl⟩ := Herr rfl
        wp_auto
        wp_for_post
        (try wp_auto)
        wp_apply wp_srvClose wp_Close t cn γ _ $$ [Hend] as %err' -
        · iframe HdD Hc Hend
        (try wp_auto)
        iapply HΦ
        itrivial
      · rw [Hnil rfl]
        obtain ⟨d0, d0', Hwr⟩ := Hwr
        rw [wire.writeOutcome_ok Hwr, List.take_length]
        wp_auto
        wp_for_post
        iframe HΦ c buf
        iexists R ++ bs1,
          (bs1 ++ List.drop (sint.nat k) (List.take bs.length bs1 ++ List.drop bs1.length bs))
        iframe Hend Hh Hr Hlb2 Hbuf
        ipureintro
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
  | eof =>
    obtain ⟨rfl, rfl, rfl⟩ := Hout
    isimp only [ReadRes.got] at Hr Hlb2
    cases err with
    | nil =>
      -- a nil `io.EOF` would not end the loop: it goes on
      wp_auto
      wp_for_post
      iframe HΦ c buf
      iexists R ++ [], _
      rw [List.append_nil]
      iframe Hend Hh Hr Hlb2 Hbuf
      ipureintro; exact Hbl
    | ok i =>
      wp_auto
      wp_for_post
      (try wp_auto)
      wp_apply wp_srvClose wp_Close t cn γ _ $$ [Hend] as %err' -
      · iframe HdD Hc Hend
      (try wp_auto)
      iapply HΦ
      itrivial
  | err =>
    obtain ⟨rfl, ⟨pe, rfl⟩, rfl⟩ := Hout
    wp_auto
    wp_for_post
    (try wp_auto)
    wp_apply wp_srvClose wp_Close t cn γ _ $$ [Hend] as %err' -
    · iframe HdD Hc Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  | wait => exact absurd rfl Hnw

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
    (c : GoInterface) (cn : Nat) (γ : DupNames) (γw : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn false srvAddr ∗
        inv cliN (cliInv (Gg := hG.goose_globalGS) cn γ γw) ∗
        inv srvN (dirInv (Gg := hG.goose_globalGS) cn false γ.up) ∗ half G γw (0 : Nat) }}
      (App (Val (@! writeAll)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %Hct, #Hc⟩, #Hinv, #Hdir, Hw⟩
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
      iapply cli_write_au cn γ γw j hj4 $$ Hinv Hdir Hw
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
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => dialerOwn γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hown⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply dial_au2 addrN srvAddr (connProto γm) (dialerOwn γm) $$ HaddrInv
      iintro %cn #Hat Hd Ha
      iapply dup_deposit γm cn $$ HsrvInv Hat Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold dialerOwn
    icases Hown with ⟨%γ, #Hname, Hend, Hwu, Hrd, #Hlbd⟩
    imod cliInv_alloc' cn γ $$ Hend Hwu with ⟨%γw, #Hcli, Hw⟩
    ihave #HdU := dup_dirInv_up γm cn γ $$ HsrvInv Hname
    ihave #HdD := dup_dirInv_down γm cn γ $$ HsrvInv Hname
    wp_auto
    wp_apply wp_fork $$ [Hw]
    · wp_apply wp_writeAll wp_Write _ cn γ γw $$ [Hw]
      · iframe Hcli HdU Hw
        unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      itrivial
    (try wp_auto)
    ihave HI : (∃ (j : Nat) (R : List w8), "i" ∷ i_ptr ↦ W64 (j + 1) ∗
        "Hr" ∷ rcvdAll (Gg := hG.goose_globalGS) γ.down R ∗
        "#Hlb" ∷ sentLb (Gg := hG.goose_globalGS) γ.down R ∗
        "%Hj" ∷ ⌜R.length = j ∧ j ≤ 4⌝ : IProp GF) $$ [i Hrd]
    · iexists 0, []
      rw [show W64 (((0 : Nat) : Int) + 1) = W64 1 from rfl]
      iframe i Hrd Hlbd
      ipureintro; exact ⟨rfl, by omega⟩
    wp_for HI
    wp_if_destruct
    · -- the body: read the byte `j + 1`
      obtain ⟨HRj, Hj4⟩ := Hj
      have hj4 : j < 4 := by
        have : sint.Z (W64 (↑j + 1)) = (j : Int) + 1 := by word
        have h4 : sint.Z (W64 4) = 4 := rfl
        omega
      wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %b ⟨Hb, -⟩
      · ipureintro; decide
      (try wp_auto)
      ihave #Hacc := cli_read_acc cn γ γw R $$ Hcli HdD
      wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
          srvAddr b _ (cliP γ R) eof $$ [Hb Hr]
        as %ok ⟨%got, %bs', HP, Hb, %Hres⟩
      · simp only [Bool.not_false]
        iframe Hb Heof Hacc
        isplitl []
        · unfold net.isConn
          iexists t
          iframe Hca
          ipureintro; rfl
        unfold cliP
        rw [List.append_nil]
        iframe Hr Hlb
      obtain ⟨Hlen, -, Hok⟩ := Hres
      cases ok
      · -- the read failed: break
        wp_auto
        wp_for_post
        wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [] as %err' ⟨%ok', -, -⟩
        · iframe Hca
          iapply cli_close_au cn γ γw $$ Hcli HdU
        (try wp_auto)
        iapply HΦ
        itrivial
      · obtain rfl := Hok rfl
        unfold cliP
        icases HP with ⟨Hr, #Hsent⟩
        imod client_check' γm cn γ γw (R ++ got) $$ HsrvInv Hname Hcli Hsent with %Hpre
        simp only [List.length_replicate] at Hlen
        have hb : got = [W8 (↑j + 1)] := dseq_last R got j hj4 HRj Hlen Hpre
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
        iexists j + 1, R ++ [W8 (↑j + 1)]
        rw [show W64 (↑j + 1) + W64 1 = W64 (↑(j + 1) + 1) by word]
        iframe i Hr Hsent
        ipureintro; exact ⟨by simp [HRj], by omega⟩
    · -- the loop ends: close
      (try wp_auto)
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply cli_close_au cn γ γw $$ Hcli HdU
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
