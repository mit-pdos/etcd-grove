/-
The proofs of `examples/net/halfclose`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `readAll`: reads until EOF or a failure, appending; the bytes read are what the other end has
  written from the start (`tcpOutLb`); on EOF, the other end's FIN after exactly them (`tcpFin`),
  the end's state unchanged; on a failure, the end's state after it (`TcpEnd.onFail`).
* `serveConn`: `readAll`; on EOF, the write back of what it read (`server_write_au`); the close
  (`server_close_au`), whose FIN keeps `finEcho`: the end is broken unless the read met EOF and the
  write wrote it all.
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's protocol).
* `Call`: the dial (`wire.dial_au`, the deposit `hc_deposit`), the write of `"hello"`, the
  shutdown of the write side, `readAll`, and the check: on EOF, the response is `"hello"`
  (`client_check`).
* `Server`, `Client`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Defs
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.Forever
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.TCPConn__CloseWrite
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

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : halfclose.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem readRes_inj {bs bs' : List w8} {c c' : w64} (h : readRes bs c = readRes bs' c') :
    bs = bs' ∧ c = c' := by
  unfold readRes at h
  obtain ⟨h1, h2⟩ := val.PairV.inj h
  exact ⟨go.intoVal_inj h1, go.intoVal_inj h2⟩

/-- `append(data, buf[:k]...)`: the first `k` bytes of `buf` appended to `data`, `buf` kept. -/
theorem wp_append_prefix (dsl buf : GoSlice) (data bs : List w8) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len) :
    {{ dsl ↦* data ∗ ownSliceCap w8 dsl (DFrac.own 1) ∗ (buf ↦* bs : IProp GF) }}
      (App (App (Val #(functions go.append [go.byte.SliceType])) (Val #dsl))
        (Val #(slice.slice buf w8 (W64 0) k)))
    {{ (s' : GoSlice), RET #s';
        s' ↦* (data ++ bs.take (sint.nat k)) ∗ ownSliceCap w8 s' (DFrac.own 1) ∗ buf ↦* bs }} := by
  wp_start_folded as ⟨Hd, Hdc, Hbuf⟩
  icases (ownSlice_split_all k buf _ bs hk).1 $$ Hbuf with ⟨Hb1, Hb2⟩
  wp_apply wp_slice_append dsl data (slice.slice buf w8 (W64 0) k) _ (DFrac.own 1) $$ [Hd Hdc Hb1]
    as %s' ⟨Hd, Hdc, Hb1⟩
  · iframe Hd Hdc Hb1
  iapply HΦ
  iframe Hd Hdc
  iapply (ownSlice_split_all k buf _ bs hk).2
  iframe Hb1 Hb2

theorem wp_readAll
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (st : TcpEnd) (x : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn s a ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x ∗
        tcpEnd G cn s st 0 }}
      (App (Val (@! readAll)) (Val #c))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
        ∃ (data : List w8) (st' : TcpEnd), sl ↦* data ∗ tcpEnd G cn s st' data.length ∗
          tcpOutLb G cn (!s) data ∗
          if ok then ⌜st' = st⌝ ∗ ∃ sent, tcpFin G cn (!s) sent ∗ ⌜sent.length = data.length⌝
          else ⌜st' = st.onFail⌝ }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %Hct, #Hc⟩, #Heof, Hend⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn s a $$ Hc
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hblen := ownSlice_len $$ Hbuf
  ihave %Hbwf := ownSlice_wf $$ Hbuf
  have hbl8 : sint.nat buf.len = 8 := by simpa using Hblen.1.symm
  have hl8 : sint.Z buf.len = 8 := by
    have h := hbl8; simp only [sint.nat, sint.Z] at h ⊢; omega
  imod tcpOutLb_nil (G (GF := GF)) cn (!s) a $$ Hat with #Hlb0
  ihave Hd0 := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hdc0 := ownSliceCap_nil (V := w8) (GF := GF)
  ihave HI : (∃ (dsl : GoSlice) (data bsb : List w8),
      "data" ∷ data_ptr ↦ dsl ∗ "Hd" ∷ dsl ↦* data ∗ "Hdc" ∷ ownSliceCap w8 dsl (DFrac.own 1) ∗
      "Hbuf" ∷ buf ↦* bsb ∗ "Hend" ∷ tcpEnd G cn s st data.length ∗
      "#Hlb" ∷ tcpOutLb G cn (!s) data ∗ "%Hbl" ∷ ⌜bsb.length = 8⌝ : IProp GF)
      $$ [data Hbuf Hend Hd0 Hdc0]
  · iexists slice.nil, [], _
    iframe data Hbuf Hend Hd0 Hdc0 Hlb0
    ipureintro; simp
  wp_for HI
  wp_apply wp_Read t cn s a buf bsb _
      (fun res => ReadPost G cn s buf.len st data.length res) $$ [Hbuf Hend]
    as %k %err ⟨%bs, %code, %bs', HQ, Hbuf, %Hout⟩
  · iframe Hc Hbuf Heof
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcl
    iexists st, data.length
    iframe Hend
    iintro %res Hpost
    imod Hcl
    imodintro
    iexact Hpost
  iunfold ReadPost at HQ
  icases HQ with (⟨%Hr, Hend⟩ | ⟨%Hr, Hend⟩ | ⟨%bs2, %sent2, %Hr, #Hlb2, Hend⟩ |
    ⟨%sent2, %Hr, #Hfin, Hend⟩)
  · -- a failure: return what was read, and `false`
    obtain ⟨rfl, rfl⟩ := readRes_inj Hr
    rcases Hout with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, -, rfl, ⟨pe, rfl⟩, rfl⟩
    · cases h0
    · cases h1
    have hc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (0 : w64) ∧
        sint.Z (0 : w64) ≤ sint.Z buf.cap := by refine ⟨?_, ?_, ?_⟩ <;> word
    have hk0 : 0 ≤ sint.Z (0 : w64) ∧ sint.Z (0 : w64) ≤ sint.Z buf.len := by
      refine ⟨?_, ?_⟩ <;> word
    rw [if_pos hc]
    wp_apply wp_append_prefix dsl buf data _ (0 : w64) hk0 $$ [Hd Hdc Hbuf]
      as %dsl' ⟨Hd, Hdc, Hbuf⟩
    · iframe Hd Hdc Hbuf
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iexists data, st.onFail
    rw [List.take_zero, List.append_nil]
    iframe Hd Hend Hlb
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  · -- an empty buffer: not with `len(buf) = 8`
    obtain ⟨-, hz, -⟩ := Hr
    exfalso
    rw [hz] at hl8
    simp [sint.Z] at hl8
  · -- the next bytes: append them, and go on
    obtain ⟨-, hb1, hbn, hsl2, hsd2, hres⟩ := Hr
    obtain ⟨rfl, rfl⟩ := readRes_inj hres
    rcases Hout with ⟨-, hk, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h0, -⟩
    · have hb8 : bs.length ≤ 8 := by
        have : buf.len.toNat = 8 := by word
        omega
      have hk8 : sint.nat k = bs.length := by rw [hk, Hbl]; omega
      have hkz : sint.Z k = bs.length := by
        simp only [sint.nat, sint.Z] at hk8 ⊢; omega
      have hc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.cap := by
        refine ⟨?_, ?_, ?_⟩ <;> word
      have hkb : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len := by refine ⟨?_, ?_⟩ <;> word
      rw [if_pos hc]
      wp_apply wp_append_prefix dsl buf data _ k hkb $$ [Hd Hdc Hbuf]
        as %dsl' ⟨Hd, Hdc, Hbuf⟩
      · iframe Hd Hdc Hbuf
      (try wp_auto)
      wp_for_post
      iframe
      have htake : (List.take bsb.length bs ++ List.drop bs.length bsb).take (sint.nat k) = bs := by
        rw [hk8, Hbl, List.take_of_length_le hb8, List.take_left]
      icases tcpOutLb_valid _ cn (!s) data sent2 $$ Hlb Hlb2 with %Hpre
      have hp : data <+: sent2 := by
        rcases Hpre with h | h
        · exact h
        · have := h.length_le; omega
      obtain ⟨tl, rfl⟩ := hp
      have htl : tl = bs := by rw [← hsd2, List.drop_left]
      subst htl
      iexists dsl', data ++ tl, (List.take bsb.length tl ++ List.drop tl.length bsb)
      rw [htake, List.length_append]
      iframe data Hd Hdc Hbuf Hend Hlb2
      ipureintro
      simp only [List.length_append, List.length_take, List.length_drop, Hbl]
      omega
    · cases h1
    · exact absurd rfl h0
  · -- EOF: return what was read, and `true`
    obtain ⟨-, hsl2, hres⟩ := Hr
    obtain ⟨rfl, rfl⟩ := readRes_inj hres
    rcases Hout with ⟨h0, -⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, h1, -⟩
    · cases h0
    · have hc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (0 : w64) ∧
          sint.Z (0 : w64) ≤ sint.Z buf.cap := by refine ⟨?_, ?_, ?_⟩ <;> word
      have hk0 : 0 ≤ sint.Z (0 : w64) ∧ sint.Z (0 : w64) ≤ sint.Z buf.len := by
        refine ⟨?_, ?_⟩ <;> word
      rw [if_pos hc]
      wp_apply wp_append_prefix dsl buf data _ (0 : w64) hk0 $$ [Hd Hdc Hbuf]
        as %dsl' ⟨Hd, Hdc, Hbuf⟩
      · iframe Hd Hdc Hbuf
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iexists data, st
      rw [List.take_zero, List.append_nil]
      iframe Hd Hend Hlb
      simp only [↓reduceIte]
      isplitr
      · ipureintro; trivial
      iexists sent2
      iframe Hfin
      ipureintro; exact hsl2
    · exact absurd rfl h1

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp sent : GoString) (hlen : sent.length = resp.length) :
    ⊢ inv hcN (hcState (G (GF := GF)) γm) -∗ hcName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp -∗ tcpFin G cn true sent ={⊤}=∗
      ⌜resp = out⌝ ∗ tcpOut G cn false out f :=
  client_check γm cn γ out f resp sent hlen

theorem wp_serveConn
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (x : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ hcInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn hcInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HhcInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Hmy, #Hname⟩, #Heof⟩
  subst Hct
  wp_auto
  wp_apply wp_readAll wp_Read (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true
      srvAddr TcpEnd.fresh x $$ [Hend]
    as %sl %ok ⟨%data, %st', Hd, Hend, #Hlb, Hres⟩
  · iframe Heof Hend
    unfold net.isConn
    iexists t
    iframe Hc
    ipureintro; rfl
  cases ok
  · -- the read failed: the end is broken; close
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with %Hst
    subst Hst
    wp_auto
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend Hmy] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ [] false TcpEnd.fresh.onFail data.length $$ HhcInv Hname Hmy
        [] Hend
      ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- EOF: write back what was read, then close
    simp only [↓reduceIte]
    icases Hres with ⟨%Hst, %sent, #Hfin, %Hsl⟩
    subst Hst
    try simp only [Bool.not_true]
    ihave #Hfe : finEcho G cn data $$ []
    · unfold finEcho
      iexists sent
      iframe Hfin Hlb
      ipureintro; exact Hsl.symm
    wp_auto
    wp_apply wp_Write t cn true srvAddr sl data (DFrac.own 1)
        (fun k ok => iprop(∃ st'', ⌜WriteRes TcpEnd.fresh data k ok st''⌝ ∗
          tcpEnd G cn true st'' data.length ∗ hcMirror G γ ([] ++ data.take k) false))
        $$ [Hd Hend Hmy]
      as %n %err ⟨%k, %okw, ⟨%st'', %Hwr, Hend, Hmy⟩, Hd, -⟩
    · iframe Hc Hd
      iapply server_write_au γm cn γ data [] TcpEnd.fresh data.length $$ HhcInv Hname Hmy Hend
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend Hmy] as %err' ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ ([] ++ data.take k) false st'' data.length $$ HhcInv Hname
        Hmy [] Hend
      rcases Hwr with ⟨h, -⟩ | ⟨-, ⟨hk, -, rfl⟩ | ⟨-, -, rfl⟩⟩
      · cases h
      · iright
        rw [hk, List.take_length, List.nil_append]
        iexact Hfe
      · ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    itrivial

theorem wp_Serve
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (x : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ hcInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases hcInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HhcInv⟩
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
      wp_apply wp_serveConn wp_Read wp_Write wp_Close γm c cn x $$ [Hproto]
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

theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_CloseWrite : net.TCPConn.CloseWrite.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) (x : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ hcInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases hcInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HhcInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, hcName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm) (fun cn => iprop(∃ γ, hcName G γm cn γ))
        $$ HaddrInv
      iintro %cn #Hat Ha
      iapply hc_deposit γm cn $$ HhcInv Hat Ha
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
        (fun k ok => iprop(∃ st', ⌜WriteRes TcpEnd.fresh (go!"hello") k ok st'⌝ ∗
          tcpEnd G cn false st' 0 ∗ tcpOut G cn false ([] ++ (go!"hello").take k) false))
        $$ [Hsl Hend Hout]
      as %n %err ⟨%k, %okw, ⟨%st', %Hwr, Hend, Hout⟩, Hsl, %Hn⟩
    · iframe Hca Hsl
      iapply wire.owned_write_au cn false _ 0 [] false _ $$ Hend Hout
    obtain ⟨-, Hnil, Herr⟩ := Hn
    cases okw
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil rfl]
    obtain ⟨rfl, rfl⟩ : k = 5 ∧ st' = TcpEnd.fresh := by
      rcases Hwr with ⟨-, -, h, -⟩ | ⟨-, ⟨hk, -, hst⟩ | ⟨-, h, -⟩⟩
      · cases h
      · exact ⟨hk, hst⟩
      · cases h
    have hout : ([] : GoString) ++ (go!"hello").take 5 = go!"hello" := rfl
    rw [hout]
    wp_auto
    -- shut the write side
    wp_apply wp_CloseWrite t cn false srvAddr
        (fun ok => iprop(∃ st2 f2,
          ⌜CloseRes true (fun st => { st with wshut := true }) TcpEnd.fresh false ok st2 f2⌝ ∗
          tcpEnd G cn false st2 0 ∗ tcpOut G cn false (go!"hello") f2)) $$ [Hend Hout]
      as %err ⟨%okc, ⟨%st2, %f2, -, Hend, Hout⟩, %Herr⟩
    · iframe Hca
      iapply owned_closeWrite_au cn false TcpEnd.fresh 0 _ false $$ Hend Hout
    cases okc
    · -- the shutdown failed: close and return
      obtain ⟨pe, rfl⟩ := Herr.2 rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ _ $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Herr.1 rfl]
    wp_auto
    -- read the response until EOF
    wp_apply wp_readAll wp_Read (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr st2 x $$ [Hend]
      as %rsl %ok ⟨%data, %st3, Hd, Hend, #Hlb, Hres⟩
    · iframe Heof Hend
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    cases ok
    · -- an error: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ _ $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- EOF: the response is `"hello"`
      simp only [↓reduceIte]
      icases Hres with ⟨-, %sent, #Hfin, %Hsl⟩
      imod client_check' γm cn γ _ f2 data sent Hsl $$ HhcInv Hname Hout Hlb Hfin with ⟨%Hdata, Hout⟩
      subst Hdata
      wp_auto
      wp_apply wp_bytes_to_string rsl (go!"hello") (DFrac.own 1) $$ Hd as Hd
      (try wp_auto)
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ _ $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
  · obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial

/-- `io.EOF`'s value, from the package's initialization: an `*errorString`. -/
theorem eof_init :
    isPkgInit (PROP := IProp GF) pkg ⊢ ∃ x : Loc,
      globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  iexists eofl
  iexact Heof

theorem wp_Server
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ hcInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! Server)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%x, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_Read wp_Write wp_Close γm x $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

theorem wp_Client
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_CloseWrite : net.TCPConn.CloseWrite.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ hcInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! Client)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%x, #Heof⟩
  (try wp_auto)
  wp_apply wp_Call wp_Dial wp_Read wp_Write wp_CloseWrite wp_Close γm h x $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.net.halfclose
end Perennial
