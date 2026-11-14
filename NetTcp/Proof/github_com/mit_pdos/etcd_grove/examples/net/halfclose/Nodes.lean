/-
The proofs of `examples/net/halfclose`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `readAll`: reads until EOF or a failure, appending, through a reader predicate `P` of the bytes
  read and an accessor per `Read` (as `wire.ReadFull`'s spec): whatever it returns, the caller has
  `P` of the bytes it returns.
* `prefixOf`: returns whether `a` is a prefix of `b`.
* `serveConn`: `readAll` (`server_read_acc`); on EOF, the write back of what it read
  (`server_write_au`: a prefix of what it read); the close (`hc_close_au`).
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's protocol).
* `Call`: the dial (`dial_both_au`, the deposit `hc_deposit`), the write of `"hello"`
  (`client_write_au`), the shutdown of the write side (`hc_closeWrite_au`), `readAll`
  (`client_read_acc`), and the check: the response is a prefix of `"hello"` (`client_check`), so
  `prefixOf` returns `true` and the panic is unreachable.
* `eof_init`: `io.EOF`'s value, from the package's initialization (what the commands' `main`s,
  `cmd/{server,client}/Main.lean`, pass to `Serve` and `Call`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Defs
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
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap sentAll rcvdAll dial_both_au
  readOutcome_got_le readOutcome_bytes_pos)

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose

/-- Two lists of slices' lengths, ordered as the lengths. -/
theorem length_lt_of_len {xs ys : List w8} {la lb : w64} (h1 : xs.length = sint.nat la)
    (h2 : ys.length = sint.nat lb) (h0 : 0 ≤ sint.Z lb) (h : ¬ sint.Z la ≤ sint.Z lb) :
    ys.length < xs.length := by
  rw [h1, h2]; simp only [sint.nat, sint.Z] at h0 h ⊢; omega

/-- An index within a slice's length is within its list. -/
theorem idx_lt_of_len {xs : List w8} {la i : w64} (h1 : xs.length = sint.nat la)
    (h0 : 0 ≤ sint.Z i) (h : sint.Z i < sint.Z la) : sint.nat i < xs.length := by
  rw [h1]; simp only [sint.nat, sint.Z] at h0 h ⊢; omega

/-- A step of `prefixOf`'s loop: different bytes at `n` (both lists that long), not a prefix; equal
ones, the lists agree up to `n + 1`. -/
theorem prefixOf_step {xs ys : List w8} {n : Nat} {x y : w8} (hx : xs[n]? = some x)
    (hy : ys[n]? = some y) (ht : xs.take n = ys.take n) :
    (x ≠ y → ¬ xs <+: ys) ∧ (x = y → xs.take (n + 1) = ys.take (n + 1)) := by
  constructor
  · intro hne hp
    have hn : n < xs.length := by
      rcases Nat.lt_or_ge n xs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hx; cases hx
    have he := List.prefix_iff_eq_take.1 hp
    have : xs[n]? = ys[n]? := by
      conv => lhs; rw [he]
      rw [List.getElem?_take, if_pos hn]
    rw [hx, hy] at this
    exact hne (Option.some.inj this)
  · intro hxy
    subst hxy
    rw [List.take_add_one, List.take_add_one, ht, hx, hy]

/-- The end of `prefixOf`'s loop: `xs` agrees with `ys` up to its length. -/
theorem prefixOf_done {xs ys : List w8} (ht : xs.take xs.length = ys.take xs.length) :
    xs <+: ys := by
  rw [List.prefix_iff_eq_take]; rw [List.take_length] at ht; exact ht

/-- `i + 1` below a signed bound does not overflow. -/
theorem sint_succ {i la : w64} (h0 : 0 ≤ sint.Z i) (h : sint.Z i < sint.Z la) :
    sint.Z (i + W64 1) = sint.Z i + 1 ∧ sint.nat (i + W64 1) = sint.nat i + 1 := by
  have hz : sint.Z (i + W64 1) = sint.Z i + 1 := by word
  refine ⟨hz, ?_⟩
  simp only [sint.nat, sint.Z] at hz h0 ⊢; omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : halfclose.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- What `c.Read(b)` returns (`net.ReadOut`), by cases: bytes; EOF; an error (or a wait, which the
update excludes), the last two with no bytes. -/
theorem readOut_cases {bs0 : List w8} {r : ReadRes} {k : w64} {err eof : GoInterface}
    {bs' : List w8} (h : net.ReadOut bs0 r k err eof bs') :
    (∃ bs, r = .bytes bs ∧ sint.nat k = min bs0.length bs.length ∧ err = interface.nil ∧
      bs' = bs.take bs0.length ++ bs0.drop bs.length) ∨
    (r.got = [] ∧ k = 0 ∧ err = eof ∧ bs' = bs0) ∨
    (r.got = [] ∧ k = 0 ∧ net.netErr err ∧ bs' = bs0) := by
  cases r with
  | bytes bs => exact .inl ⟨bs, rfl, h⟩
  | eof => exact .inr (.inl ⟨rfl, h⟩)
  | err => exact .inr (.inr ⟨rfl, h⟩)
  | wait => exact .inr (.inr ⟨rfl, h⟩)

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
    (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (x : Loc) (P : List w8 → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn s a ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x ∗
        P [] ∗
        □ (∀ (got : List w8) (m : Nat), P got -∗
          |={⊤,∅}=> ∃ st d, tcpEnd G cn s st ∗ tcpDir G cn (!s) d ∗
            ∀ r d', ⌜ReadOutcome st d m r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G cn s st -∗
              tcpDir G cn (!s) d' ={∅,⊤}=∗ P (got ++ r.got)) }}
      (App (Val (@! readAll)) (Val #c))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok); ∃ data, sl ↦* data ∗ P data }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %Hct, #Hc⟩, #Heof, HP, #Hacc⟩
  subst Hct
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hblen := ownSlice_len $$ Hbuf
  ihave %Hbwf := ownSlice_wf $$ Hbuf
  have hbl8 : sint.nat buf.len = 8 := by simpa using Hblen.1.symm
  have hl8 : sint.Z buf.len = 8 := by
    have h := hbl8; simp only [sint.nat, sint.Z] at h ⊢; omega
  have hn8 : buf.len.toNat = 8 := by word
  ihave Hd0 := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hdc0 := ownSliceCap_nil (V := w8) (GF := GF)
  ihave HI : (∃ (dsl : GoSlice) (data bsb : List w8),
      "data" ∷ data_ptr ↦ dsl ∗ "Hd" ∷ dsl ↦* data ∗ "Hdc" ∷ ownSliceCap w8 dsl (DFrac.own 1) ∗
      "Hbuf" ∷ buf ↦* bsb ∗ "HP" ∷ P data ∗ "%Hbl" ∷ ⌜bsb.length = 8⌝ : IProp GF)
      $$ [data Hbuf HP Hd0 Hdc0]
  · iexists slice.nil, [], _
    iframe data Hbuf HP Hd0 Hdc0
    ipureintro; simp
  wp_for HI
  wp_apply wp_Read t cn s a buf bsb _
      (fun r => iprop(P (data ++ r.got) ∗
        ⌜r.got.length ≤ 8 ∧ ∀ bs, r = .bytes bs → 1 ≤ bs.length⌝)) $$ [Hbuf HP]
    as %k %err ⟨%r, %bs', ⟨HP, %Hle⟩, Hbuf, %Hout⟩
  · iframe Hc Hbuf Heof
    imod Hacc $$ %data %(buf.len.toNat) HP with ⟨%st, %d, Hend, Hd, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hd
    iintro %r %d' %Hrd Hend Hd
    imod Hk $$ %r %d' %Hrd Hend Hd with HP
    imodintro
    iframe HP
    ipureintro
    have := (readOutcome_got_le Hrd.1).1
    refine ⟨by omega, fun bs hbs => ?_⟩
    subst hbs
    exact readOutcome_bytes_pos Hrd.1 (by omega)
  rcases readOut_cases Hout with ⟨bs, rfl, hk, rfl, rfl⟩ | ⟨hg, rfl, rfl, rfl⟩ |
    ⟨hg, rfl, ⟨pe, rfl⟩, rfl⟩
  · -- the next bytes: append them, and go on
    obtain ⟨Hle, Hpos⟩ := Hle
    have Hpos := Hpos bs rfl
    simp only [ReadRes.got] at Hle ⊢
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
      rw [hk8, Hbl, List.take_of_length_le Hle, List.take_left]
    iexists dsl', data ++ bs, (List.take bsb.length bs ++ List.drop bs.length bsb)
    rw [htake]
    iframe data Hd Hdc Hbuf HP
    ipureintro
    simp only [List.length_append, List.length_take, List.length_drop, Hbl]
    omega
  all_goals
    -- EOF or an error: return what was read
    rw [hg, List.append_nil] at *
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
    iexists data
    rw [List.take_zero, List.append_nil]
    iframe Hd HP

theorem wp_prefixOf (a b : GoSlice) (xs ys : List w8) (dqa dqb : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ a ↦*{dqa} xs ∗ b ↦*{dqb} ys }}
      (App (App (Val (@! prefixOf)) (Val #a)) (Val #b))
    {{ (r : Bool), RET #r; a ↦*{dqa} xs ∗ b ↦*{dqb} ys ∗ ⌜r = true ↔ xs <+: ys⌝ }} := by
  wp_start as ⟨Ha, Hb⟩
  ihave %Halen := ownSlice_len $$ Ha
  ihave %Hblen := ownSlice_len $$ Hb
  wp_auto
  wp_if_destruct
  · -- longer: not a prefix
    have hlt : ys.length < xs.length :=
      length_lt_of_len Halen.1 Hblen.1 Hblen.2 (Int.not_le.2 Hif)
    (try wp_auto)
    iapply HΦ
    iframe Ha Hb
    ipureintro
    constructor
    · intro h; cases h
    · intro h; exact absurd h.length_le (Nat.not_le.2 hlt)
  have Hab : sint.Z a.len ≤ sint.Z b.len := Int.not_lt.1 Hif
  (try wp_auto)
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧
        xs.take (sint.nat i) = ys.take (sint.nat i)⌝ : IProp GF) $$ [i]
  · iexists _
    iframe i
    ipureintro; refine ⟨by word, by word, ?_⟩
    simp [sint.nat]
  wp_for HI
  wp_if_destruct
  · -- `i < len(a)`: compare `a[i]` and `b[i]`
    have hia' : sint.Z i < sint.Z a.len := Hif
    have hia : sint.nat i < xs.length := idx_lt_of_len Halen.1 Hi.1 Hif
    have hib' : sint.Z i < sint.Z b.len := Int.lt_of_lt_of_le Hif Hab
    have hib : sint.nat i < ys.length := idx_lt_of_len Hblen.1 Hi.1 hib'
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hif⟩)]
    wp_apply wp_load_slice_index _ _ _ _ (xs[sint.nat i]) Hi.1 $$ [Ha] with Ha
    · iframe Ha; ipureintro; exact List.getElem?_eq_getElem hia
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hib'⟩)]
    wp_apply wp_load_slice_index _ _ _ _ (ys[sint.nat i]) Hi.1 $$ [Hb] with Hb
    · iframe Hb; ipureintro; exact List.getElem?_eq_getElem hib
    have Hstep := prefixOf_step (List.getElem?_eq_getElem hia) (List.getElem?_eq_getElem hib)
      Hi.2.2
    (try wp_auto)
    wp_if_destruct
    · -- equal: go on
      wp_for_post
      obtain ⟨hz, hn⟩ := sint_succ Hi.1 hia'
      iframe
      iexists i + W64 1
      iframe i
      ipureintro
      refine ⟨by omega, by omega, ?_⟩
      rw [hn]; exact Hstep.2 Hif
    · -- different: not a prefix
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iframe Ha Hb
      ipureintro
      exact ⟨fun h => absurd h (by decide), fun h => absurd h (Hstep.1 Hif)⟩
  · -- `i = len(a)`: a prefix
    have hi : sint.nat i = xs.length := by
      rw [Halen.1]; simp only [sint.nat, sint.Z] at Hi Hif ⊢; omega
    iapply HΦ
    iframe Ha Hb
    ipureintro
    refine ⟨fun _ => prefixOf_done ?_, fun _ => rfl⟩
    rw [← hi]; exact Hi.2.2

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (ns : HcNames) (R : List w8) :
    ⊢ inv hcN (hcState (Gg := hG.goose_globalGS) γm) -∗ hcName (Gg := hG.goose_globalGS) γm cn ns -∗
      rcvdAll (Gg := hG.goose_globalGS) ns.d R ={⊤}=∗ ⌜R <+: hello⌝ ∗ rcvdAll ns.d R :=
  client_check γm cn ns R

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
  wp_start as ⟨⟨#HaddrInv, #HhcInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%ns, Hend, Hr, Hw, #Hname⟩, #Heof⟩
  subst Hct
  ihave #Hacc := server_read_acc γm cn ns TcpEnd.fresh $$ [HhcInv Hname]
  · iframe HhcInv Hname
  wp_auto
  wp_apply wp_readAll wp_Read (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true
      srvAddr x (srvP ns cn TcpEnd.fresh) $$ [Hend Hr]
    as %sl %ok ⟨%data, Hd, HP⟩
  · iframe Heof
    isplitl []
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hr]
    · unfold srvP
      iframe Hend Hr
    imodintro
    simp only [Bool.not_true]
    iexact Hacc
  unfold srvP
  icases HP with ⟨Hend, Hr⟩
  cases ok
  · -- the read failed: close
    wp_auto
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply hc_close_au γm cn ns true _ $$ HhcInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- EOF: write back what was read, then close
    wp_auto
    wp_apply wp_Write t cn true srvAddr sl data (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn true TcpEnd.fresh ∗ sentAll ns.d ([] ++ data.take k) ∗
          rcvdAll ns.u data ∗ ⌜∃ d d', WriteOutcome TcpEnd.fresh d data k ok d'⌝))
        $$ [Hd Hend Hw Hr]
      as %n %err ⟨%k, %okw, ⟨Hend, -, -, -⟩, Hd, -⟩
    · iframe Hc Hd
      iapply server_write_au γm cn ns TcpEnd.fresh [] data data (by simp) $$ HhcInv Hname Hend
        Hw Hr
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hc
      iapply hc_close_au γm cn ns true _ $$ HhcInv Hname Hend
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
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => clientProto γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hcp⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply dial_both_au addrN srvAddr (connProto γm) (clientProto γm) $$ HaddrInv
      iintro %cn #Hat Hd Ha
      iapply hc_deposit γm cn $$ HhcInv Hat Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold clientProto
    icases Hcp with ⟨%ns, Hend, Hw, Hr, #Hname⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗ sentAll ns.u ([] ++ hello.take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d hello k ok d'⌝)) $$ [Hsl Hend Hw]
      as %n %err ⟨%k, %okw, ⟨Hend, -, -⟩, Hsl, %Hn⟩
    · iframe Hca Hsl
      iapply client_write_au γm cn ns TcpEnd.fresh [] hello (by simp) $$ HhcInv Hname Hend Hw
    obtain ⟨-, Hnil, Herr⟩ := Hn
    cases okw
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply hc_close_au γm cn ns false _ $$ HhcInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil rfl]
    wp_auto
    -- shut the write side
    wp_apply wp_CloseWrite t cn false srvAddr (fun _ => tcpEnd G cn false TcpEnd.fresh) $$ [Hend]
      as %err ⟨%okc, Hend, %Herr⟩
    · iframe Hca
      iapply hc_closeWrite_au γm cn ns false TcpEnd.fresh $$ HhcInv Hname Hend
    cases okc
    · -- the shutdown failed: close and return
      obtain ⟨pe, rfl⟩ := Herr.2 rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply hc_close_au γm cn ns false _ $$ HhcInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Herr.1 rfl]
    wp_auto
    -- read the response until EOF or an error
    ihave #Hacc := client_read_acc γm cn ns TcpEnd.fresh $$ [HhcInv Hname]
    · iframe HhcInv Hname
    wp_apply wp_readAll wp_Read (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr x (cliP ns cn TcpEnd.fresh) $$ [Hend Hr]
      as %rsl %ok ⟨%data, Hd, HP⟩
    · iframe Heof
      isplitl []
      · unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      isplitl [Hend Hr]
      · unfold cliP
        iframe Hend Hr
      imodintro
      simp only [Bool.not_false]
      iexact Hacc
    unfold cliP
    icases HP with ⟨Hend, Hr⟩
    -- the response is a prefix of `"hello"`
    imod client_check' γm cn ns data $$ HhcInv Hname Hr with ⟨%Hpre, Hr⟩
    cases ok
    · -- an error: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply hc_close_au γm cn ns false _ $$ HhcInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- EOF: `prefixOf` holds, no panic
      wp_auto
      wp_apply wp_string_to_bytes with %hsl ⟨Hhsl, -⟩
      (try wp_auto)
      wp_apply wp_prefixOf rsl hsl data hello (DFrac.own 1) (DFrac.own 1) $$ [Hd Hhsl]
        as %b ⟨Hd, Hhsl, %Hb⟩
      · iframe Hd Hhsl
      rw [Hb.2 Hpre]
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply hc_close_au γm cn ns false _ $$ HhcInv Hname Hend
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

end proof

end github_com.mit_pdos.etcd_grove.examples.net.halfclose
end Perennial
