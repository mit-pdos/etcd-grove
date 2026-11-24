/-
The proofs of `examples/net/halfclose`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `readAll`: reads until EOF or a failure, appending, through a reader predicate `P` of the bytes
  read and an accessor per `Read` (as `wire.ReadFull`'s spec): whatever it returns, the caller has
  `P` of the bytes it returns.
* `prefixOf`: returns whether `a` is a prefix of `b`.
* `serveConn`: `readAll` (`server_read_acc`); on EOF, the write back of what it read, a loop of
  steps (`server_write_acc`: each step's bytes extend a prefix of what it read); the close
  (`hc_close_au`).
* `Serve`: `Listen` (of the plan's own address at the node's host, `listenAt_self`), then the
  accept loop (`wire.accept_lis_au`: each accepted connection's protocol, an abandoned dial's too).
* `Call`: the dial (`dial_both_au`, the deposits `hc_deposit` and, for an abandoned connection,
  `hc_deposit_ab`), the write of `"hello"`, a loop of steps (`client_write_acc`: each step's bytes
  extend a prefix of `"hello"`; a failing step's error ends the call), the shutdown of the write side (`hc_closeWrite_au`), `readAll`
  (`client_read_acc`), and the check: the response is a prefix of `"hello"` (`client_check`), so
  `prefixOf` returns `true` and the panic is unreachable.
* `eof_init`: `io.EOF`'s value, from the package's initialization (what the commands' `main`s,
  `cmd/{server,client}/Main.lean`, pass to `Serve` and `Call`); `poll.ErrDeadlineExceeded`'s, which
  the `Read` and `Write` specs name, from `internal/poll`'s package fact (`wire.ed_of_poll`; the
  package imports `net`, not `wire`).

A failure's error is an `*OpError` (`net.resErr`, of any kind, D14), never `nil` and never `io.EOF`
(`net.resErr_netErr`): the code's `err != nil` and `err == io.EOF` tests need nothing more.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.TCPConn__CloseWrite
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
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv sentAll rcvdAll dial_both_au)

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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : halfclose.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

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
    (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (x : Loc) (ed : GoInterface)
    (P : List w8 → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn s a ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] ∗
        □ (∀ (got : List w8) (m : Nat), P got -∗
          |={⊤,∅}=> ∃ st d, netEnd G cn s st ∗ netDir G cn (!s) d ∗
            ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗ netEnd G cn s st -∗
              netDir G cn (!s) d' ={∅,⊤}=∗ P (got ++ r.got)) }}
      (App (Val (@! readAll)) (Val #c))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok); ∃ data, sl ↦* data ∗ P data }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, #Heof, #Hed, HP, #Hacc⟩
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
  wp_apply wp_Read t cn s a la ra buf bsb _ ed
      (fun r => iprop(P (data ++ r.got) ∗
        ⌜r.got.length ≤ 8 ∧ ∀ bs, r = .bytes bs → 1 ≤ bs.length⌝)) $$ [Hbuf HP]
    as %k %err ⟨%r, %bs', ⟨HP, %Hle⟩, Hbuf, %Hout, HE⟩
  · iframe Hc Hbuf Heof Hed
    imod Hacc $$ %data %(buf.len.toNat) HP with ⟨%st, %d, Hend, Hd, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hd
    iintro %r %d' %Hrd Hend Hd
    imod Hk $$ %r %d' %Hrd Hend Hd with HP
    imodintro
    iframe HP
    ipureintro
    have := (readOutcome_got_le Hrd).1
    refine ⟨by omega, fun bs hbs => ?_⟩
    subst hbs
    exact readOutcome_bytes_pos Hrd (by omega)
  cases r
  case' eof =>
    -- EOF: `err` is `io.EOF`
    simp only [net.ReadErr]
    icases HE with %Herr
    subst Herr
  case' err e =>
    -- a failure: `err` is an `*OpError`, not `io.EOF`
    simp only [net.ReadErr]
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
  case' bytes bs =>
    -- the next bytes: append them, and go on
    obtain ⟨hk, rfl⟩ := Hout
    simp only [net.ReadErr]
    icases HE with %Herr
    subst Herr
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
    obtain ⟨rfl, rfl⟩ := Hout
    rw [show ReadRes.got _ = [] from rfl, List.append_nil]
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
  wp_start as ⟨⟨#HaddrInv, #HhcInv⟩, ⟨%t, %la, %ra, %Hct, #Hc⟩, ⟨%ns, Hend, Hr, Hw, #Hname⟩,
    #Heof⟩
  subst Hct
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  icases wire.ed_of_poll $$ Hpoll with ⟨%ed, #Hed⟩
  ihave #Hacc := server_read_acc γm cn ns NetEnd.fresh $$ [HhcInv Hname]
  · iframe HhcInv Hname
  wp_auto
  wp_apply wp_readAll wp_Read (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true
      srvAddr x ed (srvP ns cn NetEnd.fresh) $$ [Hend Hr]
    as %sl %ok ⟨%data, Hd, HP⟩
  · iframe Heof Hed
    isplitl []
    · unfold net.isConn
      iexists t, la, ra
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
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend] as %err ⟨%res, -, -⟩
    · iframe Hc
      iapply hc_close_au γm cn ns true _ $$ HhcInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- EOF: write back what was read, then close
    wp_auto
    ihave #Hwacc := server_write_acc γm cn ns NetEnd.fresh data $$ [HhcInv Hname]
    · iframe HhcInv Hname
    wp_apply wp_Write t cn true srvAddr la ra sl data (DFrac.own 1) ed
        (fun w _ => srvW ns cn NetEnd.fresh data w) $$ [Hd Hend Hw Hr]
      as %n %err ⟨%w, %res, HW, Hd, -⟩
    · iframe Hc Hd Hed Hwacc
      unfold srvW
      iframe Hend Hw Hr
    unfold srvW
    icases HW with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err' ⟨%res', -, -⟩
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
        ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hplan, #Heof⟩
  icases hcInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HhcInv⟩
  (try wp_auto)
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp srvAddr $$ []
    as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%xa, %exa, #Hxa, HE, -⟩)
  · iframe %Hplan
    iapply wire.listen_au addrN srvAddr _ $$ HaddrInv
  · -- listening: the accept loop
    subst Herr
    unfold net.isListener
    icases Hli with ⟨%t, %xl, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true :
      IProp GF) $$ [Hlis]
    · iexact Hlis
    wp_for HI
    wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l xl srvAddr
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%k, Hlis, HE⟩)
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
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_for_post
      iframe
  · -- not listening: return
    icases net.opErr_netErr _ _ _ _ _ $$ HE with %Hne
    obtain ⟨pe, rfl⟩ := Hne
    wp_auto
    iapply HΦ
    itrivial

theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_CloseWrite : net.TCPConn.CloseWrite.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (x : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ hcInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases hcInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HhcInv⟩
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  icases wire.ed_of_poll $$ Hpoll with ⟨%ed, #Hed⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => clientProto γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hcp⟩ | ⟨-, %xa, #Hxa, HE⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply dial_both_au addrN srvAddr (connProto γm) (clientProto γm) $$ HaddrInv
      · iintro %cn #Hat Hd Ha
        iapply hc_deposit γm cn $$ HhcInv Hat Hd Ha
      · iintro %cn #Hat He Hd Ha
        iapply hc_deposit_ab γm cn $$ HhcInv Hat He Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    unfold clientProto
    icases Hcp with ⟨%ns, Hend, Hw, Hr, #Hname⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    ihave #Hwacc := client_write_acc γm cn ns NetEnd.fresh $$ [HhcInv Hname]
    · iframe HhcInv Hname
    wp_apply wp_Write t cn false srvAddr la ra sl _ (DFrac.own 1) ed
        (fun w _ => cliW ns cn NetEnd.fresh w) $$ [Hsl Hend Hw]
      as %n %err ⟨%w, %res, HW, Hsl, -, HE⟩
    · iframe Hca Hsl Hed Hwacc
      unfold cliW
      iframe Hend Hw
    unfold cliW
    icases HW with ⟨Hend, -⟩
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Herr
    cases res
    case some e =>
      -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr.2 (by simp)
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply hc_close_au γm cn ns false _ $$ HhcInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Herr.1 rfl]
    wp_auto
    -- shut the write side
    wp_apply wp_CloseWrite t cn false srvAddr la ra (fun _ => netEnd G cn false NetEnd.fresh)
        $$ [Hend]
      as %err ⟨%resc, Hend, HE⟩
    · iframe Hca
      iapply hc_closeWrite_au γm cn ns false NetEnd.fresh $$ HhcInv Hname Hend
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Herr
    cases resc
    case some e =>
      -- the shutdown failed: close and return
      obtain ⟨pe, rfl⟩ := Herr.2 (by simp)
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply hc_close_au γm cn ns false _ $$ HhcInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Herr.1 rfl]
    wp_auto
    -- read the response until EOF or an error
    ihave #Hacc := client_read_acc γm cn ns NetEnd.fresh $$ [HhcInv Hname]
    · iframe HhcInv Hname
    wp_apply wp_readAll wp_Read (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr x ed (cliP ns cn NetEnd.fresh) $$ [Hend Hr]
      as %rsl %ok ⟨%data, Hd, HP⟩
    · iframe Heof Hed
      isplitl []
      · unfold net.isConn
        iexists t, la, ra
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
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
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
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply hc_close_au γm cn ns false _ $$ HhcInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
  · -- the dial failed: return
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
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
