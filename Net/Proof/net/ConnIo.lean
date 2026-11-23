/-
**A connection's end as an `io.Reader` and an `io.Writer`** (dsv-bufio, 2026-11-23,
mit-pdos/etcd-grove#24): laws giving the generic `io` contracts (Perennial's `io.readerOk`,
`Proof/io/WriterOk.lean`'s `io.writerOk`) of a `*TCPConn` `t` that is the end `s` of the connection
`cn` (`connAt`), from the canonical `Conn.Read`/`Conn.Write` specs (hypotheses) and the protocol
vocabulary of `GooseLang/Ext/Net/Proto.lean`. So the kits' `bufio.NewReader(conn)` /
`bufio.NewWriter(conn)` (`Spec/bufio/`) apply over a connection with the stream states
`recvTokL cn s P` (reader) and `sendTok cn s P` (writer), and so does Perennial's `io.ReadFull`
through such a `*bufio.Reader` (`bufio.ownBufReader_readerOk`: its condition `0 < m → …` is vacuous
at `m = 0`).

Perennial's `io.ReadFull(conn, ...)` / `io.ReadAtLeast(conn, ...)` directly over a connection do
**not** follow from these laws yet (review C1 on #24): their premise asks `Pre` at every
`ys.length ≤ len(buf)`, `ys.length = len(buf)` (a read of `0` bytes, `m = 0`) included, which
`conn_readerOk`'s condition `0 < m` refuses. Either fix makes it follow: `net.Conn.Read`'s count
exact (`ReadOut`'s `sint.nat k = min …` admits a negative `k` when `min = 0`, the reason for the
`0 < m`), so the condition can be `True`; or `ReadAtLeast`'s premise asked only at
`ys.length < min` (the code reads only while `n < min`): the latter is on a Perennial branch
(`notes/perennial-changes.md`, 2026-11-23, "ReadAtLeast's premise").

* `conn_readerOk`: `io.readerOk (connIface t) (fun _ m => 0 < m) (recvTokL cn s P) (connReadE ...)`:
  a read of a non-empty buffer returns the next bytes of the direction towards `s` (`recvTokL`
  extended by them; their protocol fact a step later), and its errors are `io.EOF`'s value `eof` or
  a read `*OpError` (`connReadE`). Reads of an empty buffer are excluded (`0 < m`; see above).
* `connReader_proto`: what a `*bufio.Reader` over a connection has returned meets the protocol up to
  extension, a step later (`recvTokL_proto` with `bufio.ownBufReader_fact`).
* `conn_writerOk`: `io.writerOk (connIface t) (sendTok cn s P) (P cn) (connWriteE ...)` for a
  protocol closed under prefixes (`ProtoPrefixClosed`): a write extends `sendTok` by a prefix of
  the bytes (all of them on `nil`), each needing `□ P cn` of the whole stream; its errors are write
  `*OpError`s.
Lean-first.
-/
module

public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import GooseLang.Ext.Net.Proto
public import GooseLang.Ext.Net.Stream
public import Proof.io.WriterOk
public import Proof.bufio.Own
public import Code.bufio

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- The interface value of a `*TCPConn` (what a `net.Conn` holds). -/
def connIface (t : Loc) : GoInterfaceOk := ⟨go.GoType.PointerType TCPConn.ty, #t⟩

/-- The errors of a connection's reads: `io.EOF`'s value, or a read `*OpError`. Position-free: an
`io.EOF` claims nothing about the bytes `R` read so far being all the peer wrote (the evidence
ignores `R`); a client that needs that proves it from its protocol (review C4 on #24). -/
def connReadE (eof la ra ed : GoInterface) : List w8 → GoInterface → IProp GF :=
  fun _ e => iprop(⌜e = eof⌝ ∨ ∃ k, resErr (some k) go!"read" la ra (some ed) (· = go!"read") e)

/-- The errors of a connection's writes: a write `*OpError`. -/
def connWriteE (la ra ed : GoInterface) : GoInterface → IProp GF :=
  fun e => iprop(∃ k, resErr (some k) go!"write" la ra (some ed) (· = go!"write") e)

/-- A connection is not a `*bufio.Reader` (what `bufio.NewReader`'s spec asks of its reader). -/
theorem connIface_ne_bufioReader (t : Loc) :
    (connIface t).ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty := by
  unfold connIface TCPConn.ty _root_.Perennial.bufio.Reader.ty
  intro h; cases h

/-- A connection is not a `*bufio.Writer` (what `bufio.NewWriter`'s spec asks of its writer). -/
theorem connIface_ne_bufioWriter (t : Loc) :
    (connIface t).ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Writer.ty := by
  unfold connIface TCPConn.ty _root_.Perennial.bufio.Writer.ty
  intro h; cases h

/-- `io.EOF`'s value is a pointer (`io.ptrTyped`), from `io`'s package facts (review C3 on #24:
until then a hypothesis of `conn_readerOk`). -/
theorem eof_ptrTyped [_root_.Perennial.io.Assumptions] (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ⊢ ⌜io.ptrTyped eof⌝ := by
  iintro ⟨#Hio, #He⟩
  ihave #Hv := io.eof_of_init $$ Hio
  iunfold errors.newVar at Hv
  icases Hv with ⟨%x, #Hx, -⟩
  icombine He Hx gives %Heq
  ipureintro
  subst Heq
  intro ii T h _
  cases h
  exact ⟨x, rfl⟩

theorem netErr_ptrTyped {e : GoInterface} (h : netErr e) : io.ptrTyped e := by
  obtain ⟨pe, rfl⟩ := h
  intro ii T h _
  cases h
  exact ⟨pe, rfl⟩

/-- See the file header. `eof` is `io.EOF`'s value. -/
theorem conn_readerOk [_root_.Perennial.io.Assumptions]
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra eof ed : GoInterface) (P : Proto GF) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ connAt (GF := GF) t cn s a la ra ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ⊢
      io.readerOk (connIface t) (fun _ m => 0 < m) (recvTokL (Gg := hG.goose_globalGS) cn s P)
        (connReadE eof la ra ed) := by
  iintro ⟨#Hio, #Hc, #Heof, #Hed⟩
  ihave %heof := eof_ptrTyped eof $$ [Hio Heof]
  · iframe Hio Heof
  unfold io.readerOk connIface
  iintro !> %R %p %xs
  iintro !> %Φ ⟨%hpos, HP, Hp⟩ HΦ
  dsimp only
  ihave %Hlen := ownSlice_len _ _ _ $$ Hp
  have hpl : p.len.toNat = xs.length := by rw [Hlen.1]; word
  iapply wp_Read t cn s a la ra p xs eof ed
    (fun r => iprop(recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ r.got) ∗
      ⌜r.got.length ≤ p.len.toNat ∧ (r = .bytes [] → p.len.toNat = 0)⌝)) $$ [HP Hp]
  · iframe Hc Hp Heof Hed
    imod read_au cn s P R p.len.toNat $$ HP with ⟨%st, %d, HE, HD, Hcl⟩
    imodintro
    iexists st, d
    iframe HE HD
    iintro %r %d' %Hrd HE HD
    imod Hcl $$ %r %d' %Hrd HE HD with ⟨HP, -⟩
    imodintro
    iframe HP
    ipureintro
    exact readOutcome_got_le Hrd
  iintro !> %k %err ⟨%r, %bs', ⟨HP, %Hrl⟩, Hp, %Hout, HE⟩
  iapply HΦ
  rw [hpl] at Hrl
  cases r with
  | bytes bs =>
    obtain ⟨hk, rfl⟩ := Hout
    simp only [net.ReadErr]
    icases HE with %Herr
    subst Herr
    simp only [ReadRes.got] at Hrl
    isimp only [ReadRes.got] at HP
    have hb1 : 1 ≤ bs.length := by
      rcases bs with _ | ⟨b, bs⟩
      · have := Hrl.2 rfl; omega
      · simp
    iexists bs
    rw [List.take_of_length_le Hrl.1]
    iframe Hp HP
    isplitr
    · ipureintro
      refine ⟨?_, Hrl.1⟩
      rw [Nat.min_eq_right Hrl.1] at hk
      have : sint.nat k = (sint.Z k).toNat := rfl
      omega
    isplitl
    · unfold io.errAt; ileft; ipureintro; rfl
    ipureintro; exact io.ptrTyped_nil
  | eof =>
    obtain ⟨rfl, rfl⟩ := Hout
    simp only [net.ReadErr]
    icases HE with %Herr
    subst Herr
    isimp only [ReadRes.got, List.append_nil] at HP
    iexists []
    simp only [List.append_nil, List.nil_append, List.length_nil, List.drop_zero]
    iframe Hp HP
    isplitr
    · ipureintro; exact ⟨rfl, Nat.zero_le _⟩
    isplitl
    · unfold io.errAt connReadE; iright; imodintro; ileft; ipureintro; rfl
    ipureintro; exact heof
  | err e =>
    obtain ⟨rfl, rfl⟩ := Hout
    simp only [net.ReadErr]
    icases HE with #HE
    ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    isimp only [ReadRes.got, List.append_nil] at HP
    iexists []
    simp only [List.append_nil, List.nil_append, List.length_nil, List.drop_zero]
    iframe Hp HP
    isplitr
    · ipureintro; exact ⟨rfl, Nat.zero_le _⟩
    isplitl
    · unfold io.errAt connReadE; iright; imodintro; iright; iexists e; iexact HE
    ipureintro; exact netErr_ptrTyped (Hne.2 (by simp))

/-- See the file header. -/
theorem conn_writerOk (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra ed : GoInterface) (P : Proto GF)
    (hP : ProtoPrefixClosed P) :
    connAt (GF := GF) t cn s a la ra ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ⊢
      EtcdGrove.io.writerOk (connIface t) (sendTok (Gg := hG.goose_globalGS) cn s P) (P cn)
        (connWriteE la ra ed) := by
  iintro ⟨#Hc, #Hed⟩
  unfold EtcdGrove.io.writerOk EtcdGrove.io.prefixClosed connIface
  isplitr
  · iintro !> %x %y #Hxy
    ihave #Hx := hP.pre cn x (x ++ y) (List.prefix_append x y) $$ Hxy
    iexact Hx
  iintro !> %W %p %dq %xs
  iintro !> %Φ ⟨HS, #HQ, Hp⟩ HΦ
  dsimp only
  iapply wp_Write t cn s a la ra p xs dq ed (writeP cn s P W) $$ [HS Hp]
  · iframe Hc Hp Hed
    isplitl [HS]
    · iapply writeP_init $$ HS
    · iapply write_acc cn s P W xs $$ HQ
  iintro !> %n %err ⟨%w, %res, HS, Hp, %Hw, #HE⟩
  ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
  obtain ⟨⟨z, rfl⟩, hn, hnone, -⟩ := Hw
  unfold writeP
  iapply HΦ
  iexists w.length
  rw [List.take_left]
  iframe Hp HS
  isplitr
  · ipureintro
    refine ⟨hn, by simp, fun h => ?_⟩
    rcases res with _ | k
    · rw [← hnone rfl]
    · exact absurd h (netErr_ne_nil (Hne.2 (by simp)))
  unfold EtcdGrove.io.werrAt connWriteE
  rcases res with _ | k
  · ileft; ipureintro; exact Hne.1 rfl
  · iright; imodintro; iexists k; iexact HE

/-- See the file header (review C2 on #24: the kits' `ownReader_proto`, without unfolding). -/
theorem connReader_proto (br : Loc) (ri : GoInterfaceOk)
    (Pre : List w8 → Nat → Prop) (cn : Nat) (s : Bool) (P : Proto GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) :
    EtcdGrove.bufio.ownBufReader br ri Pre (recvTokL (Gg := hG.goose_globalGS) cn s P) E R ⊢
      EtcdGrove.bufio.ownBufReader br ri Pre (recvTokL (Gg := hG.goose_globalGS) cn s P) E R ∗
        ▷ protoPrefix P cn R :=
  EtcdGrove.bufio.ownBufReader_fact br ri Pre _ E R (fun r => iprop(▷ protoPrefix P cn r))
    (fun r => recvTokL_proto cn s P r)
    (fun x y => later_mono (protoPrefix_le (List.prefix_append x y)))

end laws

end net
end Perennial
