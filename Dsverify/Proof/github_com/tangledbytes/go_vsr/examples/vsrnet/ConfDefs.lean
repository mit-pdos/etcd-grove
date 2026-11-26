/-
The definitions, specs and lemmas of `Conf.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Net.Proof.net.AtAddr
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Kit
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.Addrs
public import Perennial.Proof.github_com.goose_lang.primitive.RandomUint64
public import Perennial.Proof.io.Link
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import GooseLang.Ext.Net.Stream
public import Net.Proof.net.ConnIo

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The configuration's wire -/

/-- The configuration's three bytes (`Conf.encode`: N, the heartbeat's and the request timeout's
positions in their lists). -/
def confBytes (n h r : Nat) : List w8 := [W8 (n : Int), W8 (h : Int), W8 (r : Int)]

/-- A configuration `decode` accepts: N = 3 or 5, the timeouts' positions in their lists. -/
def ConfOk (n h r : Nat) : Prop := (n = 3 ∨ n = 5) ∧ h < 8 ∧ r < 7

section conf
variable [GooseExts]

instance Conf.countable : Pos.Countable Conf :=
  .ofInjective (fun c => Pos.Countable.encode (c.N', c.Heartbeat', c.Request'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

/-- A configuration as three numbers. -/
def confOf (n h r : Nat) : Conf := ⟨W64 (n : Int), W64 (h : Int), W64 (r : Int)⟩

end conf

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The protocol of what the orchestrator writes to a configuration address: a prefix of one
accepted configuration's bytes, whose number of replicas is the system's (`fact γ (.size n)`:
the orchestrator fixed it before it sends; only it writes, and only its one choice). -/
def confProto (γ : Names) : Proto GF :=
  fun _cid W => iprop(∃ n h r : Nat, ⌜W <+: confBytes n h r ∧ ConfOk n h r⌝ ∗ fact γ (.size n))

/-- The protocol of a configuration address's answers (one byte; it means nothing). -/
def ackProto : Proto GF := fun _cid _W => iprop(True)

/-- Every configuration address's protocols (persistent; the start sets them). -/
def confProtos (γ : Names) : IProp GF :=
  iprop([∗list] a ∈ cfgAddrs, addrProto a (confProto γ) ackProto)

instance confProtos_persistent (γ : Names) : Persistent (confProtos (GF := GF) γ) := by
  unfold confProtos; infer_instance

/-- What a machine learns: a configuration `decode` accepts, whose number of replicas is the
system's. -/
def confOk (γ : Names) (cf : Conf) : IProp GF :=
  iprop(∃ n h r : Nat, ⌜cf = confOf n h r ∧ ConfOk n h r⌝ ∗ fact γ (.size n))

instance confOk_persistent (γ : Names) (cf : Conf) : Persistent (confOk (GF := GF) γ cf) := by
  unfold confOk; infer_instance

/-- The orchestrator fixes the number of replicas of its chosen configuration (`ghost_size` of its
`sizeTok`, as the lab's `wp_New_proof`), before it sends the configuration (`Configure`). -/
theorem conf_size (γ : Names) {n h r : Nat} (hc : ConfOk n h r) :
    sysInv (GF := GF) γ -∗ sizeTok γ ={⊤}=∗ fact γ (.size n) :=
  ghost_size γ ⊤ CoPset.subseteq_top n (by rcases hc.1 with rfl | rfl <;> decide)

end defs

/-! ## Pure facts -/

/-- Three bytes read from a configuration address are the orchestrator's configuration. -/
theorem conf_of_prefix {R : List w8} {n h r : Nat} (hl : R.length = 3)
    (hp : R <+: confBytes n h r) : R = confBytes n h r :=
  hp.eq_of_length (by simp [hl, confBytes])

theorem decode_ok [GooseExts] (x y z : w8)
    (hn : W64 (uint.Z x) = W64 3 ∨ W64 (uint.Z x) = W64 5)
    (hy : uint.Z (W64 (uint.Z y)) < uint.Z (W64 8)) (hz : uint.Z (W64 (uint.Z z)) < uint.Z (W64 7)) :
    (⟨W64 (uint.Z x), W64 (uint.Z y), W64 (uint.Z z)⟩ : Conf) =
        confOf (uint.nat x) (uint.nat y) (uint.nat z) ∧
      ConfOk (uint.nat x) (uint.nat y) (uint.nat z) := by
  have ex : ((uint.nat x : Nat) : Int) = uint.Z x := by word
  have ey : ((uint.nat y : Nat) : Int) = uint.Z y := by word
  have ez : ((uint.nat z : Nat) : Int) = uint.Z z := by word
  refine ⟨by simp only [confOf, ex, ey, ez], ?_⟩
  unfold ConfOk
  refine ⟨?_, by word, by word⟩
  rcases hn with h | h
  · left; word
  · right; word

theorem confOk_lt {n h r : Nat} (hc : ConfOk n h r) : n < 256 ∧ h < 256 ∧ r < 256 := by
  unfold ConfOk at hc; omega

theorem confBytes_eq [GooseExts] {x y z : w8} {n h r : Nat} (hc : ConfOk n h r)
    (he : [x, y, z] = confBytes n h r) :
    confOf (uint.nat x) (uint.nat y) (uint.nat z) = confOf n h r := by
  obtain ⟨hn, hh, hr⟩ := confOk_lt hc
  simp only [confBytes, List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have e : ∀ m : Nat, m < 256 → uint.nat (W8 (m : Int)) = m := fun m hm => by word
  rw [e n hn, e h hh, e r hr]

theorem dec_val_false' [GooseExts] [GoGlobalContext] : decide ((#false : val) = #true) = false := by
  simp only [decide_eq_false_iff_not]
  intro h
  have := GoGlobalContext.intoVal_inj_bool h
  simp at this

/-! ## The proofs -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- `CfgAddrs()`: a new slice of the configuration addresses. -/
abbrev CfgAddrs.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.CfgAddrs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* cfgAddrs }}

theorem wp_heartbeatMs (i : w64) (hi : uint.nat i < 8) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.heartbeatMs)) (Val #i))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64)
    [W64 1, W64 2, W64 3, W64 5, W64 10, W64 20, W64 100, W64 500]
  wp_auto
  rw [show go.arrayLiteralSize
    [KeyedElement none (ElementExpression go.uint64 #(W64 1)),
      KeyedElement none (ElementExpression go.uint64 #(W64 2)),
      KeyedElement none (ElementExpression go.uint64 #(W64 3)),
      KeyedElement none (ElementExpression go.uint64 #(W64 5)),
      KeyedElement none (ElementExpression go.uint64 #(W64 10)),
      KeyedElement none (ElementExpression go.uint64 #(W64 20)),
      KeyedElement none (ElementExpression go.uint64 #(W64 100)),
      KeyedElement none (ElementExpression go.uint64 #(W64 500))] = 8 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z (W64 8) := by word
  rw [ite_eq_left hb]
  obtain ⟨x, hx⟩ : ∃ x, [W64 1, W64 2, W64 3, W64 5, W64 10, W64 20, W64 100, W64 500][(sint.Z i).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by simp; word)⟩
  wp_apply wp_load_slice_index _ _ _ _ x hb.1 $$ [$Hsl] as Hsl
  · ipureintro; exact hx
  iapply HΦ; itrivial

theorem wp_requestMs (i : w64) (hi : uint.nat i < 7) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.requestMs)) (Val #i))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64)
    [W64 10, W64 20, W64 50, W64 100, W64 200, W64 500, W64 1000]
  wp_auto
  rw [show go.arrayLiteralSize
    [KeyedElement none (ElementExpression go.uint64 #(W64 10)),
      KeyedElement none (ElementExpression go.uint64 #(W64 20)),
      KeyedElement none (ElementExpression go.uint64 #(W64 50)),
      KeyedElement none (ElementExpression go.uint64 #(W64 100)),
      KeyedElement none (ElementExpression go.uint64 #(W64 200)),
      KeyedElement none (ElementExpression go.uint64 #(W64 500)),
      KeyedElement none (ElementExpression go.uint64 #(W64 1000))] = 7 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z (W64 7) := by word
  rw [ite_eq_left hb]
  obtain ⟨x, hx⟩ : ∃ x, [W64 10, W64 20, W64 50, W64 100, W64 200, W64 500, W64 1000][(sint.Z i).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by simp; word)⟩
  wp_apply wp_load_slice_index _ _ _ _ x hb.1 $$ [$Hsl] as Hsl
  · ipureintro; exact hx
  iapply HΦ; itrivial

/-- `choose()`: some configuration `decode` accepts. -/
theorem wp_choose :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.choose)) (Val #()))
    {{ (n h r : Nat), RET #(confOf n h r); ⌜ConfOk n h r⌝ }} := by
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.RandomUint64.wp_proof as %x1 -
  wp_if_destruct <;>
  · wp_apply github_com.goose_lang.primitive.RandomUint64.wp_proof as %x2 -
    wp_apply github_com.goose_lang.primitive.RandomUint64.wp_proof as %x3 -
    have e2 : W64 ((uint.nat (x2 % W64 8) : Nat) : Int) = x2 % W64 8 := by word
    have e3 : W64 ((uint.nat (x3 % W64 7) : Nat) : Int) = x3 % W64 7 := by word
    first
    | (ihave H := HΦ $$ %5 %(uint.nat (x2 % W64 8)) %(uint.nat (x3 % W64 7))
       unfold confOf
       rw [e2, e3]
       iapply H
       ipureintro
       refine ⟨Or.inr rfl, ?_, ?_⟩ <;> word)
    | (ihave H := HΦ $$ %3 %(uint.nat (x2 % W64 8)) %(uint.nat (x3 % W64 7))
       unfold confOf
       rw [e2, e3]
       iapply H
       ipureintro
       refine ⟨Or.inl rfl, ?_, ?_⟩ <;> word)

/-- `c.encode()`: the configuration's three bytes. -/
theorem wp_Conf_encode (n h r : Nat) (hc : ConfOk n h r) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (confOf n h r @!! Conf.ty @!! go!"encode")) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* confBytes n h r }} := by
  obtain ⟨hn, hh, hr⟩ := hc
  have e : ∀ m : Nat, m < 256 → W8 (uint.Z (W64 (m : Int))) = W8 (m : Int) := by
    intro m hm
    rw [show uint.Z (W64 (m : Int)) = (m : Int) by word]
  have hn' : n < 256 := by rcases hn with rfl | rfl <;> decide
  wp_start
  wp_auto
  rw [e n hn', e h (by omega), e r (by omega)]
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) (confBytes n h r)
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `decode(b)` of three bytes: the configuration they spell, accepted exactly when `ConfOk`. -/
theorem wp_decode (sl : GoSlice) (x y z : w8) (dq : DFrac) :
    {{ (sl ↦*{dq} [x, y, z] : IProp GF) }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.decode)) (Val #sl))
    {{ (cf : Conf) (ok : Bool), RET (PairV #cf #ok); sl ↦*{dq} [x, y, z] ∗
        ⌜ok = true → cf = confOf (uint.nat x) (uint.nat y) (uint.nat z) ∧
          ConfOk (uint.nat x) (uint.nat y) (uint.nat z)⌝ }} := by
  wp_start as Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  have hl : sint.Z sl.len = 3 := by
    have := Hlen.1; simp at this; word
  wp_auto
  simp only [hl, show sint.Z (W64 0) = 0 from rfl]
  wp_apply (wp_load_slice_index sl 0 [x, y, z] dq x (by decide)) $$ [Hsl] as Hsl
  · iframe; ipureintro; rfl
  simp only [hl, show sint.Z (W64 1) = 1 from rfl]
  wp_apply (wp_load_slice_index sl 1 [x, y, z] dq y (by decide)) $$ [Hsl] as Hsl
  · iframe; ipureintro; rfl
  simp only [hl, show sint.Z (W64 2) = 2 from rfl]
  wp_apply (wp_load_slice_index sl 2 [x, y, z] dq z (by decide)) $$ [Hsl] as Hsl
  · iframe; ipureintro; rfl
  all_goals repeat (first | wp_if_destruct | wp_auto)
  rotate_left 3
  by_cases h5 : W64 (uint.Z x) = W64 5 <;>
    first | rw [decide_eq_true h5] | rw [decide_eq_false h5]
  all_goals repeat (first | wp_if_destruct | wp_auto)
  all_goals (iapply HΦ; iframe; ipureintro)
  all_goals first
    | (intro _; exact decode_ok x y z (by first | exact Or.inl ‹_› | exact Or.inr ‹_›) ‹_› ‹_›)
    | (intro h; cases h)

/-- The values the connection's specs and `io.ReadFull` name: `io.EOF`'s (a pointer),
`io.ErrUnexpectedEOF`'s (not `nil`), `poll.ErrDeadlineExceeded`'s. -/
theorem errs_init :
    isPkgInit (PROP := IProp GF) kpkg ⊢
      ∃ eof ueof ed : GoInterface, ⌜io.ptrTyped eof ∧ ueof ≠ interface.nil⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave ⟨%ed, #Hed⟩ := github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll
  ihave Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, HEOF, HUE, -⟩
  isimp only [_root_.Perennial.errors.newVar] at HEOF HUE
  icases HEOF with ⟨%eofl, #Heof, -⟩
  icases HUE with ⟨%uel, #Hue, -⟩
  iexists _, _, ed
  iframe Heof Hue Hed
  ipureintro
  refine ⟨?_, by intro h; cases h⟩
  intro ii T h _
  cases h
  exact ⟨eofl, rfl⟩

/-- A connection's `Close`: any result. -/
theorem wp_closeConn (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    {{ net.connAt (GF := GF) t cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hca, #Hconn⟩ HΦ
  iapply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ []
  · iframe Hca
    imod close_au cn s $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd' Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
    imodintro
    itrivial
  iintro !> %err -
  iapply HΦ; itrivial

/-- `sendConf(a, b)`: the orchestrator sends the configuration's bytes `b` to `a` (under
`confProto`) and reads the answer; any result. -/
theorem wp_sendConf (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (γ : Names) (a : GoString) (b : GoSlice) (n h r : Nat) (hc : ConfOk n h r) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗
        addrProto (Gg := hG.goose_globalGS) a (confProto γ) ackProto ∗ fact γ (.size n) ∗
        b ↦* confBytes n h r }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.sendConf)) (Val #a))
        (Val #b))
    {{ (ok : Bool), RET #ok; True }} := by
  wp_start as ⟨#Hpr, #Hf, Hb⟩
  ihave ⟨%eof, %ueof, %ed, %Hev, #Heof, #Hue, #Hed⟩ := errs_init $$ Hpkg
  ihave %Hok := addrTok_ok a $$ [Hpr]
  · iapply addrProto_tok $$ Hpr
  wp_auto
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp a iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (confProto γ) ackProto [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
    as %cv %err (⟨%Herr, %cn, #Hc, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au a (confProto γ) ackProto $$ Hpr
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  unfold net.isConn
  icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
  subst Hct
  iunfold connEnd at Hend
  icases Hend with ⟨Hs, Hrv⟩
  ihave #Hconn := sendTok_connIs cn false _ _ $$ Hs
  wp_auto
  ihave #Hp0 : (□ confProto γ cn ([] ++ confBytes n h r) : IProp GF) $$ []
  · iintro !>
    unfold confProto
    iexists n, h, r
    iframe Hf
    ipureintro; exact ⟨List.prefix_refl _, hc⟩
  wp_apply wp_Write t cn false a la ra b _ _ ed (writeP (Gg := hG.goose_globalGS) cn false (confProto γ) [])
      $$ [Hb Hs] as %nw %werr ⟨%w, %res, Hs, Hb, %Hw, #HE⟩
  · iframe Hca Hb Hed
    isplitl [Hs]
    · iapply writeP_init $$ Hs
    · iapply write_acc cn false (confProto γ) [] _ $$ Hp0
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
  cases res with
  | some k =>
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_apply wp_closeConn wp_Close t cn false a la ra $$ [] as %e -
    · iframe Hca Hconn
    iapply HΦ; itrivial
  | none =>
  have := Hne.1 rfl
  subst this
  wp_auto
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hrd := net.conn_readerOk wp_Read t cn false a la ra eof ed ackProto $$ [$Hio $Hca $Heof $Hed]
  iunfold net.connIface at Hrd
  ihave Hrv := recvTok_L $$ Hrv
  ihave Hs2 := slice_array a_ptr 1 _ (by decide) $$ a
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 1 - W64 0) = W64 1 from rfl,
    show (zero_val (GoArray w8 1)).arr = [W8 0] from rfl]
  wp_apply io.wp_ReadFull ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩ (fun _ m => 0 < m)
      (recvTokL (Gg := hG.goose_globalGS) cn false ackProto) (net.connReadE eof la ra ed) [] (slice.mk a_ptr (W64 1) (W64 1)) [W8 0] eof ueof
      $$ [Hrv Hs2] as %n2 %err2 ⟨%ys, %Hys, Hs2, Hrv, #Hres⟩
  · iframe Hrd Heof Hue Hrv Hs2; ipureintro; intro _ hl; simp only [List.length_cons, List.length_nil] at hl ⊢; omega
  iunfold io.readFullRes at Hres
  icases Hres with (%Hl | ⟨%e, %He, -⟩)
  rotate_left
  · have herr : err2 ≠ GoInterface.nil := by
      obtain ⟨-, hne, h1, h2⟩ := He
      by_cases hc : e = eof ∧ ys ≠ []
      · rw [h1 hc]; exact Hev.2
      · rw [h2 hc]; exact hne
    cases err2 with
    | nil => exact absurd rfl herr
    | ok i =>
    wp_auto
    wp_apply wp_closeConn wp_Close t cn false a la ra $$ [] as %e2 -
    · iframe Hca Hconn
    iapply HΦ; itrivial
  obtain ⟨hl, rfl⟩ := Hl
  obtain ⟨b2, rfl⟩ : ∃ b2, ys = [b2] := by
    match ys, hl with
    | [b2], _ => exact ⟨b2, rfl⟩
  rw [show List.drop [b2].length [W8 0] = [] from rfl, List.append_nil]
  wp_auto
  rw [show arrayIndexRef w8 (sint.Z (W64 0)) a_ptr =
    sliceIndexRef w8 (sint.Z (W64 0)) (slice.mk a_ptr (W64 1) (W64 1)) from rfl]
  wp_apply wp_load_slice_index _ _ [b2] _ b2 (by decide) $$ [$Hs2] as Hs2
  · ipureintro; rfl
  wp_if_destruct <;>
  · wp_apply wp_closeConn wp_Close t cn false a la ra $$ [] as %e2 -
    · iframe Hca Hconn
    iapply HΦ; itrivial

/-- `Configure(cfgs, conf)`: the configuration `conf` (an accepted one, whose number of replicas
`n` the orchestrator fixed, `fact γ (.size n)`) is sent to machines `1 .. NC + n`, each until it
acknowledges it. -/
abbrev Configure.spec : Prop :=
  ∀ (γ : Names) (cfgs : GoSlice) (dq : DFrac) (n h r : Nat), ConfOk n h r →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ cfgs ↦*{dq} cfgAddrs ∗
      confProtos (G := hG.goose_globalGS) γ ∗ fact γ (.size n) }}
    (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Configure)) (Val #cfgs))
      (Val #(confOf n h r)))
  {{ RET #(); cfgs ↦*{dq} cfgAddrs }}

/-- The three bytes read on a configuration address, `decode`d, are what a machine learns. -/
theorem conf_learn (γ : Names) (cid : Nat) (x y z : w8) (cf : Conf)
    (hcf : cf = confOf (uint.nat x) (uint.nat y) (uint.nat z)) :
    protoPrefix (confProto (G := hG.goose_globalGS) γ) cid [x, y, z] ⊢ confOk γ cf := by
  iintro Hpp
  unfold protoPrefix
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #Hp⟩)
  · cases Hnil
  unfold confProto
  icases Hp with ⟨%n, %h, %r, %Hw, #Hf⟩
  obtain ⟨hpre, hok⟩ := Hw
  have he : [x, y, z] = confBytes n h r :=
    conf_of_prefix (by rfl) (Hext.trans hpre)
  unfold confOk
  iexists n, h, r
  iframe Hf
  ipureintro
  exact ⟨hcf.trans (confBytes_eq hok he), hok⟩

/-- `awaitConf(addr, ch)`: listens on `addr` (a failed `Listen` retried), accepts forever; a
connection's three bytes (`io.ReadFull`) are a prefix of the orchestrator's `confBytes n h r`
(`confProto`), so they are that configuration, with `fact γ (.size n)`; the first accepted one is
sent on `ch` (the future's `Fulfill`), each is acknowledged (`ackProto`: anything), the
connection closed. It never returns. -/
theorem wp_awaitConf (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (γ : Names) (γf : FutureNames) (ch : Loc) (addr : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗
        addrProto (Gg := hG.goose_globalGS) addr (confProto γ) ackProto ∗
        isFuture Conf γf ch ∗ Fulfill γf (confOk (G := hG.goose_globalGS) γ) }}
      (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.awaitConf)) (Val #addr))
        (Val #ch))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpr, #Hfut, Hful⟩
  ihave ⟨%eof, %ueof, %ed, %Hev, #Heof, #Hue, #Hed⟩ := errs_init $$ Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave %Hok := addrTok_ok addr $$ [Hpr]
  · iapply addrProto_tok $$ Hpr
  wp_auto
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp addr as %lv %err Hres
  · iframe %Hok
    iapply listen_au $$ Hpr
  ihave HL : (∃ (lv err : GoInterface), "l" ∷ l_ptr ↦ lv ∗ "err" ∷ err_ptr ↦ err ∗
      "Hres" ∷ ((⌜err = GoInterface.nil⌝ ∗ ∃ l, net.isListener lv l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l addr true ∗
          netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l addr) ∨
        ⌜err ≠ GoInterface.nil⌝) : IProp GF) $$ [l err Hres]
  · iexists lv, err; iframe l err
    icases Hres with (H | ⟨%x, -, #HE⟩)
    · ileft; iexact H
    · iright
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      ipureintro; exact net.netErr_ne_nil (Hne.2 (by simp))
  wp_for HL
  icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | %Hne)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Hne
    | ok i =>
    wp_auto
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    wp_apply time.wp_Sleep
    wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp addr as %lv2 %err2 Hres
    · iframe %Hok
      iapply listen_au $$ Hpr
    wp_for_post
    iframe
    iexists lv2, err2; iframe
    icases Hres with (H | ⟨%x, -, #HE⟩)
    · ileft; iexact H
    · iright
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      ipureintro; exact net.netErr_ne_nil (Hne.2 (by simp))
  subst He
  wp_auto
  rw [dec_val_false']
  simp only [Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
  wp_auto
  unfold net.isListener
  icases Hl with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  ihave HI : (∃ (fst : Bool), "first" ∷ first_ptr ↦ fst ∗
      "Hful" ∷ (if fst then Fulfill γf (confOk (G := hG.goose_globalGS) γ) else True) : IProp GF)
    $$ [first Hful]
  · iexists true; iframe first; simp only [↓reduceIte]; iexact Hful
  wp_for HI
  cleanup_bool_decide
  wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x addr
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l addr true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l addr true ∗
        connEnd (Gg := hG.goose_globalGS) cn true ackProto (confProto γ) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn true))
      $$ [Hlis]
    as %cv %err (⟨%Herr, %cn, #Hc, Hlis, Hend, -⟩ | ⟨%k, Hlis, #Herr⟩)
  · iframe Hlt Hla
    iapply accept_au addr (confProto γ) ackProto _ l true $$ Hpr Hlis
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
    wp_auto
    wp_for_post
    iframe
    iexists fst; iframe
  subst Herr
  unfold net.isConn
  icases Hc with ⟨%tc, %la, %ra, %Hct, #Hca⟩
  subst Hct
  iunfold connEnd at Hend
  icases Hend with ⟨Hs, Hrv⟩
  ihave #Hconn := sendTok_connIs cn true _ _ $$ Hs
  wp_auto
  ihave #Hrd := net.conn_readerOk wp_Read tc cn true addr la ra eof ed (confProto γ) $$ [$Hio $Hca $Heof $Hed]
  iunfold net.connIface at Hrd
  ihave Hrv := recvTok_L $$ Hrv
  ihave Hb := slice_array b_ptr 3 _ (by decide) $$ b
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 3 - W64 0) = W64 3 from rfl,
    show (zero_val (GoArray w8 3)).arr = [W8 0, W8 0, W8 0] from rfl]
  wp_apply io.wp_ReadFull ⟨go.GoType.PointerType net.TCPConn.ty, #tc⟩ (fun _ m => 0 < m)
      (recvTokL (Gg := hG.goose_globalGS) cn true (confProto γ)) (net.connReadE eof la ra ed) []
      (slice.mk b_ptr (W64 3) (W64 3)) [W8 0, W8 0, W8 0] eof ueof
      $$ [Hrv Hb] as %n2 %err2 ⟨%ys, %Hys, Hb, Hrv, #Hres⟩
  · iframe Hrd Heof Hue Hrv Hb; ipureintro; intro _ hl; simp only [List.length_cons, List.length_nil] at hl ⊢; omega
  iunfold io.readFullRes at Hres
  icases Hres with (%Hl | ⟨%e, %He, -⟩)
  rotate_left
  · have herr : err2 ≠ GoInterface.nil := by
      obtain ⟨-, hne, h1, h2⟩ := He
      by_cases hc : e = eof ∧ ys ≠ []
      · rw [h1 hc]; exact Hev.2
      · rw [h2 hc]; exact hne
    cases err2 with
    | nil => exact absurd rfl herr
    | ok i =>
    wp_auto
    wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
    · iframe Hca Hconn
    wp_for_post
    iframe
    iexists fst; iframe
  obtain ⟨hl, rfl⟩ := Hl
  obtain ⟨x1, y1, z1, rfl⟩ : ∃ x y z, ys = [x, y, z] := by
    match ys, hl with
    | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
  rw [show List.drop [x1, y1, z1].length [W8 0, W8 0, W8 0] = [] from rfl, List.append_nil]
  wp_auto_lc 1
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 3 - W64 0) = W64 3 from rfl]
  wp_apply wp_decode _ x1 y1 z1 _ $$ Hb as %cf %ok ⟨Hb, %Hok⟩
  cases ok
  · wp_auto
    wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
    · iframe Hca Hconn
    wp_for_post
    iframe
    iexists fst; iframe
  obtain ⟨hcf, -⟩ := Hok rfl
  rw [List.nil_append]
  ihave Hrv := recvTokL_later $$ Hrv
  iapply fupd_wp
  imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hrv with Hrv
  imodintro
  ihave ⟨-, Hpp⟩ := recvTok_proto $$ Hrv
  ihave #Hok := conf_learn γ cn x1 y1 z1 cf hcf $$ Hpp
  cases fst
  · wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 107]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    ihave #Hp0 : (□ ackProto (GF := GF) cn ([] ++ [W8 107])) $$ []
    · iintro !>; unfold ackProto; itrivial
    wp_apply wp_Write tc cn true addr la ra _ [W8 107] _ ed
        (writeP (Gg := hG.goose_globalGS) cn true ackProto []) $$ [Hs Hsl1]
      as %nw %werr ⟨%w, %res, Hs, Hsl1, -, -⟩
    · iframe Hca Hsl1 Hed
      isplitl [Hs]
      · iapply writeP_init $$ Hs
      · iapply write_acc cn true ackProto [] _ $$ Hp0
    wp_auto
    wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
    · iframe Hca Hconn
    wp_for_post
    iframe
    iexists false; iframe first; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]
    wp_auto
    wp_apply wp_future_fulfill (t := Conf.ty) γf ch cf $$ [$Hfut Hful]
    · unfold Fulfilled; iexists _; iframe; iexact Hok
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 107]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    ihave #Hp0 : (□ ackProto (GF := GF) cn ([] ++ [W8 107])) $$ []
    · iintro !>; unfold ackProto; itrivial
    wp_apply wp_Write tc cn true addr la ra _ [W8 107] _ ed
        (writeP (Gg := hG.goose_globalGS) cn true ackProto []) $$ [Hs Hsl1]
      as %nw %werr ⟨%w, %res, Hs, Hsl1, -, -⟩
    · iframe Hca Hsl1 Hed
      isplitl [Hs]
      · iapply writeP_init $$ Hs
      · iapply write_acc cn true ackProto [] _ $$ Hp0
    wp_auto
    wp_apply wp_closeConn wp_Close tc cn true addr la ra $$ [] as %e2 -
    · iframe Hca Hconn
    wp_for_post
    iframe
    iexists false; iframe first; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

/-- `waitConf(cfgs, m)`: machine `m`'s configuration (received at its configuration address
`cfgs[m]` by `awaitConf`, in a goroutine of its own, through a channel): an accepted one, whose
number of replicas is the system's (`confOk γ`). -/
abbrev waitConf.spec : Prop :=
  ∀ (γ : Names) (cfgs : GoSlice) (dq : DFrac) (m : w64), uint.nat m < 12 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ cfgs ↦*{dq} cfgAddrs ∗
      confProtos (G := hG.goose_globalGS) γ }}
    (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.waitConf)) (Val #cfgs))
      (Val #m))
  {{ (cf : Conf), RET #cf; cfgs ↦*{dq} cfgAddrs ∗ confOk (G := hG.goose_globalGS) γ cf }}

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
