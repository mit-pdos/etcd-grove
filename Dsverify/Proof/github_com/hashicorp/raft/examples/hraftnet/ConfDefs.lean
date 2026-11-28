/-
The hraft kit's configuration protocol (`kit.go`'s `configure`, `sendConf`, `awaitConf`; notes/dsv-hraft.md,
S5d), as vr's (`vsrnet/ConfDefs.lean`): the orchestrator sends the first configuration's size `n0`, one
byte, to every server machine's configuration address (`confAddrs`); a server answers with one byte.

* `confProto γc`: what the orchestrator writes to a configuration address is a prefix of the one byte
  `n` it drew (3 or 5), drawn for good (`chosen γc n`, `Choice.lean`): it writes only after it drew,
  and only its one draw.
* `ackProto`: the answers mean nothing.
* `confOk γc n0`: what a server learns, `n0` the drawn size.

And the helpers of the connections' proofs (vr's): `errs_init`, `wp_closeConn`.
-/
module

public import Net.Proof.net.AtAddr
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Addrs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Choice
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

namespace github_com.hashicorp.raft.examples.hraftnet

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The configuration's wire -/

/-- A size the orchestrator draws (`chooseN0`). -/
def N0Ok (n : Nat) : Prop := n = 3 ∨ n = 5

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The protocol of what the orchestrator writes to a configuration address: a prefix of the byte of
the size it drew for good. -/
def confProto (γc : GName) : Proto GF :=
  fun _cid W => iprop(∃ n : Nat, ⌜W <+: [W8 (n : Int)] ∧ N0Ok n⌝ ∗ chosen γc n)

/-- The protocol of a configuration address's answers (one byte; it means nothing). -/
def ackProto : Proto GF := fun _cid _W => iprop(True)

/-- Every configuration address's protocols (persistent; the start sets them). -/
def confProtos (γc : GName) : IProp GF :=
  iprop([∗list] a ∈ confAddrs, addrProto a (confProto γc) ackProto)

instance confProtos_persistent (γc : GName) : Persistent (confProtos (GF := GF) γc) := by
  unfold confProtos; infer_instance

/-- What a server learns: the drawn size. -/
def confOk (γc : GName) (n0 : w64) : IProp GF :=
  iprop(∃ n : Nat, ⌜n0 = W64 (n : Int) ∧ N0Ok n⌝ ∗ chosen γc n)

instance confOk_persistent (γc : GName) (n0 : w64) : Persistent (confOk (GF := GF) γc n0) := by
  unfold confOk; infer_instance

/-- The byte read from a configuration address is the drawn size. -/
theorem conf_learn (γc : GName) (cid : Nat) (x : w8) :
    protoPrefix (confProto (GF := GF) γc) cid [x] ⊢ confOk γc (W64 (uint.Z x)) := by
  iintro Hpp
  unfold protoPrefix
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #Hp⟩)
  · cases Hnil
  unfold confProto
  icases Hp with ⟨%n, %Hw, #Hf⟩
  obtain ⟨hpre, hok⟩ := Hw
  have he : [x] = [W8 (n : Int)] := (Hext.trans hpre).eq_of_length (by simp)
  simp only [List.cons.injEq, and_true] at he
  subst he
  unfold confOk
  iexists n
  iframe Hf
  ipureintro
  refine ⟨?_, hok⟩
  have : n < 256 := by unfold N0Ok at hok; omega
  word

end defs

theorem dec_val_false' [GooseExts] [GoGlobalContext] : decide ((#false : val) = #true) = false := by
  simp only [decide_eq_false_iff_not]
  intro h
  have := GoGlobalContext.intoVal_inj_bool h
  simp at this

/-! ## The connections' helpers -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.hashicorp.raft.examples.hraftnet

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

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
