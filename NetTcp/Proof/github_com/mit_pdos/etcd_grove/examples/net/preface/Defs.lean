/-
The protocol of `examples/net/preface`, over the TCP extension's resources (`GooseLang/Ext/Tcp`),
the shared per-address protocol (`wire/Addr.lean`) and the per-direction stream protocol
(`wire/Stream.lean`). As echo's, with the preface skipped:

* **Every connection** `cn` to `srvAddr` has ghost names `ν` (`pfName γm cn ν`, persistent: the
  ghost map `γm`): the server's token `ν.tok` (exclusive: the right to make the one write), and the
  stream protocols of its two directions, `ν.up` (from the dialer, false) and `ν.down` (from the
  acceptor, true). All connections' state is in one invariant (`pfState γm`), so that every
  resource the protocol moves is timeless: for each connection, both directions' `dirInv`s (the
  semantics' unread bytes tied to what was written and read) and its reply state (`pfReply ν`):
  the server's written bytes `W` on the down direction (the writer's half, `sentAll ν.down W`,
  kept here so the client can bound them) are nothing, or, once the server made its write (its
  token deposited here), a prefix of what the dialer had written past its first `preLen` (4) bytes
  (`si.drop 4`, of a lower bound `si`, `sentLb ν.up si`). `pf_dirInv` derives each direction's own
  invariant (`inv pfN (dirInv ..)`, `inv_alter`) for `Stream.lean`'s updates.
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`pf_dial_au`: the dial's update, which gets both ends' fresh resources) and the server
  takes when it accepts `cn` (`wire.accept_lis_au`): the acceptor end's state, the token, the
  reader's half of the up direction, and the names. The dialer keeps its end's state, the writer's
  half of the up direction and the reader's half of the down direction (`clientRes`).

The client's check (`client_check`): a reply it read is a prefix of the server's bytes (`sentLb`
from its read), which are a prefix of the client's own past its preface (its `sentAll ν.up`). The
token makes the server's one write start from nothing (`server_write_au`). Crashes change nothing
here: the invariants are global, and a connection's protocol stays in the address's invariant
until a server (of any incarnation) accepts it.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask DirNames dirInv
  sentAll sentLb rcvdAll DirOk)

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7107"

def addrN : Namespace := nroot.@"preface_addr"
def pfN : Namespace := nroot.@"preface_conns"

/-- The number of bytes of the preface, which the server's reply skips. -/
abbrev preLen : Nat := 4

/-- A prefix of `b` past its first `n` bytes is past the first `n` bytes of a prefix of `b`. -/
theorem drop_prefix {α : Type} {a b : List α} (h : a <+: b) (n : Nat) : a.drop n <+: b.drop n := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t.drop (n - a.length), List.drop_append.symm⟩

/-- The ghost names of a connection: the server's token, and the stream protocols of the
direction from the dialer (`up`) and from the acceptor (`down`). -/
structure PfNames where
  tok : GName
  up : DirNames
  down : DirNames

def PfNames.enc (ν : PfNames) := (ν.tok, ν.up.w, ν.up.r, ν.down.w, ν.down.r)

instance PfNames.countable : Pos.Countable PfNames :=
  .ofInjective (fun ν => Pos.Countable.encode ν.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    obtain ⟨t, ⟨uw, ur⟩, ⟨dw, dr⟩⟩ := a
    obtain ⟨t', ⟨uw', ur'⟩, ⟨dw', dr'⟩⟩ := b
    simp only [PfNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The token of a connection: the server's right to make its one write. -/
def pfTok (γ : GName) : IProp GF := @token GF (G (Gg := Gg)).allG γ

instance pfTok_timeless (γ : GName) : Timeless (pfTok (Gg := Gg) γ) := by
  unfold pfTok; letI := (G (Gg := Gg)).allG; infer_instance

theorem pfTok_exclusive (γ : GName) : pfTok (Gg := Gg) γ -∗ pfTok γ -∗ False := by
  unfold pfTok
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply token_exclusive $$ H1 H2

/-- The reply state of the connection with names `ν`: the server's written bytes `W` (the
writer's half of the down direction), nothing, or, with the token, a prefix of the dialer's bytes
past the preface. -/
def pfReply (ν : PfNames) : IProp GF :=
  iprop(∃ W, sentAll (Gg := Gg) ν.down W ∗
    ((pfTok ν.tok ∗ ∃ si, sentLb ν.up si ∗ ⌜W <+: si.drop preLen⌝) ∨ ⌜W = []⌝))

instance pfReply_timeless (ν : PfNames) : Timeless (pfReply (Gg := Gg) ν) := by
  unfold pfReply; infer_instance

/-- The state of the connection `cn` with names `ν`: its directions' protocols and its reply
state. -/
def pfConn (cn : Nat) (ν : PfNames) : IProp GF :=
  iprop(dirInv (Gg := Gg) cn false ν.up ∗ dirInv (Gg := Gg) cn true ν.down ∗ pfReply ν)

instance pfConn_timeless (cn : Nat) (ν : PfNames) : Timeless (pfConn (Gg := Gg) cn ν) := by
  unfold pfConn; infer_instance

/-- Every connection's state, their names in the ghost map `γm`. -/
def pfState (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat PfNames, @ghostMapAuth GF (G (Gg := Gg)).allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ ν ∈ m, pfConn cn ν)

instance pfState_timeless (γm : GName) : Timeless (pfState (Gg := Gg) γm) := by
  unfold pfState; letI := (G (Gg := Gg)).allG; infer_instance

/-- The connection `cn`'s names are `ν`. -/
def pfName (γm : GName) (cn : Nat) (ν : PfNames) : IProp GF :=
  @ghostMapElem GF (G (Gg := Gg)).allG _ _ _ _ γm cn .discard ν

instance pfName_persistent (γm : GName) (cn : Nat) (ν : PfNames) :
    Persistent (pfName (Gg := Gg) γm cn ν) := by
  unfold pfName; letI := (G (Gg := Gg)).allG; infer_instance

instance pfName_timeless (γm : GName) (cn : Nat) (ν : PfNames) :
    Timeless (pfName (Gg := Gg) γm cn ν) := by
  unfold pfName; letI := (G (Gg := Gg)).allG; infer_instance

/-- What the server gets when it accepts `cn`: its end's state, the token, the reader's half of
the up direction (nothing read) and its lower bound, and the names. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ ν, tcpEnd G cn true TcpEnd.fresh ∗ pfTok (Gg := Gg) ν.tok ∗ rcvdAll ν.up [] ∗
    sentLb ν.up [] ∗ pfName γm cn ν)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`: its end's state, the writer's half of the up
direction, the reader's half of the down direction (and its lower bound), and the names. -/
def clientRes (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ ν, tcpEnd G cn false TcpEnd.fresh ∗ sentAll (Gg := Gg) ν.up [] ∗ rcvdAll ν.down [] ∗
    sentLb ν.down [] ∗ pfName γm cn ν)

/-- The invariants of the protocol. -/
def pfInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv pfN (pfState (Gg := Gg) γm))

instance pfInvs_persistent (γm : GName) : Persistent (pfInvs (Gg := Gg) γm) := by
  unfold pfInvs; infer_instance

theorem pfInvs_elim (γm : GName) :
    pfInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv pfN (pfState (Gg := Gg) γm) := .rfl

/-- A direction's stream protocol, from its fresh resource, without its invariant (a candidate
for `Stream.lean`, as `dirInv_alloc`'s first half). -/
theorem dirGhost_alloc (c : Nat) (s : Bool) :
    tcpDir (G (Gg := Gg)) c s TcpDir.fresh ==∗ ∃ γ, dirInv c s γ ∗ sentAll γ [] ∗
      rcvdAll γ [] := by
  letI := (G (Gg := Gg)).allG
  iintro Hd
  imod mono_list_own_alloc (GF := GF) ([] : List w8) with ⟨%γw, Hw, -⟩
  icases (show monoListAuthOwn (GF := GF) γw 1 ([] : List w8) ⊣⊢
      iprop(monoListAuthOwn γw (1 : Qp).half [] ∗ monoListAuthOwn γw (1 : Qp).half []) by
    conv => lhs; rw [← Qp.half_add_half 1]
    exact (monoListAuthOwn_fractional γw []).fractional _ _).mp $$ Hw with ⟨Hw1, Hw2⟩
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γr, Hr⟩
  icases (ghostVar_split_half γr 1 ([] : List w8)).mp $$ Hr with ⟨Hr1, Hr2⟩
  imodintro
  iexists ⟨γw, γr⟩
  unfold dirInv sentAll rcvdAll
  isplitl [Hd Hw1 Hr1]
  · iexists TcpDir.fresh, [], []
    iframe Hd Hw1 Hr1
    ipureintro; exact wire.dirOk_fresh
  · iframe Hw2 Hr2

/-- A connection's state, from the map's: it and the wand that puts it back. -/
theorem pfConns_acc (m : GMap Nat PfNames) (cn : Nat) (ν : PfNames) (Hl : m.lookup cn = some ν) :
    ([∗map] k ↦ v ∈ m, pfConn (Gg := Gg) k v) ⊢
      pfConn cn ν ∗ (pfConn cn ν -∗ [∗map] k ↦ v ∈ m, pfConn (Gg := Gg) k v) := by
  iintro Hconns
  icases BigSepM.bigSepM_insert_acc (show PartialMap.get? m cn = some ν by
    rw [gmap_get?_eq]; exact Hl) $$ Hconns with ⟨Hc, Hback⟩
  iframe Hc
  iintro Hc
  have hm : PartialMap.insert m cn ν = m := by
    show m.insert cn ν = m
    apply GMap.ext; intro k; simp only [GMap.lookup_insert_eq_iff]
    split <;> simp_all
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn ν, pfConn (Gg := Gg) k v) ⊢
      [∗map] k ↦ v ∈ m, pfConn (Gg := Gg) k v := by rw [hm]
  iapply hconv
  iapply Hback $$ Hc

/-- A connection's state, from the invariant's: it and the wand that puts it back. -/
theorem pfState_acc (γm : GName) (cn : Nat) (ν : PfNames) :
    pfName (Gg := Gg) γm cn ν ⊢ pfState γm -∗ pfConn cn ν ∗ (pfConn cn ν -∗ pfState γm) := by
  letI := (G (Gg := Gg)).allG
  iintro #Hname Hi
  unfold pfState
  icases Hi with ⟨%m, Hm, Hconns⟩
  unfold pfName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases pfConns_acc m cn ν Hl $$ Hconns with ⟨Hc, Hback⟩
  iframe Hc
  iintro Hc
  iexists m
  iframe Hm
  iapply Hback $$ Hc

/-- Each direction's own invariant, from the protocol's (`inv_alter`), for `Stream.lean`'s
updates. -/
theorem pf_dirInv (γm : GName) (cn : Nat) (ν : PfNames) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ pfName γm cn ν -∗
      inv pfN (dirInv cn false ν.up) ∗ inv pfN (dirInv cn true ν.down) := by
  iintro #Hinv #Hname
  isplitl []
  · iapply inv_alter pfN _ _ $$ Hinv
    inext; imodintro
    iintro Hi
    icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
    unfold pfConn
    icases Hc with ⟨Hup, Hdown, Hrep⟩
    iframe Hup
    iintro Hup
    iapply Hback
    iframe Hup Hdown Hrep
  · iapply inv_alter pfN _ _ $$ Hinv
    inext; imodintro
    iintro Hi
    icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
    unfold pfConn
    icases Hc with ⟨Hup, Hdown, Hrep⟩
    iframe Hdown
    iintro Hdown
    iapply Hback
    iframe Hup Hdown Hrep

/-- A dialer's deposit for its new connection `cn`, from both ends' fresh resources: new names,
both directions' protocols and the reply state (nothing written yet) in the invariant; the
server's part (`connProto`) and the dialer's (`clientRes`). -/
theorem pf_deposit (γm : GName) (cn : Nat) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ tcpFresh G cn false -∗ tcpFresh G cn true
      ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ clientRes γm cn := by
  iintro #Hinv Hd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "preface_conns" "preface_addr" (by decide)
  unfold pfState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFresh
  icases Hd with ⟨Hde, Hdd⟩
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some ν' =>
    -- `cn` is new: the direction from its dialer is owned once
    icases pfConns_acc m cn ν' hm $$ Hconns with ⟨Hc, -⟩
    unfold pfConn dirInv
    icases Hc with ⟨⟨%d, %W, %R, Hd', -⟩, -⟩
    icases tcpDir_excl _ cn false d TcpDir.fresh $$ Hd' Hdd with ⟨⟩
  | none =>
    imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
    imod dirGhost_alloc cn false $$ Hdd with ⟨%γu, Hup, Hwu, Hru⟩
    imod dirGhost_alloc cn true $$ Had with ⟨%γd, Hdown, Hwd, Hrd⟩
    ihave #Hlbu := wire.sentLb_get γu [] $$ Hwu
    ihave #Hlbd := wire.sentLb_get γd [] $$ Hwd
    imod ghost_map_insert_persist cn (⟨γt, γu, γd⟩ : PfNames) hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hup Hdown Hwd] with -
    · inext
      iexists m.insert cn ⟨γt, γu, γd⟩
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold pfConn pfReply
      iframe Hup Hdown
      iexists []
      iframe Hwd
      iright
      ipureintro; rfl
    imodintro
    unfold connProto clientRes pfName pfTok
    isplitl [Hae Htok Hru]
    · iexists ⟨γt, γu, γd⟩
      iframe Hae Htok Hru Hlbu Hname
    · iexists ⟨γt, γu, γd⟩
      iframe Hde Hwu Hrd Hlbd Hname

/-- A dial of `srvAddr`: the update of `net.Dial`, which deposits the connection's protocol in
the address's invariant (as `wire.dial_au`, but the deposit is made from both ends' fresh
resources, since it allocates both directions' protocols: a candidate for `Addr.lean`). -/
theorem pf_dial_au (γm : GName) :
    ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) -∗ inv pfN (pfState (Gg := Gg) γm) -∗
      |={⊤,∅}=> ∃ S, tcpPend G srvAddr S ∗
        ∀ cn, ⌜cn ∉ S⌝ -∗ tcpPend G srvAddr (S ∪ {[cn]}) -∗ tcpConnAt G cn srvAddr -∗
          tcpFresh G cn false -∗ tcpFresh G cn true ={∅,⊤}=∗ clientRes γm cn := by
  iintro #HaddrInv #HpfInv
  iinv HaddrInv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨%S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend #Hat Hd Ha
  imod Hmask
  imod pf_deposit γm cn $$ HpfInv Hd Ha with ⟨HΦ, HR⟩
  imod Hclose $$ [Hpend Hdeps HΦ] with -
  · inext
    iexists S ∪ {[cn]}
    iframe Hpend
    rw [wire.setMap_insert]
    iapply (BigSepM.bigSepM_insert (wire.setMap_lookup_none HcS)).2
    iframe Hdeps HΦ
  imodintro
  iexact HR

/-- The server's one write on `cn`, of bytes `bs` that are a prefix of the dialer's (`si`) past
the preface, with the connection's token: the reply state's bytes were nothing, and are a prefix
of `si.drop preLen` after. -/
theorem server_write_au (γm : GName) (cn : Nat) (ν : PfNames) (bs si : List w8) (st : TcpEnd)
    (hbs : bs <+: si.drop preLen) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ pfName γm cn ν -∗ pfTok ν.tok -∗ sentLb ν.up si -∗
      tcpEnd G cn true st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G cn true st0 ∗ tcpDir G cn true d ∗
        ∀ k ok d', ⌜WriteOutcome st0 d bs k ok d'⌝ -∗ tcpEnd G cn true st0 -∗
          tcpDir G cn true d' ={∅,⊤}=∗ tcpEnd G cn true st := by
  iintro #Hinv #Hname Htok #Hsi Hend
  iinv Hinv with Hi Hclose
  icases Hi with >Hi
  icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
  unfold pfConn
  icases Hc with ⟨Hup, Hdown, Hrep⟩
  unfold pfReply
  icases Hrep with ⟨%W, Hw, Hcase⟩
  icases Hcase with (⟨Htok', -⟩ | %HW)
  · icases pfTok_exclusive ν.tok $$ Htok Htok' with ⟨⟩
  subst HW
  unfold dirInv
  icases Hdown with ⟨%d, %W', %R, Hd, Hw', Hr, %Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %ok %d' %Hwr Hend Hd
  imod Hmask
  imod wire.sentAll_app ν.down W' [] (bs.take k) $$ Hw' Hw with ⟨%Heq, Hw', Hw⟩
  subst Heq
  imod Hclose $$ [Hback Hup Hd Hw' Hr Hw Htok] with -
  · inext
    iapply Hback
    iframe Hup
    isplitl [Hd Hw' Hr]
    · iexists d', [] ++ bs.take k, R
      iframe Hd Hw' Hr
      ipureintro; exact wire.dirOk_write Hok Hwr
    · iexists [] ++ bs.take k
      iframe Hw
      ileft
      iframe Htok
      iexists si
      iframe Hsi
      ipureintro
      exact (List.take_prefix k bs).trans hbs
  imodintro
  iexact Hend

/-- The client's check: a reply it read (`resp`, a lower bound of the server's bytes) is a prefix
of the client's own bytes `W` past the preface. -/
theorem client_check (γm : GName) (cn : Nat) (ν : PfNames) (W resp : List w8) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ pfName γm cn ν -∗ sentAll ν.up W -∗ sentLb ν.down resp
      ={⊤}=∗ ⌜resp <+: W.drop preLen⌝ ∗ sentAll ν.up W := by
  iintro #Hinv #Hname Hmy #Hresp
  iinv Hinv with Hi Hclose
  icases Hi with >Hi
  icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
  unfold pfConn
  icases Hc with ⟨Hup, Hdown, Hrep⟩
  unfold pfReply
  icases Hrep with ⟨%Wd, Hwd, Hcase⟩
  icases wire.sentLb_prefix ν.down Wd resp $$ Hwd Hresp with %Hrs
  icases Hcase with (⟨Htk, %si, #Hsi, %Hso⟩ | %Hso)
  · icases wire.sentLb_prefix ν.up W si $$ Hmy Hsi with %Hsio
    imod Hclose $$ [Hback Hup Hdown Hwd Htk] with -
    · inext
      iapply Hback
      iframe Hup Hdown
      iexists Wd
      iframe Hwd
      ileft
      iframe Htk
      iexists si
      iframe Hsi
      ipureintro; exact Hso
    imodintro
    iframe Hmy
    ipureintro; exact Hrs.trans (Hso.trans (drop_prefix Hsio preLen))
  · subst Hso
    imod Hclose $$ [Hback Hup Hdown Hwd] with -
    · inext
      iapply Hback
      iframe Hup Hdown
      iexists []
      iframe Hwd
      iright
      ipureintro; rfl
    imodintro
    iframe Hmy
    ipureintro
    rw [List.prefix_nil.1 Hrs]
    exact List.nil_prefix

/-- A close of an end its thread owns, whose direction follows the stream protocol, its result
dropped (`wire.close_au`, forgotten). -/
theorem close_drop_au (N : Namespace) (c : Nat) (s : Bool) (γ : DirNames) (st : TcpEnd) :
    ⊢ inv N (dirInv (Gg := Gg) c s γ) -∗ tcpEnd G c s st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c s d ∗
        ∀ ok st' d', ⌜CloseOutcome st0 d ok st' d'⌝ -∗ tcpEnd G c s st' -∗ tcpDir G c s d'
          ={∅,⊤}=∗ True := by
  iintro #Hinv Hend
  imod wire.close_au N c s γ st $$ Hinv Hend with ⟨%st0, %d, Hend, Hd, Hk⟩
  imodintro
  iexists st0, d
  iframe Hend Hd
  iintro %ok %st' %d' %Hc Hend Hd
  imod Hk $$ %ok %st' %d' %Hc Hend Hd with -
  imodintro
  itrivial

/-- A deadline set (or cleared) by an end its thread owns: the update of `net.Conn.SetDeadline`,
which hands back the end's state, whatever its outcome. -/
theorem owned_setDeadline_au (c : Nat) (s : Bool) (st : TcpEnd) (kind : w64) (set : Bool) :
    ⊢ tcpEnd (G (Gg := Gg)) c s st -∗
      |={⊤,∅}=> ∃ st0, tcpEnd G c s st0 ∗
        ∀ ok st', ⌜DeadlineOutcome st0 kind set ok st'⌝ -∗
          tcpEnd G c s st' ={∅,⊤}=∗ ∃ st'', tcpEnd G c s st'' := by
  iintro Hend
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st
  iframe Hend
  iintro %ok %st' - Hend
  imod Hmask
  imodintro
  iexists st'
  iexact Hend

end wps

end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial
