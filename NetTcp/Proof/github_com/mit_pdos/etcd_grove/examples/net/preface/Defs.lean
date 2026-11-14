/-
The protocol of `examples/net/preface`, over the TCP extension's resources (`GooseLang/Ext/Tcp`)
and the shared per-address protocol (`wire/Addr.lean`). As echo's (`echo/Defs.lean`), with the
preface skipped:

* **Every connection** `cn` to `srvAddr` has a token name `γ` (`pfName γm cn γ`, persistent: the
  ghost map `γm`) and a reply state (`pfConn cn γ`): the acceptor's written bytes `so`
  (`tcpOut cn true so f`) are a prefix of what the dialer has written past its first
  `prefaceLen` (4) bytes (`si.drop 4`, of a lower bound `si`, `tcpOutLb cn false si`), or nothing
  while the server still holds the connection's token `γ` (`pfTok`, exclusive: the right to make
  the one write). All connections' states are in one invariant (`pfState γm`), so that every
  resource the protocol moves is timeless.
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`pf_deposit`, through `wire.dial_au`) and the server takes when it accepts `cn`
  (`wire.accept_au`): the acceptor end's state (`tcpEnd cn true fresh 0`), the token and its name.

The client's check (`client_check`): a reply it read is a prefix of the server's bytes, which are
a prefix of the client's own past its preface (whatever the preface was: the server's check of
`Magic` is not needed for this). The token makes the server's one write start from nothing
(`server_write_au`). Crashes change nothing here: the invariants are global, and a connection's
protocol stays in the address's invariant until a server (of any incarnation) accepts it.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask)

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7107"

def addrN : Namespace := nroot.@"preface_addr"
def pfN : Namespace := nroot.@"preface_conns"

section defs
variable {GF : BundledGFunctors}

/-- The token of a connection: the server's right to make its one write. -/
def pfTok (hT : TcpGS GF) (γ : GName) : IProp GF := @token GF hT.allG γ

instance pfTok_timeless (hT : TcpGS GF) (γ : GName) : Timeless (pfTok hT γ) := by
  unfold pfTok; letI := hT.allG; infer_instance

/-- The number of bytes of the preface, which the server's reply skips. -/
abbrev preLen : Nat := 4

/-- A prefix of `b` past its first `n` bytes is past the first `n` bytes of a prefix of `b`. -/
theorem drop_prefix {α : Type} {a b : List α} (h : a <+: b) (n : Nat) : a.drop n <+: b.drop n := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t.drop (n - a.length), List.drop_append.symm⟩

/-- The reply state of the connection `cn`, whose token is `γ`. -/
def pfConn (hT : TcpGS GF) (cn : Nat) (γ : GName) : IProp GF :=
  iprop(∃ (so : GoString) (f : Bool), tcpOut hT cn true so f ∗
    ((pfTok hT γ ∗ ∃ si, tcpOutLb hT cn false si ∗ ⌜so <+: si.drop preLen⌝) ∨ ⌜so = []⌝))

instance pfConn_timeless (hT : TcpGS GF) (cn : Nat) (γ : GName) :
    Timeless (pfConn hT cn γ) := by
  unfold pfConn; infer_instance

/-- Every connection's reply state, their token names in the ghost map `γm`. -/
def pfState (hT : TcpGS GF) (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat GName, @ghostMapAuth GF hT.allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ γ ∈ m, pfConn hT cn γ)

/-- The connection `cn`'s token name is `γ`. -/
def pfName (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) : IProp GF :=
  @ghostMapElem GF hT.allG _ _ _ _ γm cn .discard γ

instance pfName_persistent (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Persistent (pfName hT γm cn γ) := by
  unfold pfName; letI := hT.allG; infer_instance

instance pfName_timeless (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Timeless (pfName hT γm cn γ) := by
  unfold pfName; letI := hT.allG; infer_instance

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What the server gets when it accepts `cn`. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn true TcpEnd.fresh 0 ∗ pfTok G γ ∗ pfName G γm cn γ)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- The invariants of the protocol. -/
def pfInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv pfN (pfState G γm))

instance pfInvs_persistent (γm : GName) : Persistent (pfInvs (Gg := Gg) γm) := by
  unfold pfInvs; infer_instance

theorem pfInvs_elim (γm : GName) :
    pfInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv pfN (pfState G γm) := .rfl

theorem pfTok_exclusive (γ : GName) :
    pfTok (G (Gg := Gg)) γ -∗ pfTok G γ -∗ False := by
  unfold pfTok
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply token_exclusive $$ H1 H2

/-- A dialer's deposit for its new connection `cn`: a token, its name in the map, the
connection's reply state (nothing written yet), and the acceptor end's state for the server. -/
theorem pf_deposit (γm : GName) (cn : Nat) :
    ⊢ inv pfN (pfState (G (Gg := Gg)) γm) -∗ tcpConnAt G cn srvAddr -∗
      tcpFreshEnd G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ ∃ γ, pfName G γm cn γ := by
  iintro #Hinv #Hat Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "preface_conns" "preface_addr" (by decide)
  unfold pfState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFreshEnd
  icases Ha with ⟨Hae, Hao⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its acceptor's written bytes are owned once
    icases BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm) $$ Hconns with ⟨Hc, -⟩
    unfold pfConn
    icases Hc with ⟨%so, %f, Hout, -⟩
    icases tcpOut_excl _ cn true so [] f false $$ Hout Hao with ⟨⟩
  | none =>
    imod token_alloc (GF := GF) with ⟨%γ, Htok⟩
    imod ghost_map_insert_persist cn γ hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hao] with -
    · inext
      iexists m.insert cn γ
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold pfConn
      iexists [], false
      iframe Hao
      iright
      ipureintro; rfl
    imodintro
    unfold connProto pfName pfTok
    isplitl [Hae Htok]
    · iexists γ
      iframe Hae Htok Hname
    · iexists γ
      iexact Hname


/-- The reply state of a connection, from the invariant, by its token name: it and the update that
puts it back. -/
theorem pfState_acc (γm : GName) (cn : Nat) (γ : GName) (E : CoPset) (hE : ↑pfN ⊆ E) :
    ⊢ inv pfN (pfState (G (Gg := Gg)) γm) -∗ pfName G γm cn γ -∗
      |={E, E \ ↑pfN}=> pfConn G cn γ ∗ (pfConn G cn γ ={E \ ↑pfN, E}=∗ True) := by
  iintro #Hinv #Hname
  iinv Hinv with Hi Hclose
  unfold pfState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold pfName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases BigSepM.bigSepM_insert_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl) $$ Hconns with ⟨Hc, Hback⟩
  imodintro
  iframe Hc
  iintro Hc
  have hm : PartialMap.insert m cn γ = m := by
    show m.insert cn γ = m
    apply GMap.ext; intro k; simp only [GMap.lookup_insert_eq_iff]
    split <;> simp_all
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn γ, pfConn (G (Gg := Gg)) k v) ⊢
      [∗map] k ↦ v ∈ m, pfConn G k v := by rw [hm]
  imod Hclose $$ [Hm Hback Hc] with -
  · inext
    iexists m
    iframe Hm
    iapply hconv
    iapply Hback $$ Hc
  imodintro
  itrivial

/-- The server's one write on `cn`, of bytes `bs` that are a prefix of the dialer's (`si`) past
the preface, with the connection's token: the reply state's bytes were nothing, and are a prefix
of `si.drop preLen` after. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : GName) (bs si : GoString) (st : TcpEnd)
    (r : Nat) (hbs : bs <+: si.drop preLen) :
    ⊢ inv pfN (pfState (G (Gg := Gg)) γm) -∗ pfName G γm cn γ -∗ pfTok G γ -∗
      tcpOutLb G cn false si -∗ tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st0 r0 out f, tcpEnd G cn true st0 r0 ∗ tcpOut G cn true out f ∗
        ∀ k ok st', ⌜WriteRes st0 bs k ok st'⌝ -∗ tcpEnd G cn true st' r0 -∗
          tcpOut G cn true (out ++ bs.take k) f ={∅,⊤}=∗ ∃ st', tcpEnd G cn true st' r := by
  iintro #Hinv #Hname Htok #Hsi Hend
  imod pfState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold pfConn
  icases Hc with ⟨%so, %f, Hout, Hcase⟩
  icases Hcase with (⟨Htok', -⟩ | %Hso)
  · icases pfTok_exclusive γ $$ Htok Htok' with ⟨⟩
  subst Hso
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, [], f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  imod Hclose $$ [Hout Htok] with -
  · iexists [] ++ bs.take k, f
    iframe Hout
    ileft
    iframe Htok
    iexists si
    iframe Hsi
    ipureintro
    exact (List.take_prefix k bs).trans hbs
  imodintro
  iexists st'
  iexact Hend

/-- The server's close of `cn`: the reply state's bytes do not change. -/
theorem server_close_au (γm : GName) (cn : Nat) (γ : GName) (st : TcpEnd) (r : Nat) :
    ⊢ inv pfN (pfState (G (Gg := Gg)) γm) -∗ pfName G γm cn γ -∗ tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn true st r ∗ tcpOut G cn true out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn true st' r -∗ tcpOut G cn true out f' ={∅,⊤}=∗ True := by
  iintro #Hinv #Hname Hend
  imod pfState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold pfConn
  icases Hc with ⟨%so, %f, Hout, Hcase⟩
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, so, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr - Hout
  imod Hmask
  iapply Hclose
  iexists so, f'
  iframe Hout Hcase

/-- The client's check: a reply it read (`resp`, a prefix of the server's bytes) is a prefix of
the client's own bytes `out` past the preface. -/
theorem client_check (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp : GoString) :
    ⊢ inv pfN (pfState (G (Gg := Gg)) γm) -∗ pfName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp ={⊤}=∗
      ⌜resp <+: out.drop preLen⌝ ∗ tcpOut G cn false out f := by
  iintro #Hinv #Hname Hmy #Hresp
  imod pfState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold pfConn
  icases Hc with ⟨%so, %f', Hout, Hcase⟩
  icases tcpOut_lb_prefix _ cn true so f' resp $$ Hout Hresp with %Hrs
  icases Hcase with (⟨Htk, %si, #Hsi, %Hso⟩ | %Hso)
  · icases tcpOut_lb_prefix _ cn false out f si $$ Hmy Hsi with %Hsio
    imod Hclose $$ [Hout Htk] with -
    · iexists so, f'
      iframe Hout
      ileft
      iframe Htk
      iexists si
      iframe Hsi
      ipureintro; exact Hso
    imodintro
    iframe Hmy
    ipureintro; exact Hrs.trans (Hso.trans (drop_prefix Hsio preLen))
  · subst Hso
    imod Hclose $$ [Hout] with -
    · iexists [], f'
      iframe Hout
      iright
      ipureintro; rfl
    imodintro
    iframe Hmy
    ipureintro
    rw [List.prefix_nil.1 Hrs]
    exact List.nil_prefix

/-- A deadline set (or cleared) by an end its thread owns: the update of `net.Conn.SetDeadline`,
which hands back the end's state, whatever its outcome. -/
theorem owned_setDeadline_au (c : Nat) (s : Bool) (st : TcpEnd) (r : Nat) :
    ⊢ tcpEnd (G (Gg := Gg)) c s st r -∗
      |={⊤,∅}=> ∃ st0 r0, tcpEnd G c s st0 r0 ∗
        ∀ ok st', ⌜(st0.closed = true ∧ ok = false ∧ st' = st0) ∨
            (st0.closed = false ∧ ok = true ∧ st' = { st0 with dl := true })⌝ -∗
          tcpEnd G c s st' r0 ={∅,⊤}=∗ ∃ st'', tcpEnd G c s st'' r := by
  iintro Hend
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r
  iframe Hend
  iintro %ok %st' - Hend
  imod Hmask
  imodintro
  iexists st'
  iexact Hend

end wps

end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial
