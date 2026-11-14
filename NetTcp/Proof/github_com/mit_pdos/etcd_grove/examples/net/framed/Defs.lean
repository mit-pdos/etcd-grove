/-
The protocol of `examples/net/framed`, over the TCP extension's resources (`GooseLang/Ext/Tcp`) and
the shared per-address protocol (`wire/Addr.lean`):

* **Every connection** `cn` to `srvAddr` has a ghost-variable name `γ` (`framedName γm cn γ`,
  persistent: the ghost map `γm`) and a framed state (`framedConn cn γ`): the acceptor's written
  bytes `so` (`tcpOut cn true so f`) are a prefix of what the dialer has written (a lower bound
  `si`, `tcpOutLb cn false si`), and the ghost variable `γ` holds `so` (half here, half with the
  thread serving the connection, `srvView`, so that the server knows what it has written). All
  connections' states are in one invariant (`framedState γm`), so that every resource the protocol
  moves is timeless.
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`framed_deposit`, through `wire.dial_au`) and the server takes when it accepts `cn`
  (`wire.accept_au`): the acceptor end's state (`tcpEnd cn true fresh 0`), the server's half of the
  ghost variable (nothing written) and its name.

The server writes back only bytes it has read: a write of `bs` after `so`, with `so ++ bs` a prefix
of the dialer's bytes (`server_write_au`), keeps the acceptor's bytes a prefix of the dialer's,
whatever part of `bs` it writes. The client's check (`client_check`): a reply it read is a prefix of
the server's bytes, which are a prefix of the client's own. Crashes change nothing here: the
invariants are global, and a connection's protocol stays in the address's invariant until a server
(of any incarnation) accepts it; a server that crashes while serving a connection leaves its state
in the invariant, and no one writes on that end again.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask)

namespace github_com.mit_pdos.etcd_grove.examples.net.framed

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7102"

def addrN : Namespace := nroot.@"framed_addr"
def framedN : Namespace := nroot.@"framed_conns"

section defs
variable {GF : BundledGFunctors}

/-- Half of the ghost variable `γ`: the acceptor of its connection has written `so`. -/
def srvView (hT : TcpGS GF) (γ : GName) (so : GoString) : IProp GF :=
  @ghostVar GF hT.allG GoString _ γ (1 : Qp).half so

instance srvView_timeless (hT : TcpGS GF) (γ : GName) (so : GoString) :
    Timeless (srvView hT γ so) := by
  unfold srvView; letI := hT.allG; infer_instance

/-- The framed state of the connection `cn`, whose ghost variable is `γ`. -/
def framedConn (hT : TcpGS GF) (cn : Nat) (γ : GName) : IProp GF :=
  iprop(∃ (so : GoString) (f : Bool) (si : GoString), tcpOut hT cn true so f ∗ srvView hT γ so ∗
    tcpOutLb hT cn false si ∗ ⌜so <+: si⌝)

instance framedConn_timeless (hT : TcpGS GF) (cn : Nat) (γ : GName) :
    Timeless (framedConn hT cn γ) := by
  unfold framedConn; infer_instance

/-- Every connection's framed state, their ghost variables' names in the ghost map `γm`. -/
def framedState (hT : TcpGS GF) (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat GName, @ghostMapAuth GF hT.allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ γ ∈ m, framedConn hT cn γ)

/-- The connection `cn`'s ghost variable is `γ`. -/
def framedName (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) : IProp GF :=
  @ghostMapElem GF hT.allG _ _ _ _ γm cn .discard γ

instance framedName_persistent (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Persistent (framedName hT γm cn γ) := by
  unfold framedName; letI := hT.allG; infer_instance

instance framedName_timeless (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Timeless (framedName hT γm cn γ) := by
  unfold framedName; letI := hT.allG; infer_instance

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What the server gets when it accepts `cn`. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn true TcpEnd.fresh 0 ∗ srvView G γ [] ∗ framedName G γm cn γ)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- The invariants of the protocol. -/
def framedInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv framedN (framedState G γm))

instance framedInvs_persistent (γm : GName) : Persistent (framedInvs (Gg := Gg) γm) := by
  unfold framedInvs; infer_instance

theorem framedInvs_elim (γm : GName) :
    framedInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv framedN (framedState G γm) := .rfl

/-- A dialer's deposit for its new connection `cn`: a ghost variable (nothing written), its name in
the map, the connection's framed state, and the acceptor end's state and the ghost variable's other
half for the server. -/
theorem framed_deposit (γm : GName) (cn : Nat) :
    ⊢ inv framedN (framedState (G (Gg := Gg)) γm) -∗ tcpConnAt G cn srvAddr -∗
      tcpFreshEnd G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ ∃ γ, framedName G γm cn γ := by
  iintro #Hinv #Hat Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "framed_conns" "framed_addr" (by decide)
  unfold framedState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFreshEnd
  icases Ha with ⟨Hae, Hao⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its acceptor's written bytes are owned once
    icases BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm) $$ Hconns with ⟨Hc, -⟩
    unfold framedConn
    icases Hc with ⟨%so, %f, %si, Hout, -⟩
    icases tcpOut_excl _ cn true so [] f false $$ Hout Hao with ⟨⟩
  | none =>
    imod ghostVar_alloc (GF := GF) ([] : GoString) with ⟨%γ, Hv⟩
    icases (ghostVar_split_half (GF := GF) γ 1 ([] : GoString)).1 $$ Hv with ⟨Hv1, Hv2⟩
    imod tcpOutLb_nil (G (Gg := Gg)) cn false srvAddr $$ Hat with #Hlb0
    imod ghost_map_insert_persist cn γ hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hao Hv1] with -
    · inext
      iexists m.insert cn γ
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold framedConn srvView
      iexists [], false, []
      iframe Hao Hv1 Hlb0
      ipureintro; exact List.prefix_refl _
    imodintro
    unfold connProto framedName srvView
    isplitl [Hae Hv2]
    · iexists γ
      iframe Hae Hv2 Hname
    · iexists γ
      iexact Hname

/-- The framed state of a connection, from the invariant, by its ghost variable's name: it and the
update that puts it back. -/
theorem framedState_acc (γm : GName) (cn : Nat) (γ : GName) (E : CoPset) (hE : ↑framedN ⊆ E) :
    ⊢ inv framedN (framedState (G (Gg := Gg)) γm) -∗ framedName G γm cn γ -∗
      |={E, E \ ↑framedN}=> framedConn G cn γ ∗ (framedConn G cn γ ={E \ ↑framedN, E}=∗ True) := by
  iintro #Hinv #Hname
  iinv Hinv with Hi Hclose
  unfold framedState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold framedName
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
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn γ, framedConn (G (Gg := Gg)) k v) ⊢
      [∗map] k ↦ v ∈ m, framedConn G k v := by rw [hm]
  imod Hclose $$ [Hm Hback Hc] with -
  · inext
    iexists m
    iframe Hm
    iapply hconv
    iapply Hback $$ Hc
  imodintro
  itrivial

/-- A write by the server on `cn` of bytes `bs` after the `so` it has written, with `so ++ bs` a
prefix of the dialer's bytes (`si`): whatever part of `bs` the write writes, the acceptor's bytes
stay a prefix of the dialer's, and the server's view follows them. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : GName) (so bs si : GoString) (st : TcpEnd)
    (r : Nat) (hbs : so ++ bs <+: si) :
    ⊢ inv framedN (framedState (G (Gg := Gg)) γm) -∗ framedName G γm cn γ -∗ srvView G γ so -∗
      tcpOutLb G cn false si -∗ tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st0 r0 out f, tcpEnd G cn true st0 r0 ∗ tcpOut G cn true out f ∗
        ∀ k ok st', ⌜WriteRes st0 bs k ok st'⌝ -∗ tcpEnd G cn true st' r0 -∗
          tcpOut G cn true (out ++ bs.take k) f ={∅,⊤}=∗
          ∃ st'', ⌜WriteRes st bs k ok st''⌝ ∗ tcpEnd G cn true st'' r ∗
            srvView G γ (so ++ bs.take k) := by
  iintro #Hinv #Hname Hv #Hsi Hend
  imod framedState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold framedConn
  icases Hc with ⟨%so', %f, %si', Hout, Hv', -⟩
  letI := (G (Gg := Gg)).allG
  unfold srvView
  icases ghostVar_agree γ so _ so' _ $$ Hv Hv' with %Hso
  subst Hso
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, so, f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  imod ghostVar_update_halves (so ++ bs.take k) γ so so $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hout Hv'] with -
  · iexists so ++ bs.take k, f, si
    iframe Hout Hv' Hsi
    ipureintro
    exact ((List.prefix_append_right_inj so).2 (List.take_prefix k bs)).trans hbs
  imodintro
  iexists st'
  iframe Hend Hv
  ipureintro; exact Hwr

/-- The server's close of `cn`: the framed state's bytes do not change. -/
theorem server_close_au (γm : GName) (cn : Nat) (γ : GName) (st : TcpEnd) (r : Nat) :
    ⊢ inv framedN (framedState (G (Gg := Gg)) γm) -∗ framedName G γm cn γ -∗
      tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn true st r ∗ tcpOut G cn true out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn true st' r -∗ tcpOut G cn true out f' ={∅,⊤}=∗ True := by
  iintro #Hinv #Hname Hend
  imod framedState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold framedConn
  icases Hc with ⟨%so, %f, %si, Hout, Hrest⟩
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, so, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr - Hout
  imod Hmask
  iapply Hclose
  iexists so, f', si
  iframe Hout Hrest

/-- The client's check: a reply it read (`resp`, a prefix of the server's bytes) is a prefix of
the client's own bytes `out`. -/
theorem client_check (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp : GoString) :
    ⊢ inv framedN (framedState (G (Gg := Gg)) γm) -∗ framedName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp ={⊤}=∗
      ⌜resp <+: out⌝ ∗ tcpOut G cn false out f := by
  iintro #Hinv #Hname Hmy #Hresp
  imod framedState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold framedConn
  icases Hc with ⟨%so, %f', %si, Hout, Hv, #Hsi, %Hso⟩
  icases tcpOut_lb_prefix _ cn true so f' resp $$ Hout Hresp with %Hrs
  icases tcpOut_lb_prefix _ cn false out f si $$ Hmy Hsi with %Hsio
  imod Hclose $$ [Hout Hv] with -
  · iexists so, f', si
    iframe Hout Hv Hsi
    ipureintro; exact Hso
  imodintro
  iframe Hmy
  ipureintro; exact Hrs.trans (Hso.trans Hsio)

end wps

end github_com.mit_pdos.etcd_grove.examples.net.framed
end Perennial
