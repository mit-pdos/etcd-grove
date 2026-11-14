/-
The protocol of `examples/net/framed`, over the TCP extension's resources (`GooseLang/Ext/Tcp`),
the per-direction stream protocol (`wire/Stream.lean`) and the per-address protocol
(`wire/Addr.lean`):

* **Every connection** `cn` to `srvAddr` has ghost names `γ` (`framedName γm cn γ`, persistent: the
  ghost map `γm`) and a state (`framedConn cn γ`): the stream protocol of its two directions, up
  (dialer to acceptor, `dirInv cn false γ.u`) and down (`dirInv cn true γ.d`), whose bodies are
  kept here rather than in invariants of their own (an invariant is not timeless, and the acceptor
  learns of a connection only through its timeless deposit); and the framed fact: the server's
  written bytes `so` (the down direction's writer half, `sentAll γ.d so`) are a prefix of a lower
  bound `si` of the client's (`sentLb γ.u si`), with a ghost variable `γ.v` holding `so` (half
  here, half with the thread serving the connection, `srvView`, so that the server knows what it
  has written). All connections' states are in one invariant (`framedState γm`), from which each
  direction's `inv framedN (dirInv …)` is derived (`framed_dirInv`, by `inv_alter`) for
  `wire/Stream.lean`'s updates.
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`framed_deposit`, through `wire.dial_both_au`) and the server takes when it accepts `cn`
  (`wire.accept_lis_au`): the acceptor end's state (`tcpEnd cn true fresh`), the reader half of
  the up direction (nothing read), the server's half of the view (nothing written) and the names.
  The dialer keeps its end's state, the writer half of the up direction and the reader half of the
  down direction (`dialerProto`).

The server writes back only bytes it has read: a write of `bs` after `so`, with `so ++ bs` a prefix
of a lower bound of the dialer's bytes (`server_write_au`), keeps the server's bytes a prefix of
the dialer's, whatever part of `bs` it writes. The client's check (`client_check`): a reply it read
(a lower bound of the server's bytes, `wire.read_au`) is a prefix of the server's bytes, which are
a prefix of the client's own. Crashes change nothing here: the invariants are global, and a
connection's protocol stays in the address's invariant until a server (of any incarnation) accepts
it; a server that crashes while serving a connection leaves its state in the invariant, and no one
writes on that end again.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.framed.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask DirNames dirInv
  sentAll sentLb rcvdAll DirOk)

namespace github_com.mit_pdos.etcd_grove.examples.net.framed

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7102"

def addrN : Namespace := nroot.@"framed_addr"
def framedN : Namespace := nroot.@"framed_conns"

/-- A connection's ghost names: its up direction's (`uw`, `ur`), its down direction's (`dw`,
`dr`), and the server's view (`v`). -/
structure FNames where
  uw : GName
  ur : GName
  dw : GName
  dr : GName
  v : GName
deriving DecidableEq

instance FNames.countable : Pos.Countable FNames :=
  .ofInjective (fun γ : FNames => Pos.Countable.encode (γ.uw, γ.ur, γ.dw, γ.dr, γ.v))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

/-- The up direction's (dialer to acceptor) names. -/
abbrev FNames.u (γ : FNames) : DirNames := ⟨γ.uw, γ.ur⟩
/-- The down direction's (acceptor to dialer) names. -/
abbrev FNames.d (γ : FNames) : DirNames := ⟨γ.dw, γ.dr⟩
/-- The names of the direction from the end `s`. -/
abbrev FNames.dir (γ : FNames) : Bool → DirNames
  | false => γ.u
  | true => γ.d

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Half of the ghost variable `γ`: the acceptor of its connection has written `so`. -/
def srvView (γ : GName) (so : List w8) : IProp GF :=
  @ghostVar GF (G (Gg := Gg)).allG (List w8) _ γ (1 : Qp).half so

instance srvView_timeless (γ : GName) (so : List w8) : Timeless (srvView (Gg := Gg) γ so) := by
  unfold srvView; letI := (G (Gg := Gg)).allG; infer_instance

/-- The framed fact of a connection with names `γ`: the server has written `so`, a prefix of a
lower bound `si` of the client's bytes. -/
def framedFact (γ : FNames) : IProp GF :=
  iprop(∃ (so si : List w8), sentAll (Gg := Gg) γ.d so ∗ srvView γ.v so ∗ sentLb γ.u si ∗
    ⌜so <+: si⌝)

/-- The state of the connection `cn`, whose names are `γ`: its two directions' stream protocol,
and the framed fact. -/
def framedConn (cn : Nat) (γ : FNames) : IProp GF :=
  iprop(dirInv (Gg := Gg) cn false γ.u ∗ dirInv cn true γ.d ∗ framedFact γ)

instance framedConn_timeless (cn : Nat) (γ : FNames) : Timeless (framedConn (Gg := Gg) cn γ) := by
  unfold framedConn framedFact; infer_instance

/-- Every connection's state, their names in the ghost map `γm`. -/
def framedState (γm : GName) : IProp GF :=
  letI := (G (Gg := Gg)).allG
  iprop(∃ m : GMap Nat FNames, ghostMapAuth γm 1 m ∗ [∗map] cn ↦ γ ∈ m, framedConn cn γ)

/-- The connection `cn`'s names are `γ`. -/
def framedName (γm : GName) (cn : Nat) (γ : FNames) : IProp GF :=
  letI := (G (Gg := Gg)).allG; ghostMapElem γm cn .discard γ

instance framedName_persistent (γm : GName) (cn : Nat) (γ : FNames) :
    Persistent (framedName (Gg := Gg) γm cn γ) := by
  unfold framedName; letI := (G (Gg := Gg)).allG; infer_instance

instance framedName_timeless (γm : GName) (cn : Nat) (γ : FNames) :
    Timeless (framedName (Gg := Gg) γm cn γ) := by
  unfold framedName; letI := (G (Gg := Gg)).allG; infer_instance

/-- What the server gets when it accepts `cn`: its end's state, the up direction's reader half,
its half of the view, and the names. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn true TcpEnd.fresh ∗ rcvdAll (Gg := Gg) γ.u [] ∗ sentLb γ.u [] ∗
    srvView γ.v [] ∗ framedName γm cn γ)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`: its end's state, the up direction's writer
half, the down direction's reader half, and the names. -/
def dialerProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn false TcpEnd.fresh ∗ sentAll (Gg := Gg) γ.u [] ∗ rcvdAll γ.d [] ∗
    sentLb γ.d [] ∗ framedName γm cn γ)

/-- The invariants of the protocol. -/
def framedInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv framedN (framedState γm))

instance framedInvs_persistent (γm : GName) : Persistent (framedInvs (Gg := Gg) γm) := by
  unfold framedInvs; infer_instance

theorem framedInvs_elim (γm : GName) :
    framedInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv framedN (framedState γm) := .rfl

/-- A dialer's deposit for its new connection `cn`: the two directions' protocols and the framed
fact (nothing written), the names in the map, the server's part (`connProto`) and the dialer's
(`dialerProto`). -/
theorem framed_deposit (γm : GName) (cn : Nat) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ tcpConnAt G cn srvAddr -∗
      tcpFresh G cn false -∗ tcpFresh G cn true ={⊤ \ ↑addrN}=∗
      connProto γm cn ∗ dialerProto γm cn := by
  iintro #Hinv #Hat Hd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "framed_conns" "framed_addr" (by decide)
  unfold framedState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFresh
  icases Hd with ⟨Hde, Hdd⟩
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: the direction from its dialer is owned once
    icases BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm) $$ Hconns with ⟨Hc, -⟩
    unfold framedConn dirInv
    icases Hc with ⟨⟨%d, %W, %R, Hd', -⟩, -⟩
    icases tcpDir_excl _ cn false d TcpDir.fresh $$ Hd' Hdd with ⟨⟩
  | none =>
    imod wire.dirInv_body_alloc cn false $$ Hdd with ⟨%γu, Hu, Huw, Hur⟩
    imod wire.dirInv_body_alloc cn true $$ Had with ⟨%γd, Hdn, Hdw, Hdr⟩
    imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γv, Hv⟩
    icases (ghostVar_split_half (GF := GF) γv 1 ([] : List w8)).1 $$ Hv with ⟨Hv1, Hv2⟩
    ihave #Hlb0 := wire.sentLb_get γu [] $$ Huw
    ihave #Hlbd := wire.sentLb_get γd [] $$ Hdw
    let γ : FNames := ⟨γu.w, γu.r, γd.w, γd.r, γv⟩
    imod ghost_map_insert_persist cn γ hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hu Hdn Hdw Hv1] with -
    · inext
      iexists m.insert cn γ
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold framedConn framedFact srvView
      iframe Hu Hdn
      iexists [], []
      iframe Hdw Hv1 Hlb0
      ipureintro; exact List.prefix_refl _
    imodintro
    unfold connProto dialerProto framedName srvView
    isplitl [Hae Hur Hv2]
    · iexists γ
      iframe Hae Hur Hlb0 Hv2 Hname
    · iexists γ
      iframe Hde Huw Hdr Hlbd Hname

/-- The state of a connection, from the invariant, by its names: it and the update that puts it
back. -/
theorem framedState_acc (γm : GName) (cn : Nat) (γ : FNames) (E : CoPset) (hE : ↑framedN ⊆ E) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗
      |={E, E \ ↑framedN}=> framedConn cn γ ∗ (framedConn cn γ ={E \ ↑framedN, E}=∗ True) := by
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
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn γ, framedConn (Gg := Gg) k v) ⊢
      [∗map] k ↦ v ∈ m, framedConn k v := by rw [hm]
  imod Hclose $$ [Hm Hback Hc] with -
  · inext
    iexists m
    iframe Hm
    iapply hconv
    iapply Hback $$ Hc
  imodintro
  itrivial

/-- The invariant of the direction from the end `s` of `cn`, derived from the connections' state
(`inv_alter`), for `wire/Stream.lean`'s updates. -/
theorem framed_dirInv (γm : GName) (cn : Nat) (γ : FNames) (s : Bool) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗
      inv framedN (dirInv cn s (γ.dir s)) := by
  iintro #Hinv #Hname
  iapply inv_alter $$ Hinv
  inext
  imodintro
  iintro Hi
  unfold framedState
  icases Hi with ⟨%m, Hm, Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold framedName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases BigSepM.bigSepM_insert_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl) $$ Hconns with ⟨Hc, Hback⟩
  have hm : PartialMap.insert m cn γ = m := by
    show m.insert cn γ = m
    apply GMap.ext; intro k; simp only [GMap.lookup_insert_eq_iff]
    split <;> simp_all
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn γ, framedConn (Gg := Gg) k v) ⊢
      [∗map] k ↦ v ∈ m, framedConn k v := by rw [hm]
  iunfold framedConn at Hc
  icases Hc with ⟨Hu, Hd, Hf⟩
  cases s
  · iframe Hu
    iintro Hu
    iexists m
    iframe Hm
    iapply hconv
    iapply Hback
    unfold framedConn; iframe Hu Hd Hf
  · iframe Hd
    iintro Hd
    iexists m
    iframe Hm
    iapply hconv
    iapply Hback
    unfold framedConn; iframe Hu Hd Hf

/-- `framed_dirInv` of the up direction. -/
theorem framed_upInv (γm : GName) (cn : Nat) (γ : FNames) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗
      inv framedN (dirInv cn false γ.u) := framed_dirInv γm cn γ false

/-- `framed_dirInv` of the down direction. -/
theorem framed_downInv (γm : GName) (cn : Nat) (γ : FNames) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗
      inv framedN (dirInv cn true γ.d) := framed_dirInv γm cn γ true

/-- `framed_dirInv` of the up direction, as the acceptor's reads take it. -/
theorem framed_upInv' (γm : GName) (cn : Nat) (γ : FNames) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗
      inv framedN (dirInv cn (!true) γ.u) := framed_dirInv γm cn γ false

/-- `framed_dirInv` of the down direction, as the dialer's reads take it. -/
theorem framed_downInv' (γm : GName) (cn : Nat) (γ : FNames) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗
      inv framedN (dirInv cn (!false) γ.d) := framed_dirInv γm cn γ true

/-- A write by the server on `cn` (its end's state `st`) of bytes `bs` after the `so` it has
written, with `so ++ bs` a prefix of a lower bound `si` of the dialer's bytes: whatever part of
`bs` the write writes, the server's bytes stay a prefix of the dialer's, and its view follows
them. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : FNames) (so bs si : List w8) (st : TcpEnd)
    (hbs : so ++ bs <+: si) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗ srvView γ.v so -∗
      sentLb γ.u si -∗ tcpEnd G cn true st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G cn true st0 ∗ tcpDir G cn true d ∗
        ∀ k ok d', ⌜WriteOutcome st0 d bs k ok d'⌝ -∗ tcpEnd G cn true st0 -∗
          tcpDir G cn true d' ={∅,⊤}=∗
          tcpEnd G cn true st ∗ srvView γ.v (so ++ bs.take k) ∗
            ⌜∃ d d', WriteOutcome st d bs k ok d'⌝ := by
  iintro #Hinv #Hname Hv #Hsi Hend
  imod framedState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold framedConn framedFact dirInv
  icases Hc with ⟨Hu, ⟨%d, %W, %R, Hd, Hwa, Hr, %Hok⟩, ⟨%so', %si', Hw, Hv', -, -⟩⟩
  letI := (G (Gg := Gg)).allG
  unfold srvView
  icases ghostVar_agree γ.v so _ so' _ $$ Hv Hv' with %Hso
  subst Hso
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %ok %d' %Hwr Hend Hd
  imod Hmask
  imod wire.sentAll_app γ.d W so (bs.take k) $$ Hwa Hw with ⟨%Heq, Hwa, Hw⟩
  subst Heq
  imod ghostVar_update_halves (W ++ bs.take k) γ.v W W $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hu Hd Hwa Hr Hw Hv'] with -
  · iframe Hu
    isplitl [Hd Hwa Hr]
    · iexists d', W ++ bs.take k, R
      iframe Hd Hwa Hr
      ipureintro; exact wire.dirOk_write Hok Hwr
    · iexists W ++ bs.take k, si
      iframe Hw Hv' Hsi
      ipureintro
      exact ((List.prefix_append_right_inj W).2 (List.take_prefix k bs)).trans hbs
  imodintro
  iframe Hend Hv
  ipureintro; exact ⟨d, d', Hwr⟩

/-- The client's check: a reply it read (`resp`, a lower bound of the server's bytes) is a prefix
of the client's own bytes `out`. -/
theorem client_check (γm : GName) (cn : Nat) (γ : FNames) (out resp : List w8) :
    ⊢ inv framedN (framedState (Gg := Gg) γm) -∗ framedName γm cn γ -∗
      sentAll γ.u out -∗ sentLb γ.d resp ={⊤}=∗ ⌜resp <+: out⌝ ∗ sentAll γ.u out := by
  iintro #Hinv #Hname Hmy #Hresp
  imod framedState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold framedConn framedFact
  icases Hc with ⟨Hu, Hd, ⟨%so, %si, Hw, Hv, #Hsi, %Hso⟩⟩
  icases wire.sentLb_prefix γ.d so resp $$ Hw Hresp with %Hrs
  icases wire.sentLb_prefix γ.u out si $$ Hmy Hsi with %Hsio
  imod Hclose $$ [Hu Hd Hw Hv] with -
  · iframe Hu Hd
    iexists so, si
    iframe Hw Hv Hsi
    ipureintro; exact Hso
  imodintro
  iframe Hmy
  ipureintro; exact Hrs.trans (Hso.trans Hsio)

end wps

end github_com.mit_pdos.etcd_grove.examples.net.framed
end Perennial
