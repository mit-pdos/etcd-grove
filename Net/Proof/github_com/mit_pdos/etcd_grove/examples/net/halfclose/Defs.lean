/-
The protocol of `examples/net/halfclose`, over the net extension's resources (`GooseLang/Ext/Net`),
the shared per-address protocol (`wire/Addr.lean`) and the stream bookkeeping of `wire/Stream.lean`
(`sentAll`, `rcvdAll`, `DirOk`):

* **Every connection** `cn` to `srvAddr` has ghost names `ns` (`hcName γm cn ns`, persistent: the
  ghost map `γm`), one `DirNames` per direction (`ns.u` from the dialer, `ns.d` from the acceptor),
  and a state (`hcConn cn ns`): for each direction its unread bytes (`netDir`), the invariant's
  halves of what its writer wrote (`W`) and its reader read (`R`), agreeing (`DirOk`), and the
  crux, `HcOk`: the acceptor wrote a prefix of what it read (`WD <+: RU`). All connections' states are in one invariant
  (`hcState γm`), so that every resource the protocol moves is timeless.
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`hc_deposit`, through `wire.dial_both_au`) and the server takes when it accepts `cn`
  (`wire.accept_lis_au`): the acceptor end's state, the reader's half of the up direction and the
  writer's half of the down direction, and the names. The dialer keeps the other halves
  (`clientProto`). A failed dial that abandons its connection (D16: the dialer's end closed, the up
  direction `⟨[], .fin⟩`) deposits the same `connProto` (`hc_deposit_ab`): its state has nothing
  written or read (`dirPart_alloc`, over `wire.dirInv_body_alloc_of` and `Net.dirOk_abandoned`),
  and nobody keeps the dialer's halves, so the server reads EOF and writes back nothing it did not
  read.

The client's check (`client_check`): what it read from the down direction (`RD`) is a prefix of
what the server wrote (`WD`, `DirOk`), a prefix of what the server read (`RU`, `HcOk`), a prefix of
what the client wrote (`WU`, `DirOk`), which the client knows, holding the writer's half of `WU`:
its request (a random one). No FIN or EOF reasoning:
EOF guarantees nothing (a killed process's kernel sends a FIN, `Impl.lean`, D1). Crashes change
nothing: the invariants are global.

The updates of the operations, each opening the connection's state: a `Write` is a loop of steps
(D2), each step's bytes extending what the writer wrote, by `client_write_au` and `server_write_au`
(`W ++ rs <+: R`, the bytes it read), with the writer predicates `cliW`,
`srvW` and the accessors `net.Conn.Write.spec` takes, `client_write_acc`, `server_write_acc`;
`client_read_acc`, `server_read_acc` (the accessors of `readAll`), `hc_close_au`,
`hc_closeWrite_au`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv DirNames sentAll rcvdAll dirInv dirInv_body_alloc_of sentAll_app)

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7105"

def addrN : Namespace := nroot.@"halfclose_addr"
def hcN : Namespace := nroot.@"halfclose_conns"

/-! ## The pure part -/

/-- The connection's protocol, on the up direction (`dU`, written `WU`, read `RU`) and the down
direction (`dD`, `WD`, `RD`): each direction's bookkeeping agrees (`DirOk`), the acceptor wrote a
prefix of what it read. -/
def HcOk (dU : NetDir) (WU RU : List w8) (dD : NetDir) (WD RD : List w8) : Prop :=
  DirOk dU WU RU ∧ DirOk dD WD RD ∧ WD <+: RU

/-- Nothing written or read. -/
theorem hcOk_nil {dU dD : NetDir} (hU : DirOk dU [] []) (hD : DirOk dD [] []) :
    HcOk dU [] [] dD [] [] :=
  ⟨hU, hD, List.nil_prefix⟩

/-- What the dialer read is a prefix of what it wrote. -/
theorem hcOk_check {dU dD : NetDir} {WU RU WD RD : List w8} (h : HcOk dU WU RU dD WD RD) :
    RD <+: WU :=
  (dirOk_prefix h.2.1).trans (h.2.2.trans (dirOk_prefix h.1))

/-! ## The ghost names -/

/-- The ghost names of a connection's protocol: each direction's `DirNames`. -/
structure HcNames where
  uw : GName
  ur : GName
  dw : GName
  dr : GName

instance HcNames.countable : Pos.Countable HcNames :=
  .ofInjective (fun ns : HcNames => Pos.Countable.encode (ns.uw, ns.ur, ns.dw, ns.dr))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h'; rfl)

/-- The up direction's names (from the dialer). -/
def HcNames.u (ns : HcNames) : DirNames := ⟨ns.uw, ns.ur⟩
/-- The down direction's names (from the acceptor). -/
def HcNames.d (ns : HcNames) : DirNames := ⟨ns.dw, ns.dr⟩
/-- The names of the two directions' protocols. -/
def HcNames.of (γu γd : DirNames) : HcNames := ⟨γu.w, γu.r, γd.w, γd.r⟩
theorem HcNames.of_u (γu γd : DirNames) : (HcNames.of γu γd).u = γu := rfl
theorem HcNames.of_d (γu γd : DirNames) : (HcNames.of γu γd).d = γd := rfl

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The invariant -/

/-- The invariant's part of a direction from the end `s` of `c` with names `γ`: its unread bytes,
and the invariant's halves of what its writer wrote and its reader read. -/
def dirPart (c : Nat) (s : Bool) (γ : DirNames) (d : NetDir) (W R : List w8) : IProp GF :=
  iprop(netDir G c s d ∗ @monoListAuthOwn GF (G (Gg := Gg)).allG _ _ γ.w (1 : Qp).half W ∗
    @ghostVar GF (G (Gg := Gg)).allG _ _ γ.r (1 : Qp).half R)

instance dirPart_timeless c s γ d W R : Timeless (dirPart (Gg := Gg) c s γ d W R) := by
  unfold dirPart; letI := (G (Gg := Gg)).allG; infer_instance

/-- The state of the connection `cn`, with names `ns`. -/
def hcConn (cn : Nat) (ns : HcNames) : IProp GF :=
  iprop(∃ (dU : NetDir) (WU RU : List w8) (dD : NetDir) (WD RD : List w8),
    dirPart (Gg := Gg) cn false ns.u dU WU RU ∗ dirPart cn true ns.d dD WD RD ∗
    ⌜HcOk dU WU RU dD WD RD⌝)

instance hcConn_timeless (cn : Nat) (ns : HcNames) : Timeless (hcConn (Gg := Gg) cn ns) := by
  unfold hcConn; infer_instance

/-- Every connection's state, their names in the ghost map `γm`. -/
def hcState (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat HcNames, @ghostMapAuth GF (G (Gg := Gg)).allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ ns ∈ m, hcConn (Gg := Gg) cn ns)

/-- The connection `cn`'s names are `ns`. -/
def hcName (γm : GName) (cn : Nat) (ns : HcNames) : IProp GF :=
  @ghostMapElem GF (G (Gg := Gg)).allG _ _ _ _ γm cn .discard ns

instance hcName_persistent (γm : GName) (cn : Nat) (ns : HcNames) :
    Persistent (hcName (Gg := Gg) γm cn ns) := by
  unfold hcName; letI := (G (Gg := Gg)).allG; infer_instance

instance hcName_timeless (γm : GName) (cn : Nat) (ns : HcNames) :
    Timeless (hcName (Gg := Gg) γm cn ns) := by
  unfold hcName; letI := (G (Gg := Gg)).allG; infer_instance

/-- What the server gets when it accepts `cn`: the acceptor end's state, the reader's half of the
up direction, the writer's half of the down direction. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ ns, netEnd G cn true NetEnd.fresh ∗ rcvdAll (Gg := Gg) ns.u [] ∗ sentAll ns.d [] ∗
    hcName γm cn ns)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`: its end's state, the writer's half of the up
direction, the reader's half of the down direction. -/
def clientProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ ns, netEnd G cn false NetEnd.fresh ∗ sentAll (Gg := Gg) ns.u [] ∗ rcvdAll ns.d [] ∗
    hcName γm cn ns)

/-- The invariants of the protocol. -/
def hcInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv hcN (hcState (Gg := Gg) γm))

instance hcInvs_persistent (γm : GName) : Persistent (hcInvs (Gg := Gg) γm) := by
  unfold hcInvs; infer_instance

theorem hcInvs_elim (γm : GName) :
    hcInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv hcN (hcState (Gg := Gg) γm) := .rfl

/-! ## Dialing -/

/-- A direction's protocol state, from its resource at a direction that agrees with nothing
written or read (`wire.dirInv_body_alloc_of`: a fresh direction, `dirOk_fresh`, or the shut empty
up direction of an abandoned dial, `dirOk_abandoned`), as the invariant's part of it: nothing
written or read, the writer's and the reader's halves. -/
theorem dirPart_alloc (c : Nat) (s : Bool) (d : NetDir) (hd : DirOk d [] []) :
    netDir (G (Gg := Gg)) c s d ==∗ ∃ γ d', dirPart c s γ d' [] [] ∗ ⌜DirOk d' [] []⌝ ∗
      sentAll γ [] ∗ rcvdAll γ [] := by
  letI := (G (Gg := Gg)).allG
  iintro Hd
  imod dirInv_body_alloc_of c s d hd $$ Hd with ⟨%γ, Hb, Hw, Hr⟩
  unfold dirInv sentAll rcvdAll
  icases Hb with ⟨%d', %W, %R, Hd, HW, HR, %Hok⟩
  icases monoListAuthOwn_agree γ.w _ _ W [] $$ HW Hw with %HW'
  icases ghostVar_agree γ.r R _ [] _ $$ HR Hr with %HR'
  obtain ⟨-, rfl⟩ := HW'
  subst HR'
  imodintro
  iexists γ, d'
  unfold dirPart
  iframe Hd HW HR Hw Hr
  ipureintro; exact Hok

/-- A dialer's deposit for its new connection `cn`, from both ends' fresh resources: the
connection's state (nothing written or read) in the invariant, the server's part (`connProto`) and
the dialer's (`clientProto`). -/
theorem hc_deposit (γm : GName) (cn : Nat) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ netConnAt G cn srvAddr -∗ netFresh G cn false -∗
      netFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ clientProto γm cn := by
  iintro #Hinv #Hat Hd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "halfclose_conns" "halfclose_addr" (by decide)
  unfold hcState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold netFresh
  icases Hd with ⟨Hde, Hdd⟩
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some ns' =>
    -- `cn` is new: its up direction's resource is owned once
    icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some ns' by
      rw [gmap_get?_eq]; exact hm)).1 $$ Hconns with ⟨Hc, -⟩
    unfold hcConn dirPart
    icases Hc with ⟨%dU, %WU, %RU, %dD, %WD, %RD, ⟨HdU, -, -⟩, -, -⟩
    icases netDir_excl _ cn false dU NetDir.fresh $$ HdU Hdd with ⟨⟩
  | none =>
    imod dirPart_alloc cn false _ dirOk_fresh $$ Hdd with ⟨%γu, %dU, HuP, %HokU, HuS, HuC⟩
    imod dirPart_alloc cn true _ dirOk_fresh $$ Had with ⟨%γd, %dD, HdP, %HokD, HdS, HdC⟩
    imod ghost_map_insert_persist cn (HcNames.of γu γd) hm $$ Hm
      with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns HuP HdP] with -
    · inext
      iexists m.insert cn (HcNames.of γu γd)
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold hcConn
      iexists dU, [], [], dD, [], []
      rw [HcNames.of_u, HcNames.of_d]
      iframe HuP HdP
      ipureintro; exact hcOk_nil HokU HokD
    imodintro
    unfold connProto clientProto hcName
    isplitl [Hae HuC HdS]
    · iexists (HcNames.of γu γd)
      rw [HcNames.of_u, HcNames.of_d]
      iframe Hae HuC HdS Hname
    · iexists (HcNames.of γu γd)
      rw [HcNames.of_u, HcNames.of_d]
      iframe Hde HuS HdC Hname

/-- A failed dial's deposit for the connection `cn` it abandoned (D16): its dialer's end closed,
the up direction shut and empty, the acceptor's end fresh. The connection's state (nothing written
or read; the up direction `⟨[], .fin⟩`) goes in the invariant and the server's part (`connProto`)
in the address's; nobody writes into the up direction or reads the down one (the dialer's halves
are dropped). -/
theorem hc_deposit_ab (γm : GName) (cn : Nat) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ netConnAt G cn srvAddr -∗
      netEnd G cn false { NetEnd.fresh with closed := true } -∗ netDir G cn false ⟨[], .fin⟩ -∗
      netFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn := by
  iintro #Hinv #Hat - Hdd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "halfclose_conns" "halfclose_addr" (by decide)
  unfold hcState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold netFresh
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some ns' =>
    -- `cn` is new: its up direction's resource is owned once
    icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some ns' by
      rw [gmap_get?_eq]; exact hm)).1 $$ Hconns with ⟨Hc, -⟩
    unfold hcConn dirPart
    icases Hc with ⟨%dU, %WU, %RU, %dD, %WD, %RD, ⟨HdU, -, -⟩, -, -⟩
    icases netDir_excl _ cn false dU _ $$ HdU Hdd with ⟨⟩
  | none =>
    imod dirPart_alloc cn false _ dirOk_abandoned $$ Hdd with ⟨%γu, %dU, HuP, %HokU, -, HuC⟩
    imod dirPart_alloc cn true _ dirOk_fresh $$ Had with ⟨%γd, %dD, HdP, %HokD, HdS, -⟩
    imod ghost_map_insert_persist cn (HcNames.of γu γd) hm $$ Hm
      with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns HuP HdP] with -
    · inext
      iexists m.insert cn (HcNames.of γu γd)
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold hcConn
      iexists dU, [], [], dD, [], []
      rw [HcNames.of_u, HcNames.of_d]
      iframe HuP HdP
      ipureintro; exact hcOk_nil HokU HokD
    imodintro
    unfold connProto hcName
    iexists (HcNames.of γu γd)
    rw [HcNames.of_u, HcNames.of_d]
    iframe Hae HuC HdS Hname

/-! ## Opening a connection's state -/

/-- The state of a connection, from the invariant, by its name: it and the update that puts it
back. -/
theorem hcState_acc (γm : GName) (cn : Nat) (ns : HcNames) (E : CoPset) (hE : ↑hcN ⊆ E) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ hcName γm cn ns -∗
      |={E, E \ ↑hcN}=> hcConn cn ns ∗ (hcConn cn ns ={E \ ↑hcN, E}=∗ True) := by
  iintro #Hinv #Hname
  iinv Hinv with Hi Hclose
  unfold hcState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold hcName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some ns by
    rw [gmap_get?_eq]; exact Hl)).1 $$ Hconns with ⟨Hc, Hback⟩
  imodintro
  iframe Hc
  iintro Hc
  imod Hclose $$ [Hm Hback Hc] with -
  · inext
    iexists m
    iframe Hm
    iapply Hback $$ Hc
  imodintro
  itrivial

/-- The direction from the end `s` of a connection's state, and its write-back at a direction
that keeps every `DirOk`. -/
theorem hcConn_dir (cn : Nat) (ns : HcNames) (s : Bool) :
    hcConn (Gg := Gg) cn ns ⊢ ∃ d, netDir G cn s d ∗
      (∀ d', ⌜∀ W R, DirOk d W R → DirOk d' W R⌝ -∗ netDir G cn s d' -∗ hcConn cn ns) := by
  unfold hcConn dirPart
  iintro ⟨%dU, %WU, %RU, %dD, %WD, %RD, ⟨HdU, HwU, HrU⟩, ⟨HdD, HwD, HrD⟩, %Hok⟩
  cases s
  · iexists dU
    iframe HdU
    iintro %d' %Hd' HdU
    iexists d', WU, RU, dD, WD, RD
    iframe HdU HwU HrU HdD HwD HrD
    ipureintro
    exact ⟨Hd' _ _ Hok.1, Hok.2.1, Hok.2.2⟩
  · iexists dD
    iframe HdD
    iintro %d' %Hd' HdD
    iexists dU, WU, RU, d', WD, RD
    iframe HdU HwU HrU HdD HwD HrD
    ipureintro
    exact ⟨Hok.1, Hd' _ _ Hok.2.1, Hok.2.2⟩

/-! ## The updates -/

/-- One step of the dialer's `Write` on `cn` (its end's state `st`), of the bytes `rs` it has not
written yet, having written `W`: it has then written `W ++ rs.take k`. -/
theorem client_write_au (γm : GName) (cn : Nat) (ns : HcNames) (st : NetEnd) (W rs : List w8) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ hcName γm cn ns -∗ netEnd G cn false st -∗
      sentAll ns.u W -∗
      |={⊤,∅}=> ∃ st0 d, netEnd G cn false st0 ∗ netDir G cn false d ∗
        ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn false st0 -∗
          netDir G cn false d' ={∅,⊤}=∗ netEnd G cn false st ∗
            sentAll ns.u (W ++ rs.take k) := by
  iintro #Hinv #Hname Hend Hw
  imod hcState_acc γm cn ns ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn dirPart
  icases Hc with ⟨%dU, %WU, %RU, %dD, %WD, %RD, ⟨HdU, HwU, HrU⟩, HD, %Hok⟩
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, dU
  iframe Hend HdU
  iintro %k %res %d' %Hwr Hend HdU
  imod Hmask
  imod sentAll_app ns.u WU W (rs.take k) $$ HwU Hw with ⟨%Heq, HwU, Hw⟩
  subst Heq
  imod Hclose $$ [HdU HwU HrU HD] with -
  · try unfold hcConn dirPart
    iexists d', WU ++ rs.take k, RU, dD, WD, RD
    iframe HdU HwU HrU HD
    ipureintro
    exact ⟨dirOk_write Hok.1 Hwr, Hok.2.1, Hok.2.2⟩
  imodintro
  iframe Hend Hw

/-- The dialer's writer predicate of `net.Conn.Write.spec` on `cn`: its end's state, and the bytes
`w` its `Write` of its request has written so far (all it has written). -/
def cliW (ns : HcNames) (cn : Nat) (st : NetEnd) (w : List w8) : IProp GF :=
  iprop(netEnd G cn false st ∗ sentAll (Gg := Gg) ns.u w)

/-- The accessor of the dialer's `Write` of its request `bs`, for `cliW`: each step's bytes extend
what it wrote (`client_write_au`). -/
theorem client_write_acc (γm : GName) (cn : Nat) (ns : HcNames) (st : NetEnd) (bs : List w8) :
    inv hcN (hcState (Gg := Gg) γm) ∗ hcName γm cn ns ⊢
      □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ cliW ns cn st w -∗
        |={⊤,∅}=> ∃ st0 d, netEnd G cn false st0 ∗ netDir G cn false d ∗
          ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn false st0 -∗
            netDir G cn false d' ={∅,⊤}=∗ cliW ns cn st (w ++ rs.take k)) := by
  iintro ⟨#Hinv, #Hname⟩
  imodintro
  iintro %w %rs %_ HP
  unfold cliW
  icases HP with ⟨Hend, Hw⟩
  iapply client_write_au γm cn ns st w rs $$ Hinv Hname Hend Hw

/-- One step of the server's `Write` on `cn` (its end's state `st`), of the bytes `rs` it has not
written yet, having written `W` and read `R`, with `W ++ rs` a prefix of `R`: it has then written
`W ++ rs.take k`. -/
theorem server_write_au (γm : GName) (cn : Nat) (ns : HcNames) (st : NetEnd) (W R rs : List w8)
    (h : W ++ rs <+: R) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ hcName γm cn ns -∗ netEnd G cn true st -∗
      sentAll ns.d W -∗ rcvdAll ns.u R -∗
      |={⊤,∅}=> ∃ st0 d, netEnd G cn true st0 ∗ netDir G cn true d ∗
        ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn true st0 -∗
          netDir G cn true d' ={∅,⊤}=∗ netEnd G cn true st ∗ sentAll ns.d (W ++ rs.take k) ∗
            rcvdAll ns.u R := by
  iintro #Hinv #Hname Hend Hw Hr
  imod hcState_acc γm cn ns ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn dirPart
  icases Hc with ⟨%dU, %WU, %RU, %dD, %WD, %RD, ⟨HdU, HwU, HrU⟩, ⟨HdD, HwD, HrD⟩, %Hok⟩
  letI := (G (Gg := Gg)).allG
  unfold rcvdAll
  icases ghostVar_agree $$ HrU Hr with %HeqR
  subst HeqR
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, dD
  iframe Hend HdD
  iintro %k %res %d' %Hwr Hend HdD
  imod Hmask
  imod sentAll_app ns.d WD W (rs.take k) $$ HwD Hw with ⟨%Heq, HwD, Hw⟩
  subst Heq
  imod Hclose $$ [HdU HwU HrU HdD HwD HrD] with -
  · try unfold hcConn dirPart
    iexists dU, WU, RU, d', WD ++ rs.take k, RD
    iframe HdU HwU HrU HdD HwD HrD
    ipureintro
    exact ⟨Hok.1, dirOk_write Hok.2.1 Hwr,
      ((List.prefix_append_right_inj WD).2 (List.take_prefix k rs)).trans h⟩
  imodintro
  iframe Hend Hw Hr

/-- The server's writer predicate of `net.Conn.Write.spec` on `cn`: its end's state, the bytes `w`
its `Write` of what it read (`R`) has written so far (all it has written), and what it read. -/
def srvW (ns : HcNames) (cn : Nat) (st : NetEnd) (R w : List w8) : IProp GF :=
  iprop(netEnd G cn true st ∗ sentAll (Gg := Gg) ns.d w ∗ rcvdAll ns.u R)

/-- The accessor of the server's `Write` of what it read (`R`), for `srvW`: each step's bytes
extend what it wrote, a prefix of `R` (`server_write_au`). -/
theorem server_write_acc (γm : GName) (cn : Nat) (ns : HcNames) (st : NetEnd) (R : List w8) :
    inv hcN (hcState (Gg := Gg) γm) ∗ hcName γm cn ns ⊢
      □ (∀ (w rs : List w8), ⌜w ++ rs = R⌝ -∗ srvW ns cn st R w -∗
        |={⊤,∅}=> ∃ st0 d, netEnd G cn true st0 ∗ netDir G cn true d ∗
          ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn true st0 -∗
            netDir G cn true d' ={∅,⊤}=∗ srvW ns cn st R (w ++ rs.take k)) := by
  iintro ⟨#Hinv, #Hname⟩
  imodintro
  iintro %w %rs %Hbs HP
  unfold srvW
  icases HP with ⟨Hend, Hw, Hr⟩
  iapply server_write_au γm cn ns st w R rs (by rw [Hbs]; exact List.prefix_refl _) $$ Hinv Hname Hend Hw Hr

/-- The server's reader predicate of `readAll` on `cn`: its end's state, and the bytes `got` read
from the up direction. -/
def srvP (ns : HcNames) (cn : Nat) (st : NetEnd) (got : List w8) : IProp GF :=
  iprop(netEnd G cn true st ∗ rcvdAll (Gg := Gg) ns.u got)

/-- The accessor of `readAll` for `srvP`. -/
theorem server_read_acc (γm : GName) (cn : Nat) (ns : HcNames) (st : NetEnd) :
    inv hcN (hcState (Gg := Gg) γm) ∗ hcName γm cn ns ⊢
      □ (∀ (got : List w8) (m : Nat), srvP ns cn st got -∗
        |={⊤,∅}=> ∃ st0 d, netEnd G cn true st0 ∗ netDir G cn false d ∗
          ∀ r d', ⌜ReadOutcome st0 d m r d'⌝ -∗ netEnd G cn true st0 -∗
            netDir G cn false d' ={∅,⊤}=∗ srvP ns cn st (got ++ r.got)) := by
  iintro ⟨#Hinv, #Hname⟩
  imodintro
  iintro %got %m HP
  unfold srvP
  icases HP with ⟨Hend, Hr⟩
  imod hcState_acc γm cn ns ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn dirPart
  icases Hc with ⟨%dU, %WU, %RU, %dD, %WD, %RD, ⟨HdU, HwU, HrU⟩, HD, %Hok⟩
  letI := (G (Gg := Gg)).allG
  unfold rcvdAll
  icases ghostVar_agree $$ HrU Hr with %HeqR
  subst HeqR
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, dU
  iframe Hend HdU
  iintro %r %d' %Hrd Hend HdU
  imod Hmask
  imod ghostVar_update_halves (RU ++ r.got) $$ HrU Hr with ⟨HrU, Hr⟩
  imod Hclose $$ [HdU HwU HrU HD] with -
  · try unfold hcConn dirPart
    iexists d', WU, RU ++ r.got, dD, WD, RD
    iframe HdU HwU HrU HD
    ipureintro
    exact ⟨dirOk_read Hok.1 Hrd, Hok.2.1, Hok.2.2.trans (List.prefix_append RU r.got)⟩
  imodintro
  iframe Hend Hr

/-- The dialer's reader predicate of `readAll` on `cn`: its end's state, and the bytes `got` read
from the down direction. -/
def cliP (ns : HcNames) (cn : Nat) (st : NetEnd) (got : List w8) : IProp GF :=
  iprop(netEnd G cn false st ∗ rcvdAll (Gg := Gg) ns.d got)

/-- The accessor of `readAll` for `cliP`. -/
theorem client_read_acc (γm : GName) (cn : Nat) (ns : HcNames) (st : NetEnd) :
    inv hcN (hcState (Gg := Gg) γm) ∗ hcName γm cn ns ⊢
      □ (∀ (got : List w8) (m : Nat), cliP ns cn st got -∗
        |={⊤,∅}=> ∃ st0 d, netEnd G cn false st0 ∗ netDir G cn true d ∗
          ∀ r d', ⌜ReadOutcome st0 d m r d'⌝ -∗ netEnd G cn false st0 -∗
            netDir G cn true d' ={∅,⊤}=∗ cliP ns cn st (got ++ r.got)) := by
  iintro ⟨#Hinv, #Hname⟩
  imodintro
  iintro %got %m HP
  unfold cliP
  icases HP with ⟨Hend, Hr⟩
  imod hcState_acc γm cn ns ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn dirPart
  icases Hc with ⟨%dU, %WU, %RU, %dD, %WD, %RD, HU, ⟨HdD, HwD, HrD⟩, %Hok⟩
  letI := (G (Gg := Gg)).allG
  unfold rcvdAll
  icases ghostVar_agree $$ HrD Hr with %HeqR
  subst HeqR
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, dD
  iframe Hend HdD
  iintro %r %d' %Hrd Hend HdD
  imod Hmask
  imod ghostVar_update_halves (RD ++ r.got) $$ HrD Hr with ⟨HrD, Hr⟩
  imod Hclose $$ [HU HdD HwD HrD] with -
  · try unfold hcConn dirPart
    iexists dU, WU, RU, d', WD, RD ++ r.got
    iframe HU HdD HwD HrD
    ipureintro
    exact ⟨Hok.1, dirOk_read Hok.2.1 Hrd, Hok.2.2⟩
  imodintro
  iframe Hend Hr

/-- The client's check on `cn`: what it read from the down direction is a prefix of what it wrote
(`W`, its writer's half). -/
theorem client_check (γm : GName) (cn : Nat) (ns : HcNames) (W R : List w8) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ hcName γm cn ns -∗ sentAll ns.u W -∗ rcvdAll ns.d R ={⊤}=∗
      ⌜R <+: W⌝ ∗ sentAll ns.u W ∗ rcvdAll ns.d R := by
  iintro #Hinv #Hname Hw Hr
  imod hcState_acc γm cn ns ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn dirPart
  icases Hc with ⟨%dU, %WU, %RU, %dD, %WD, %RD, ⟨HdU, HwU, HrU⟩, ⟨HdD, HwD, HrD⟩, %Hok⟩
  letI := (G (Gg := Gg)).allG
  unfold rcvdAll
  icases ghostVar_agree $$ HrD Hr with %HeqR
  subst HeqR
  unfold sentAll
  icases monoListAuthOwn_agree ns.u.w _ _ WU W $$ HwU Hw with %Hag
  obtain ⟨-, rfl⟩ := Hag
  imod Hclose $$ [HdU HwU HrU HdD HwD HrD] with -
  · try unfold hcConn dirPart
    iexists dU, WU, RU, dD, WD, RD
    iframe HdU HwU HrU HdD HwD HrD
    ipureintro; exact Hok
  imodintro
  iframe Hr Hw
  ipureintro; exact hcOk_check Hok

/-- A close of the end `s` of `cn` (its state `st` the thread's): the direction from it shut
(`CloseOutcome`). -/
theorem hc_close_au (γm : GName) (cn : Nat) (ns : HcNames) (s : Bool) (st : NetEnd) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ hcName γm cn ns -∗ netEnd G cn s st -∗
      |={⊤,∅}=> ∃ st0 d, netEnd G cn s st0 ∗ netDir G cn s d ∗
        ∀ ok st' d', ⌜CloseOutcome st0 d ok st' d'⌝ -∗ netEnd G cn s st' -∗ netDir G cn s d'
          ={∅,⊤}=∗ True := by
  iintro #Hinv #Hname Hend
  imod hcState_acc γm cn ns ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  icases hcConn_dir cn ns s $$ Hc with ⟨%d, Hd, Hback⟩
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %st' %d' %Hcl - Hd
  imod Hmask
  iapply Hclose
  iapply Hback $$ %d' [] Hd
  ipureintro; intro W R h; exact dirOk_close h Hcl

/-- A `CloseWrite` of the end `s` of `cn` (its state `st` the thread's): the direction from it shut
(`CloseWriteOutcome`); the end's state is handed back. -/
theorem hc_closeWrite_au (γm : GName) (cn : Nat) (ns : HcNames) (s : Bool) (st : NetEnd) :
    ⊢ inv hcN (hcState (Gg := Gg) γm) -∗ hcName γm cn ns -∗ netEnd G cn s st -∗
      |={⊤,∅}=> ∃ st0 d, netEnd G cn s st0 ∗ netDir G cn s d ∗
        ∀ ok d', ⌜CloseWriteOutcome st0 d ok d'⌝ -∗ netEnd G cn s st0 -∗ netDir G cn s d'
          ={∅,⊤}=∗ netEnd G cn s st := by
  iintro #Hinv #Hname Hend
  imod hcState_acc γm cn ns ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  icases hcConn_dir cn ns s $$ Hc with ⟨%d, Hd, Hback⟩
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %d' %Hcl Hend Hd
  imod Hmask
  imod Hclose $$ [Hback Hd] with -
  · iapply Hback $$ %d' [] Hd
    ipureintro; intro W R h; exact dirOk_closeWrite h Hcl
  imodintro
  iexact Hend

end wps

end github_com.mit_pdos.etcd_grove.examples.net.halfclose
end Perennial
