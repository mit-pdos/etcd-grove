/-
The protocol of `examples/net/duplex`, over the TCP extension's resources (`GooseLang/Ext/Tcp`),
the per-address protocol (`wire/Addr.lean`) and the per-direction stream protocol
(`wire/Stream.lean`):

* **Every connection** `cn` to `srvAddr` has ghost names `γ` (`srvName γm cn γ`, persistent: the
  ghost map `γm`): the two directions' stream protocols (`γ.up`, from the dialer; `γ.down`, from
  the acceptor) and a ghost variable `γ.m`. Its state (`connInv cn γ`) is both directions'
  `dirInv`s and the server's side (`srvSide γ`): the acceptor's written bytes `W` (the writer's
  half `sentAll γ.down W`, mirrored by `γ.m`, whose other half is the server thread's) are a
  prefix of a lower bound `R` of the dialer's (`sentLb γ.up R`: bytes the server read). All
  connections' states are in one invariant (`srvState γm`), so that every resource the protocol
  moves is timeless; each direction's `inv srvN (dirInv …)`, which `Stream.lean`'s updates take, is
  derived from it (`dup_dirInv_up`/`_down`, `inv_alter`).
* **The connection's protocol** `connProto γm cn`, which the dialer deposits in `srvAddr`'s
  invariant (`dup_deposit`, through `wire.dial_both_au`) and the server takes at `Accept`: the acceptor
  end's state, the mirror's half (nothing written), the reader's half of the up-direction. The
  dialer keeps `dialerOwn γm cn`: its end's state, the writer's half of the up-direction, the
  reader's half of the down-direction.
* **The client's end** (`cliInv cn γ γw`, an invariant the client allocates after its dial,
  `cliInv_alloc`): the dialer end's state, shared by the writer goroutine and the reader (the main
  thread, which also closes it), and the up-direction's writer's half: the bytes written are the
  first `w` of 1, 2, 3, 4 (`dseq`), `w` mirrored by the ghost variable `γw` whose other half is the
  writer's (`cli_write_au`). The reader's half of the down-direction is the reader's own, in its
  predicate of `wire.ReadFull` (`cliP`, accessor `cli_read_acc`).

The client's check (`client_check`): what the client read (`sentLb γ.down`, from its reads) is a
prefix of what the server wrote (`sentAll γ.down W`), a prefix of what the server read
(`sentLb γ.up R`), a prefix of what the client wrote (`sentAll γ.up`), a prefix of `dseq`: the byte
read at position `i - 1` is `i`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask DirNames DirOk
  dirInv sentAll sentLb rcvdAll setMap_insert setMap_lookup_none)

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7104"

/-- The bytes the client writes, in order. -/
abbrev dseq : List w8 := [W8 1, W8 2, W8 3, W8 4]

def addrN : Namespace := nroot.@"duplex_addr"
def srvN : Namespace := nroot.@"duplex_conns"
def cliN : Namespace := nroot.@"duplex_client"

/-- The ghost names of a connection: the server's mirror of its written bytes, and the two
directions' stream protocols. -/
structure DupNames where
  m : GName
  up : DirNames
  down : DirNames

def DupNames.enc (γ : DupNames) : GName × GName × GName × GName × GName :=
  (γ.m, γ.up.w, γ.up.r, γ.down.w, γ.down.r)

instance DupNames.countable : Pos.Countable DupNames :=
  .ofInjective (fun γ => Pos.Countable.encode γ.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    obtain ⟨t, ⟨uw, ur⟩, ⟨dw, dr⟩⟩ := a
    obtain ⟨t', ⟨uw', ur'⟩, ⟨dw', dr'⟩⟩ := b
    simp only [DupNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

/-! ## Pure facts -/

theorem dseq_take_succ (i : Nat) (hi : i < 4) :
    dseq.take i ++ [W8 (i + 1)] = dseq.take (i + 1) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- The bytes read so far, `j + 1` of them a prefix of `dseq`: the last is `j + 1`. -/
theorem dseq_last (R got : List w8) (j : Nat) (hj : j < 4) (hR : R.length = j)
    (hg : got.length = 1) (hp : R ++ got <+: dseq) : got = [W8 (j + 1)] := by
  have hlen : (R ++ got).length = j + 1 := by simp [hR, hg]
  have ht : R ++ got = dseq.take (j + 1) := by
    have := List.prefix_iff_eq_take.1 hp
    rw [hlen] at this; exact this
  have hd : got = (R ++ got).drop j := by rw [List.drop_left' hR]
  rw [hd, ht]
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

section defs
variable {GF : BundledGFunctors}

/-- A half of the ghost variable `γ` (the server's view of its bytes, the writer's count). -/
def half {A : Type} [Pos.Countable A] (hT : TcpGS GF) (γ : GName) (a : A) : IProp GF :=
  @ghostVar GF hT.allG A _ γ (1 : Qp).half a

instance half_timeless {A : Type} [Pos.Countable A] (hT : TcpGS GF) (γ : GName) (a : A) :
    Timeless (half hT γ a) := by
  unfold half; letI := hT.allG; infer_instance

end defs

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The server's side of a connection with names `γ`: the acceptor's written bytes `W`, mirrored
by `γ.m`, a prefix of bytes `R` the dialer wrote. -/
def srvSide (γ : DupNames) : IProp GF :=
  iprop(∃ W R : List w8, sentAll (Gg := Gg) γ.down W ∗ half G γ.m W ∗ sentLb (Gg := Gg) γ.up R ∗
    ⌜W <+: R⌝)

instance srvSide_timeless (γ : DupNames) : Timeless (srvSide (Gg := Gg) γ) := by
  unfold srvSide; infer_instance

/-- The state of the connection `cn`, with names `γ`. -/
def connInv (cn : Nat) (γ : DupNames) : IProp GF :=
  iprop(dirInv (Gg := Gg) cn false γ.up ∗ dirInv (Gg := Gg) cn true γ.down ∗ srvSide γ)

instance connInv_timeless (cn : Nat) (γ : DupNames) : Timeless (connInv (Gg := Gg) cn γ) := by
  unfold connInv; infer_instance

/-- Every connection's state, their names in the ghost map `γm`. -/
def srvState (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat DupNames, @ghostMapAuth GF (G (Gg := Gg)).allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ γ ∈ m, connInv cn γ)

instance srvState_timeless (γm : GName) : Timeless (srvState (Gg := Gg) γm) := by
  unfold srvState; letI := (G (Gg := Gg)).allG; infer_instance

/-- The connection `cn`'s names are `γ`. -/
def srvName (γm : GName) (cn : Nat) (γ : DupNames) : IProp GF :=
  @ghostMapElem GF (G (Gg := Gg)).allG _ _ _ _ γm cn .discard γ

instance srvName_persistent (γm : GName) (cn : Nat) (γ : DupNames) :
    Persistent (srvName (Gg := Gg) γm cn γ) := by
  unfold srvName; letI := (G (Gg := Gg)).allG; infer_instance

instance srvName_timeless (γm : GName) (cn : Nat) (γ : DupNames) :
    Timeless (srvName (Gg := Gg) γm cn γ) := by
  unfold srvName; letI := (G (Gg := Gg)).allG; infer_instance

/-- What the server gets when it accepts `cn`. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, srvName (Gg := Gg) γm cn γ ∗ tcpEnd G cn true TcpEnd.fresh ∗
    half G γ.m ([] : List w8) ∗ rcvdAll (Gg := Gg) γ.up [] ∗ sentLb (Gg := Gg) γ.up [])

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`. -/
def dialerOwn (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, srvName (Gg := Gg) γm cn γ ∗ tcpEnd G cn false TcpEnd.fresh ∗
    sentAll (Gg := Gg) γ.up [] ∗ rcvdAll (Gg := Gg) γ.down [] ∗ sentLb (Gg := Gg) γ.down [])

/-- The invariants of the protocol. -/
def dupInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv srvN (srvState (Gg := Gg) γm))

instance dupInvs_persistent (γm : GName) : Persistent (dupInvs (Gg := Gg) γm) := by
  unfold dupInvs; infer_instance

theorem dupInvs_elim (γm : GName) :
    dupInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv srvN (srvState (Gg := Gg) γm) := .rfl

/-- The client's end of `cn` (names `γ`): its state, and the up-direction's written bytes, the
first `w` of `dseq` (`γw`). -/
def cliInv (cn : Nat) (γ : DupNames) (γw : GName) : IProp GF :=
  iprop(∃ (st : TcpEnd) (w : Nat), tcpEnd G cn false st ∗ sentAll (Gg := Gg) γ.up (dseq.take w) ∗
    half G γw w)

instance cliInv_timeless (cn : Nat) (γ : DupNames) (γw : GName) :
    Timeless (cliInv (Gg := Gg) cn γ γw) := by
  unfold cliInv; infer_instance

/-- The reader's predicate of `wire.ReadFull` on the client's end: the bytes `got` this call has
read after the `R0` read before, all written by the server. -/
def cliP (γ : DupNames) (R0 got : List w8) : IProp GF :=
  iprop(rcvdAll (Gg := Gg) γ.down (R0 ++ got) ∗ sentLb (Gg := Gg) γ.down (R0 ++ got))

theorem half_agree {A : Type} [Pos.Countable A] (γ : GName) (a b : A) :
    half (G (Gg := Gg)) γ a -∗ half G γ b -∗ ⌜a = b⌝ := by
  unfold half
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

theorem half_update {A : Type} [Pos.Countable A] (γ : GName) (a b c : A) :
    half (G (Gg := Gg)) γ a -∗ half G γ b ==∗ half G γ c ∗ half G γ c := by
  unfold half
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

theorem half_alloc {A : Type} [Pos.Countable A] (a : A) :
    ⊢ |==> ∃ γ, half (G (Gg := Gg)) γ a ∗ half G γ a := by
  unfold half
  letI := (G (Gg := Gg)).allG
  imod ghostVar_alloc (GF := GF) a with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply (ghostVar_split_half (GF := GF) γ 1 a).1 $$ H

/-- A dialer's deposit for its new connection `cn`: both directions' stream protocols, the
server's mirror, the names in the map, the connection's state (nothing written yet); the server's
part (`connProto`) and the dialer's (`dialerOwn`). -/
theorem dup_deposit (γm : GName) (cn : Nat) :
    ⊢ inv srvN (srvState (Gg := Gg) γm) -∗ tcpConnAt G cn srvAddr -∗ tcpFresh G cn false -∗
      tcpFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ dialerOwn γm cn := by
  iintro #Hinv #Hat Hd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "duplex_conns" "duplex_addr" (by decide)
  unfold srvState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFresh
  icases Hd with ⟨Hde, Hdd⟩
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its acceptor's direction is owned once
    icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm)).1 $$ Hconns with ⟨Hc, -⟩
    unfold connInv dirInv
    icases Hc with ⟨-, ⟨%d, %W, %R, Hdir, -⟩, -⟩
    icases tcpDir_excl _ cn true d TcpDir.fresh $$ Hdir Had with ⟨⟩
  | none =>
    imod wire.dirInv_body_alloc cn false $$ Hdd with ⟨%γu, HIu, Hwu, Hru⟩
    imod wire.dirInv_body_alloc cn true $$ Had with ⟨%γd, HId, Hwd, Hrd⟩
    imod half_alloc (Gg := Gg) ([] : List w8) with ⟨%γh, Hh1, Hh2⟩
    ihave #Hlbu : (sentLb (Gg := Gg) γu [] : IProp GF) $$ [Hwu]
    · iapply wire.sentLb_get
      iexact Hwu
    ihave #Hlbd : (sentLb (Gg := Gg) γd [] : IProp GF) $$ [Hwd]
    · iapply wire.sentLb_get
      iexact Hwd
    imod ghost_map_insert_persist cn (⟨γh, γu, γd⟩ : DupNames) hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns HIu HId Hwd Hh1] with -
    · inext
      iexists m.insert cn ⟨γh, γu, γd⟩
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold connInv srvSide
      iframe HIu HId
      iexists [], []
      iframe Hwd Hh1 Hlbu
      ipureintro; exact List.nil_prefix
    imodintro
    unfold connProto dialerOwn srvName
    isplitl [Hae Hh2 Hru]
    · iexists ⟨γh, γu, γd⟩
      iframe Hname Hae Hh2 Hru Hlbu
    · iexists ⟨γh, γu, γd⟩
      iframe Hname Hde Hwu Hrd Hlbd

/-- The state of a connection, from the invariant, by its names. -/
theorem srvState_lookup (γm : GName) (cn : Nat) (γ : DupNames) :
    srvName (Gg := Gg) γm cn γ ⊢ srvState γm -∗ connInv cn γ ∗ (connInv cn γ -∗ srvState γm) := by
  iintro #Hname Hi
  unfold srvState
  icases Hi with ⟨%m, Hm, Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold srvName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl)).1 $$ Hconns with ⟨Hc, Hback⟩
  iframe Hc
  iintro Hc
  iexists m
  iframe Hm
  iapply Hback $$ Hc

/-- The up-direction's stream invariant of a connection, from the protocol's. -/
theorem dup_dirInv_up (γm : GName) (cn : Nat) (γ : DupNames) :
    ⊢ inv srvN (srvState (Gg := Gg) γm) -∗ srvName γm cn γ -∗
      inv srvN (dirInv (Gg := Gg) cn false γ.up) := by
  iintro #Hinv #Hname
  iapply inv_alter $$ Hinv
  inext
  imodintro
  iintro Hi
  icases srvState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  iframe Hu
  iintro Hu
  iapply Hback
  iframe Hu Hd He

/-- The down-direction's stream invariant of a connection, from the protocol's. -/
theorem dup_dirInv_down (γm : GName) (cn : Nat) (γ : DupNames) :
    ⊢ inv srvN (srvState (Gg := Gg) γm) -∗ srvName γm cn γ -∗
      inv srvN (dirInv (Gg := Gg) cn true γ.down) := by
  iintro #Hinv #Hname
  iapply inv_alter $$ Hinv
  inext
  imodintro
  iintro Hi
  icases srvState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  iframe Hd
  iintro Hd
  iapply Hback
  iframe Hu Hd He

/-- A write by the server on `cn` (its end's state `st` the thread's) of bytes `bs` that, after
its bytes `W`, the dialer wrote (`sentLb γ.up (W ++ bs)`): its bytes are then `W ++ bs.take k`. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : DupNames) (W bs : List w8) (st : TcpEnd) :
    ⊢ inv srvN (srvState (Gg := Gg) γm) -∗ srvName γm cn γ -∗ half G γ.m W -∗
      sentLb (Gg := Gg) γ.up (W ++ bs) -∗ tcpEnd G cn true st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G cn true st0 ∗ tcpDir G cn true d ∗
        ∀ k ok d', ⌜WriteOutcome st0 d bs k ok d'⌝ -∗ tcpEnd G cn true st0 -∗
          tcpDir G cn true d' ={∅,⊤}=∗ tcpEnd G cn true st ∗ half G γ.m (W ++ bs.take k) ∗
            ⌜∃ d d', WriteOutcome st d bs k ok d'⌝ := by
  iintro #Hinv #Hname Hh #Hlb Hend
  iinv Hinv with Hi Hclose
  imod Hi
  icases srvState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  unfold dirInv
  icases Hd with ⟨%d, %Wi, %Ri, Hdir, Hw, Hr, %Hok⟩
  unfold srvSide
  icases He with ⟨%Ws, %Rs, Hws, Hh', #HRs, %HWs⟩
  icases half_agree (Gg := Gg) γ.m W Ws $$ Hh Hh' with %Heq
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %k %ok %d' %Hwr Hend Hdir
  imod Hmask
  imod wire.sentAll_app γ.down Wi W (bs.take k) $$ Hw Hws with ⟨%Heq, Hw, Hws⟩
  subst Heq
  imod half_update (Gg := Gg) γ.m Wi Wi (Wi ++ bs.take k) $$ Hh Hh' with ⟨Hh, Hh'⟩
  imod Hclose $$ [Hback Hu Hdir Hw Hr Hws Hh'] with -
  · inext
    iapply Hback
    iframe Hu
    isplitl [Hdir Hw Hr]
    · iexists d', Wi ++ bs.take k, Ri
      iframe Hdir Hw Hr
      ipureintro; exact wire.dirOk_write Hok Hwr
    · iexists Wi ++ bs.take k, Wi ++ bs
      iframe Hws Hh' Hlb
      ipureintro
      exact (List.prefix_append_right_inj Wi).2 (List.take_prefix k bs)
  imodintro
  iframe Hend Hh
  ipureintro; exact ⟨d, d', Hwr⟩

/-- The client's end, put in its invariant after the dial: nothing written. -/
theorem cliInv_alloc (cn : Nat) (γ : DupNames) :
    tcpEnd (G (Gg := Gg)) cn false TcpEnd.fresh -∗ sentAll (Gg := Gg) γ.up [] ={⊤}=∗
      ∃ γw, inv cliN (cliInv cn γ γw) ∗ half G γw (0 : Nat) := by
  iintro Hend Hw
  imod half_alloc (Gg := Gg) (0 : Nat) with ⟨%γw, Hw1, Hw2⟩
  imod inv_alloc cliN ⊤ (cliInv (Gg := Gg) cn γ γw) $$ [Hend Hw Hw1] with #Hinv
  · inext
    unfold cliInv
    iexists TcpEnd.fresh, 0
    rw [List.take_zero]
    iframe Hend Hw Hw1
  imodintro
  iexists γw
  iframe Hinv Hw2

/-- The reader's accessor of the client's end (`wire.ReadFull`'s), for `cliP`: the end's state
from the client's invariant, the down-direction from the connection's. -/
theorem cli_read_acc (cn : Nat) (γ : DupNames) (γw : GName) (R0 : List w8) :
    ⊢ inv cliN (cliInv (Gg := Gg) cn γ γw) -∗ inv srvN (dirInv (Gg := Gg) cn true γ.down) -∗
      □ (∀ (got : List w8) (m : Nat), cliP γ R0 got -∗
        |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn true d ∗
          ∀ r d', ⌜ReadOutcome st d m r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G cn false st -∗
            tcpDir G cn true d' ={∅,⊤}=∗ cliP γ R0 (got ++ r.got)) := by
  iintro #Hcli #Hdir
  imodintro
  iintro %got %m HP
  unfold cliP
  icases HP with ⟨Hr, -⟩
  iinv Hcli with Hi Hclose
  iinv Hdir with Hj Hclose'
  · exact ndot_mask nroot "duplex_conns" "duplex_client" (by decide)
  unfold cliInv
  icases Hi with ⟨%st, %w, >Hend, >Hw, >Hwh⟩
  unfold dirInv
  icases Hj with ⟨%d, %W, %R', >Hd, >Hwa, >Hr', >%Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %r %d' %Hrd Hend Hd
  imod Hmask
  unfold rcvdAll
  letI := (G (Gg := Gg)).allG
  icases ghostVar_agree $$ Hr' Hr with %Heq
  subst Heq
  imod ghostVar_update_halves (R0 ++ got ++ r.got) $$ Hr' Hr with ⟨Hr', Hr⟩
  have Hok' := wire.dirOk_read Hok Hrd.1
  ihave #Hlb : (sentLb (Gg := Gg) γ.down (R0 ++ got ++ r.got) : IProp GF) $$ [Hwa]
  · unfold sentLb
    iapply monoListLbOwn_le _ (wire.dirOk_prefix Hok')
    iapply monoListLbOwn_get
    iexact Hwa
  imod Hclose' $$ [Hd Hwa Hr'] with -
  · inext
    iexists d', W, R0 ++ got ++ r.got
    iframe Hd Hwa Hr'
    ipureintro; exact Hok'
  imod Hclose $$ [Hend Hw Hwh] with -
  · inext
    iexists st, w
    iframe Hend Hw Hwh
  imodintro
  rw [List.append_assoc]
  iframe Hr Hlb

/-- The writer's write of the byte `i + 1` after the first `i` of `dseq`: they are then the first
`i + k`. -/
theorem cli_write_au (cn : Nat) (γ : DupNames) (γw : GName) (i : Nat) (hi : i < 4) :
    ⊢ inv cliN (cliInv (Gg := Gg) cn γ γw) -∗ inv srvN (dirInv (Gg := Gg) cn false γ.up) -∗
      half G γw i -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn false d ∗
        ∀ k ok d', ⌜WriteOutcome st d [W8 (i + 1)] k ok d'⌝ -∗ tcpEnd G cn false st -∗
          tcpDir G cn false d' ={∅,⊤}=∗ half G γw (i + k) ∗ ⌜ok = true → k = 1⌝ := by
  iintro #Hcli #Hdir Hwh
  iinv Hcli with Hi Hclose
  iinv Hdir with Hj Hclose'
  · exact ndot_mask nroot "duplex_conns" "duplex_client" (by decide)
  unfold cliInv
  icases Hi with ⟨%st, %w, >Hend, >Hw, >Hwh'⟩
  icases half_agree (Gg := Gg) γw i w $$ Hwh Hwh' with %Heq
  subst Heq
  unfold dirInv
  icases Hj with ⟨%d, %W, %R, >Hd, >Hwa, >Hr, >%Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %ok %d' %Hwr Hend Hd
  imod Hmask
  have hk1 : k ≤ 1 := by simpa using wire.writeOutcome_le Hwr
  have hok : ok = true → k = 1 := by
    intro h; subst h; simpa using wire.writeOutcome_ok Hwr
  imod wire.sentAll_app γ.up W (dseq.take i) ([W8 (i + 1)].take k) $$ Hwa Hw with ⟨%Heq, Hwa, Hw⟩
  subst Heq
  imod half_update (Gg := Gg) γw i i (i + k) $$ Hwh Hwh' with ⟨Hwh, Hwh'⟩
  have htk : dseq.take i ++ [W8 (i + 1)].take k = dseq.take (i + k) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl
    · simp
    · exact dseq_take_succ i hi
  imod Hclose' $$ [Hd Hwa Hr] with -
  · inext
    iexists d', dseq.take i ++ [W8 (i + 1)].take k, R
    iframe Hd Hwa Hr
    ipureintro; exact wire.dirOk_write Hok Hwr
  imod Hclose $$ [Hend Hw Hwh'] with -
  · inext
    iexists st, i + k
    rw [htk]
    iframe Hend Hw Hwh'
  imodintro
  iframe Hwh
  ipureintro; exact hok

/-- A close of the client's end, by the reader (the writer may still be writing). -/
theorem cli_close_au (cn : Nat) (γ : DupNames) (γw : GName) :
    ⊢ inv cliN (cliInv (Gg := Gg) cn γ γw) -∗ inv srvN (dirInv (Gg := Gg) cn false γ.up) -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn false d ∗
        ∀ ok st' d', ⌜CloseOutcome st d ok st' d'⌝ -∗ tcpEnd G cn false st' -∗
          tcpDir G cn false d' ={∅,⊤}=∗ True := by
  iintro #Hcli #Hdir
  iinv Hcli with Hi Hclose
  iinv Hdir with Hj Hclose'
  · exact ndot_mask nroot "duplex_conns" "duplex_client" (by decide)
  unfold cliInv
  icases Hi with ⟨%st, %w, >Hend, >Hw, >Hwh⟩
  unfold dirInv
  icases Hj with ⟨%d, %W, %R, >Hd, >Hwa, >Hr, >%Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %st' %d' %Hc Hend Hd
  imod Hmask
  imod Hclose' $$ [Hd Hwa Hr] with -
  · inext
    iexists d', W, R
    iframe Hd Hwa Hr
    ipureintro; exact wire.dirOk_close Hok Hc
  imod Hclose $$ [Hend Hw Hwh] with -
  · inext
    iexists st', w
    iframe Hend Hw Hwh
  imodintro
  itrivial

/-- The client's check: what it read (`resp`) is a prefix of the server's bytes, of what the
server read, of what the client wrote: of `dseq`. -/
theorem client_check (γm : GName) (cn : Nat) (γ : DupNames) (γw : GName) (resp : List w8) :
    ⊢ inv srvN (srvState (Gg := Gg) γm) -∗ srvName γm cn γ -∗ inv cliN (cliInv cn γ γw) -∗
      sentLb (Gg := Gg) γ.down resp ={⊤}=∗ ⌜resp <+: dseq⌝ := by
  iintro #Hinv #Hname #Hcli #Hresp
  iinv Hinv with Hi Hclose
  imod Hi
  icases srvState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  unfold srvSide
  icases He with ⟨%Ws, %Rs, Hws, Hh, #HRs, %HWs⟩
  icases wire.sentLb_prefix γ.down Ws resp $$ Hws Hresp with %Hrs
  iinv Hcli with Hj Hclose'
  · exact ndot_mask nroot "duplex_client" "duplex_conns" (by decide)
  unfold cliInv
  icases Hj with ⟨%st, %w, >Hend, >Hw, >Hwh⟩
  icases wire.sentLb_prefix γ.up (dseq.take w) Rs $$ Hw HRs with %HRw
  imod Hclose' $$ [Hend Hw Hwh] with -
  · inext
    iexists st, w
    iframe Hend Hw Hwh
  imod Hclose $$ [Hback Hu Hd Hws Hh] with -
  · inext
    iapply Hback
    iframe Hu Hd
    iexists Ws, Rs
    iframe Hws Hh HRs
    ipureintro; exact HWs
  imodintro
  ipureintro
  exact Hrs.trans (HWs.trans (HRw.trans (List.take_prefix w dseq)))

/-- The protocol's invariants on a fresh network, from `srvAddr`'s pending set (empty). -/
theorem dupInvs_alloc :
    tcpPend (G (Gg := Gg)) srvAddr ∅ ={⊤}=∗ ∃ γm, dupInvs (Gg := Gg) γm := by
  iintro Hpend
  letI := (G (Gg := Gg)).allG
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := DupNames) with ⟨%γm, Hm⟩
  imod inv_alloc srvN ⊤ (srvState (Gg := Gg) γm) $$ [Hm] with #HsrvInv
  · inext
    unfold srvState
    iexists ∅
    iframe Hm
    iapply BigSepM.bigSepM_empty.2
    iempintro
  imod wire.addrInv_alloc addrN srvAddr (connProto (Gg := Gg) γm) $$ Hpend with #HaddrInv
  imodintro
  iexists γm
  unfold dupInvs
  iframe HaddrInv HsrvInv

end ghost

end github_com.mit_pdos.etcd_grove.examples.net.duplex
end Perennial
