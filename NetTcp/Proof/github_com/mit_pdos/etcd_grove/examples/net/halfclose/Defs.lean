/-
The protocol of `examples/net/halfclose`, over the TCP extension's resources (`GooseLang/Ext/Tcp`)
and the shared per-address protocol (`wire/Addr.lean`):

* **Every connection** `cn` to `srvAddr` has a ghost name `γ` (`hcName γm cn γ`, persistent: the
  ghost map `γm`) and a state (`hcConn cn γ`): the acceptor's written bytes `so` and FIN flag `f`
  (`tcpOut cn true so f`), mirrored in a ghost variable `γ` whose other half the server holds while
  it serves the connection (so that it knows them), and the crux: once the acceptor has sent its
  FIN, its bytes are all of the dialer's (`finEcho cn so`: the dialer has sent its FIN after bytes
  of `so`'s length, and has written at least `so`). All connections' states are in one invariant
  (`hcState γm`), so that every resource the protocol moves is timeless.
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`hc_deposit`, through `wire.dial_au`) and the server takes when it accepts `cn`
  (`wire.accept_au`): the acceptor end's state (`tcpEnd cn true fresh 0`), the server's half of the
  mirror (nothing written, no FIN) and its name.

Why `finEcho` holds when the server's FIN is sent (`server_close_au`): a close sends the FIN only
from an end that is not broken (`CloseRes`); the server's end breaks on any failed read or write (it
sets no deadline, `TcpEnd.onFail`), so it is not broken only if its read loop met EOF -- the
dialer's FIN after exactly the bytes read, `tcpFin` -- and its one write of them all succeeded.

The client's check (`client_check`): what it read until EOF is the server's bytes in full (the
server's FIN after them, `tcpOut_fin`), which `finEcho` says are the dialer's -- the client's own --
in full: a prefix of the client's bytes (`tcpOutLb`) of the length of its FIN's (`tcpOut_fin`).
Crashes change nothing here: the invariants are global, and a crashed end sends no FIN.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask)

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7105"

def addrN : Namespace := nroot.@"halfclose_addr"
def hcN : Namespace := nroot.@"halfclose_conns"

section defs
variable {GF : BundledGFunctors}

/-- A half of the mirror `γ` of the acceptor's written bytes and FIN flag. -/
def hcMirror (hT : TcpGS GF) (γ : GName) (so : GoString) (f : Bool) : IProp GF :=
  @ghostVar GF hT.allG _ _ γ (1 : Qp).half (so, f)

instance hcMirror_timeless (hT : TcpGS GF) (γ : GName) (so : GoString) (f : Bool) :
    Timeless (hcMirror hT γ so f) := by
  unfold hcMirror; letI := hT.allG; infer_instance

/-- The acceptor's bytes `so` of `cn` are the dialer's in full: the dialer has sent its FIN after
bytes of `so`'s length, and has written at least `so`. -/
def finEcho (hT : TcpGS GF) (cn : Nat) (so : GoString) : IProp GF :=
  iprop(∃ si, tcpFin hT cn false si ∗ tcpOutLb hT cn false so ∗ ⌜so.length = si.length⌝)

instance finEcho_persistent (hT : TcpGS GF) (cn : Nat) (so : GoString) :
    Persistent (finEcho hT cn so) := by
  unfold finEcho; infer_instance

instance finEcho_timeless (hT : TcpGS GF) (cn : Nat) (so : GoString) :
    Timeless (finEcho hT cn so) := by
  unfold finEcho; infer_instance

/-- The state of the connection `cn`, whose mirror is `γ`: the acceptor's bytes and FIN flag, and
if it has sent its FIN, `finEcho`. -/
def hcConn (hT : TcpGS GF) (cn : Nat) (γ : GName) : IProp GF :=
  iprop(∃ (so : GoString) (f : Bool), tcpOut hT cn true so f ∗ hcMirror hT γ so f ∗
    (⌜f = false⌝ ∨ finEcho hT cn so))

instance hcConn_timeless (hT : TcpGS GF) (cn : Nat) (γ : GName) :
    Timeless (hcConn hT cn γ) := by
  unfold hcConn; infer_instance

/-- Every connection's state, their mirrors' names in the ghost map `γm`. -/
def hcState (hT : TcpGS GF) (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat GName, @ghostMapAuth GF hT.allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ γ ∈ m, hcConn hT cn γ)

/-- The connection `cn`'s mirror is `γ`. -/
def hcName (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) : IProp GF :=
  @ghostMapElem GF hT.allG _ _ _ _ γm cn .discard γ

instance hcName_persistent (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Persistent (hcName hT γm cn γ) := by
  unfold hcName; letI := hT.allG; infer_instance

instance hcName_timeless (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Timeless (hcName hT γm cn γ) := by
  unfold hcName; letI := hT.allG; infer_instance

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What the server gets when it accepts `cn`. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn true TcpEnd.fresh 0 ∗ hcMirror G γ [] false ∗ hcName G γm cn γ)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- The invariants of the protocol. -/
def hcInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv hcN (hcState G γm))

instance hcInvs_persistent (γm : GName) : Persistent (hcInvs (Gg := Gg) γm) := by
  unfold hcInvs; infer_instance

theorem hcInvs_elim (γm : GName) :
    hcInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv hcN (hcState G γm) := .rfl

/-- A dialer's deposit for its new connection `cn`: a mirror, its name in the map, the
connection's state (nothing written, no FIN), and the acceptor end's state for the server. -/
theorem hc_deposit (γm : GName) (cn : Nat) :
    ⊢ inv hcN (hcState (G (Gg := Gg)) γm) -∗ tcpConnAt G cn srvAddr -∗
      tcpFreshEnd G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ ∃ γ, hcName G γm cn γ := by
  iintro #Hinv #Hat Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "halfclose_conns" "halfclose_addr" (by decide)
  unfold hcState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFreshEnd
  icases Ha with ⟨Hae, Hao⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its acceptor's written bytes are owned once
    icases BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm) $$ Hconns with ⟨Hc, -⟩
    unfold hcConn
    icases Hc with ⟨%so, %f, Hout, -⟩
    icases tcpOut_excl _ cn true so [] f false $$ Hout Hao with ⟨⟩
  | none =>
    imod ghostVar_alloc_halves (GF := GF) (([] : GoString), false) with ⟨%γ, Hv1, Hv2⟩
    imod ghost_map_insert_persist cn γ hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hao Hv1] with -
    · inext
      iexists m.insert cn γ
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold hcConn hcMirror
      iexists [], false
      iframe Hao Hv1
      ileft
      ipureintro; rfl
    imodintro
    unfold connProto hcName hcMirror
    isplitl [Hae Hv2]
    · iexists γ
      iframe Hae Hv2 Hname
    · iexists γ
      iexact Hname

/-- The state of a connection, from the invariant, by its mirror's name: it and the update that
puts it back. -/
theorem hcState_acc (γm : GName) (cn : Nat) (γ : GName) (E : CoPset) (hE : ↑hcN ⊆ E) :
    ⊢ inv hcN (hcState (G (Gg := Gg)) γm) -∗ hcName G γm cn γ -∗
      |={E, E \ ↑hcN}=> hcConn G cn γ ∗ (hcConn G cn γ ={E \ ↑hcN, E}=∗ True) := by
  iintro #Hinv #Hname
  iinv Hinv with Hi Hclose
  unfold hcState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold hcName
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
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn γ, hcConn (G (Gg := Gg)) k v) ⊢
      [∗map] k ↦ v ∈ m, hcConn G k v := by rw [hm]
  imod Hclose $$ [Hm Hback Hc] with -
  · inext
    iexists m
    iframe Hm
    iapply hconv
    iapply Hback $$ Hc
  imodintro
  itrivial

/-- The two halves of a mirror agree. -/
theorem hcMirror_agree (γ : GName) (so so' : GoString) (f f' : Bool) :
    hcMirror (G (Gg := Gg)) γ so f -∗ hcMirror G γ so' f' -∗ ⌜so = so' ∧ f = f'⌝ := by
  unfold hcMirror
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  icases ghostVar_agree $$ H1 H2 with %h
  ipureintro
  exact Prod.mk.inj h

/-- The two halves of a mirror, updated together. -/
theorem hcMirror_update (γ : GName) (so so' so'' : GoString) (f f' f'' : Bool) :
    hcMirror (G (Gg := Gg)) γ so f -∗ hcMirror G γ so' f' ==∗
      hcMirror G γ so'' f'' ∗ hcMirror G γ so'' f'' := by
  unfold hcMirror
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply ghostVar_update_halves (so'', f'') $$ H1 H2

/-- The server's write on `cn` of bytes `bs`, with its half of the mirror (`so`, no FIN): its bytes
become `so ++ bs.take k`, still with no FIN; it gets back the end's state after the write. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : GName) (bs so : GoString) (st : TcpEnd)
    (r : Nat) :
    ⊢ inv hcN (hcState (G (Gg := Gg)) γm) -∗ hcName G γm cn γ -∗ hcMirror G γ so false -∗
      tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st0 r0 out f, tcpEnd G cn true st0 r0 ∗ tcpOut G cn true out f ∗
        ∀ k ok st', ⌜WriteRes st0 bs k ok st'⌝ -∗ tcpEnd G cn true st' r0 -∗
          tcpOut G cn true (out ++ bs.take k) f ={∅,⊤}=∗
          ∃ st'', ⌜WriteRes st bs k ok st''⌝ ∗ tcpEnd G cn true st'' r ∗
            hcMirror G γ (so ++ bs.take k) false := by
  iintro #Hinv #Hname Hmy Hend
  imod hcState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn
  icases Hc with ⟨%so', %f, Hout, Hmir, Hcase⟩
  icases hcMirror_agree γ so so' false f $$ Hmy Hmir with %Hag
  obtain ⟨rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, so, false
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  imod hcMirror_update γ so so (so ++ bs.take k) false false false $$ Hmy Hmir with ⟨Hmy, Hmir⟩
  imod Hclose $$ [Hout Hmir] with -
  · iexists so ++ bs.take k, false
    iframe Hout Hmir
    ileft
    ipureintro; rfl
  imodintro
  iexists st'
  iframe Hend Hmy
  ipureintro; exact Hwr

/-- The server's close of `cn`, with its half of the mirror (`so`, `f`), when its end is broken or
`so` is the dialer's bytes in full: the FIN it may send keeps `finEcho`. -/
theorem server_close_au (γm : GName) (cn : Nat) (γ : GName) (so : GoString) (f : Bool)
    (st : TcpEnd) (r : Nat) :
    ⊢ inv hcN (hcState (G (Gg := Gg)) γm) -∗ hcName G γm cn γ -∗ hcMirror G γ so f -∗
      (⌜st.broken = true⌝ ∨ finEcho G cn so) -∗ tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn true st r ∗ tcpOut G cn true out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn true st' r -∗ tcpOut G cn true out f' ={∅,⊤}=∗ True := by
  iintro #Hinv #Hname Hmy #Hok Hend
  imod hcState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn
  icases Hc with ⟨%so', %f0, Hout, Hmir, #Hcase⟩
  icases hcMirror_agree γ so so' f f0 $$ Hmy Hmir with %Hag
  obtain ⟨rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, so, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr - Hout
  imod Hmask
  imod hcMirror_update γ so so so f f f' $$ Hmy Hmir with ⟨-, Hmir⟩
  iapply Hclose
  iexists so, f'
  iframe Hout Hmir
  rcases Hcr with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
  · iexact Hcase
  · cases f
    · cases hb : st.broken
      · simp only [Bool.not_false, Bool.or_true]
        icases Hok with (%Hb | #Hfe)
        · cases Hb
        · iright; iexact Hfe
      · ileft; ipureintro; rfl
    · simp only [Bool.true_or]
      iexact Hcase

/-- The client's check on `cn`, its bytes `out`: what it read until EOF (`resp`, a prefix of the
server's bytes, of the length of the server's FIN's) is `out`. -/
theorem client_check (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp sent : GoString) (hlen : sent.length = resp.length) :
    ⊢ inv hcN (hcState (G (Gg := Gg)) γm) -∗ hcName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp -∗ tcpFin G cn true sent ={⊤}=∗
      ⌜resp = out⌝ ∗ tcpOut G cn false out f := by
  iintro #Hinv #Hname Hmy #Hresp #Hfin
  imod hcState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold hcConn
  icases Hc with ⟨%so, %f', Hout, Hmir, #Hcase⟩
  icases tcpOut_lb_prefix _ cn true so f' resp $$ Hout Hresp with %Hrs
  icases tcpOut_fin _ cn true so f' sent $$ Hout Hfin with %Hf
  obtain ⟨hf', hsent⟩ := Hf
  icases Hcase with (%Hf | #Hfe)
  · rw [hf'] at Hf; cases Hf
  ihave #Hfe' := Hfe
  unfold finEcho
  icases Hfe' with ⟨%si, #Hsi, #Hlb, %Hsl⟩
  icases tcpOut_fin _ cn false out f si $$ Hmy Hsi with %Hf2
  icases tcpOut_lb_prefix _ cn false out f so $$ Hmy Hlb with %Hpre
  imod Hclose $$ [Hout Hmir] with -
  · iexists so, f'
    iframe Hout Hmir
    iright
    iexact Hfe
  imodintro
  iframe Hmy
  ipureintro
  have h1 : resp = so := Hrs.eq_of_length (by rw [← hlen, hsent])
  have h2 : so = out := Hpre.eq_of_length (by rw [Hsl, Hf2.2])
  rw [h1, h2]

/-- A shutdown of the write side by an end its thread owns: the update of
`net.TCPConn.CloseWrite`, which hands back the end's state and FIN flag after it. -/
theorem owned_closeWrite_au (c : Nat) (s : Bool) (st : TcpEnd) (r : Nat) (out : GoString)
    (f : Bool) :
    ⊢ tcpEnd G c s st r -∗ tcpOut (G (Gg := Gg)) c s out f -∗
      |={⊤,∅}=> ∃ st0 r0 out0 f0, tcpEnd G c s st0 r0 ∗ tcpOut G c s out0 f0 ∗
        ∀ ok st' f', ⌜CloseRes true (fun st => { st with wshut := true }) st0 f0 ok st' f'⌝ -∗
          tcpEnd G c s st' r0 -∗ tcpOut G c s out0 f' ={∅,⊤}=∗
          ∃ st'' f'', ⌜CloseRes true (fun st => { st with wshut := true }) st f ok st'' f''⌝ ∗
            tcpEnd G c s st'' r ∗ tcpOut G c s out f'' := by
  iintro Hend Hout
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr Hend Hout
  imod Hmask
  imodintro
  iexists st', f'
  iframe Hend Hout
  ipureintro; exact Hcr

end wps

end github_com.mit_pdos.etcd_grove.examples.net.halfclose
end Perennial
