/-
The protocol of `examples/net/duplex`, over the TCP extension's resources (`GooseLang/Ext/Tcp`)
and the per-address protocol (`wire/Addr.lean`):

* **The server's side of every connection** `cn` to `srvAddr` (`srvConn cn γ`, all of them in one
  invariant `srvState γm` over a ghost map of names, as echo's): the acceptor's written bytes `so`
  (`tcpOut cn true so f`) are a prefix of a lower bound of the dialer's (`tcpOutLb cn false si`);
  a ghost variable `γ` mirrors `so`, its other half the server thread's, so that the server knows
  its own bytes and appends to them only bytes it has read (`server_write_au`).
* **The connection's protocol** `connProto γm cn`, which the dialer deposits in the address's
  invariant (`dup_deposit`, through `wire.dial_au`) and the server takes at `Accept`: the acceptor
  end's state and the ghost variable's half (nothing written).
* **The client's end** (`cliInv cn γr γw`, an invariant the client allocates after its dial): the
  dialer end's state and written bytes, shared by the writer goroutine and the reader (the main
  thread, which also closes it); the written bytes are the first `w` of 1, 2, 3, 4 (`dseq`), `w`
  mirrored by the ghost variable `γw` whose other half is the writer's (`cli_write_au`); the read
  position `r` by `γr`, whose other half is the reader's predicate of `wire.ReadFull`
  (`cli_read_acc`).

The client's check (`client_check`): a reply it read is a prefix of the server's bytes, a prefix
of the client's, a prefix of `dseq`: the byte read at position `i - 1` is `i`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask)

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7104"

/-- The bytes the client writes, in order. -/
abbrev dseq : List w8 := [W8 1, W8 2, W8 3, W8 4]

def addrN : Namespace := nroot.@"duplex_addr"
def srvN : Namespace := nroot.@"duplex_conns"
def cliN : Namespace := nroot.@"duplex_client"

section defs
variable {GF : BundledGFunctors}

/-- A half of the ghost variable `γ` (the server's view of its bytes, the writer's count, the
reader's position). -/
def half {A : Type} [Pos.Countable A] (hT : TcpGS GF) (γ : GName) (a : A) : IProp GF :=
  @ghostVar GF hT.allG A _ γ (1 : Qp).half a

instance half_timeless {A : Type} [Pos.Countable A] (hT : TcpGS GF) (γ : GName) (a : A) :
    Timeless (half hT γ a) := by
  unfold half; letI := hT.allG; infer_instance

/-- The server's side of the connection `cn`, whose ghost variable is `γ`. -/
def srvConn (hT : TcpGS GF) (cn : Nat) (γ : GName) : IProp GF :=
  iprop(∃ (so : GoString) (f : Bool), tcpOut hT cn true so f ∗
    half hT γ so ∗
    ∃ si, tcpOutLb hT cn false si ∗ ⌜so <+: si⌝)

instance srvConn_timeless (hT : TcpGS GF) (cn : Nat) (γ : GName) :
    Timeless (srvConn hT cn γ) := by
  unfold srvConn; infer_instance

/-- Every connection's server side, their ghost variables' names in the ghost map `γm`. -/
def srvState (hT : TcpGS GF) (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat GName, @ghostMapAuth GF hT.allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ γ ∈ m, srvConn hT cn γ)

/-- The connection `cn`'s ghost variable is `γ`. -/
def srvName (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) : IProp GF :=
  @ghostMapElem GF hT.allG _ _ _ _ γm cn .discard γ

instance srvName_persistent (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Persistent (srvName hT γm cn γ) := by
  unfold srvName; letI := hT.allG; infer_instance

instance srvName_timeless (hT : TcpGS GF) (γm : GName) (cn : Nat) (γ : GName) :
    Timeless (srvName hT γm cn γ) := by
  unfold srvName; letI := hT.allG; infer_instance

/-- The client's end of `cn`: its state at read position `r` (`γr`), its written bytes the first
`w` of `dseq` (`γw`). -/
def cliInv (hT : TcpGS GF) (cn : Nat) (γr γw : GName) : IProp GF :=
  iprop(∃ (st : TcpEnd) (r : Nat) (out : GoString) (f : Bool) (w : Nat),
    tcpEnd hT cn false st r ∗ tcpOut hT cn false out f ∗ half hT γr r ∗ half hT γw w ∗
    ⌜out = dseq.take w⌝)

instance cliInv_timeless (hT : TcpGS GF) (cn : Nat) (γr γw : GName) :
    Timeless (cliInv hT cn γr γw) := by
  unfold cliInv; infer_instance

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What the server gets when it accepts `cn`. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn true TcpEnd.fresh 0 ∗ half G γ ([] : GoString) ∗ srvName G γm cn γ)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- The invariants of the protocol. -/
def dupInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv srvN (srvState G γm))

instance dupInvs_persistent (γm : GName) : Persistent (dupInvs (Gg := Gg) γm) := by
  unfold dupInvs; infer_instance

theorem dupInvs_elim (γm : GName) :
    dupInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv srvN (srvState G γm) := .rfl

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

/-- A dialer's deposit for its new connection `cn`: the connection's server side (nothing
written), its name in the map, and the acceptor end's state for the server. -/
theorem dup_deposit (γm : GName) (cn : Nat) :
    ⊢ inv srvN (srvState (G (Gg := Gg)) γm) -∗ tcpConnAt G cn srvAddr -∗
      tcpFreshEnd G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ ∃ γ, srvName G γm cn γ := by
  iintro #Hinv #Hat Ha
  imod tcpOutLb_nil (G (Gg := Gg)) cn false srvAddr $$ Hat with #Hlb
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "duplex_conns" "duplex_addr" (by decide)
  unfold srvState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFreshEnd
  icases Ha with ⟨Hae, Hao⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its acceptor's written bytes are owned once
    icases BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm) $$ Hconns with ⟨Hc, -⟩
    unfold srvConn
    icases Hc with ⟨%so, %f, Hout, -⟩
    icases tcpOut_excl _ cn true so [] f false $$ Hout Hao with ⟨⟩
  | none =>
    imod half_alloc (Gg := Gg) ([] : GoString) with ⟨%γ, Hh1, Hh2⟩
    imod ghost_map_insert_persist cn γ hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hao Hh1] with -
    · inext
      iexists m.insert cn γ
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold srvConn
      iexists [], false
      iframe Hao
      iframe Hh1
      iexists []
      iframe Hlb
      ipureintro; exact List.nil_prefix
    imodintro
    unfold connProto srvName
    isplitl [Hae Hh2]
    · iexists γ
      iframe Hae Hh2 Hname
    · iexists γ
      iexact Hname

/-- The server side of a connection, from the invariant, by its name: it and the update that puts
it back. -/
theorem srvState_acc (γm : GName) (cn : Nat) (γ : GName) (E : CoPset) (hE : ↑srvN ⊆ E) :
    ⊢ inv srvN (srvState (G (Gg := Gg)) γm) -∗ srvName G γm cn γ -∗
      |={E, E \ ↑srvN}=> srvConn G cn γ ∗ (srvConn G cn γ ={E \ ↑srvN, E}=∗ True) := by
  iintro #Hinv #Hname
  iinv Hinv with Hi Hclose
  unfold srvState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold srvName
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
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn γ, srvConn (G (Gg := Gg)) k v) ⊢
      [∗map] k ↦ v ∈ m, srvConn G k v := by rw [hm]
  imod Hclose $$ [Hm Hback Hc] with -
  · inext
    iexists m
    iframe Hm
    iapply hconv
    iapply Hback $$ Hc
  imodintro
  itrivial

/-- A write by the server on `cn` of bytes `bs` that, after its bytes `so`, are a prefix of the
dialer's (`sR`): its bytes are then `so ++ bs.take k`. The end's state is the server thread's. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : GName) (so bs sR : GoString) (st : TcpEnd)
    (r : Nat) (hbs : so ++ bs <+: sR) :
    ⊢ inv srvN (srvState (G (Gg := Gg)) γm) -∗ srvName G γm cn γ -∗ half G γ so -∗
      tcpOutLb G cn false sR -∗ tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st0 r0 out f, tcpEnd G cn true st0 r0 ∗ tcpOut G cn true out f ∗
        ∀ k ok st', ⌜WriteRes st0 bs k ok st'⌝ -∗ tcpEnd G cn true st' r0 -∗
          tcpOut G cn true (out ++ bs.take k) f ={∅,⊤}=∗
          ∃ st'', ⌜WriteRes st bs k ok st''⌝ ∗ tcpEnd G cn true st'' r ∗
            half G γ (so ++ bs.take k) := by
  iintro #Hinv #Hname Hh #HsR Hend
  imod srvState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold srvConn
  icases Hc with ⟨%so', %f, Hout, Hh', %si, #Hsi, %Hso⟩
  icases half_agree (Gg := Gg) γ so so' $$ Hh Hh' with %Heq
  subst Heq
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, so, f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  imod half_update (Gg := Gg) γ so so (so ++ bs.take k) $$ Hh Hh' with ⟨Hh, Hh'⟩
  imod Hclose $$ [Hout Hh'] with -
  · iexists so ++ bs.take k, f
    iframe Hout
    iframe Hh'
    iexists sR
    iframe HsR
    ipureintro
    exact (List.prefix_append_right_inj so |>.2 (List.take_prefix k bs)).trans hbs
  imodintro
  iexists st'
  iframe Hend Hh
  ipureintro; exact Hwr

/-- The server's close of `cn`: the server side's bytes do not change. -/
theorem server_close_au (γm : GName) (cn : Nat) (γ : GName) (st : TcpEnd) (r : Nat) :
    ⊢ inv srvN (srvState (G (Gg := Gg)) γm) -∗ srvName G γm cn γ -∗ tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn true st r ∗ tcpOut G cn true out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn true st' r -∗ tcpOut G cn true out f' ={∅,⊤}=∗ True := by
  iintro #Hinv #Hname Hend
  imod srvState_acc γm cn γ ⊤ (by simp) $$ Hinv Hname with ⟨Hc, Hclose⟩
  unfold srvConn
  icases Hc with ⟨%so, %f, Hout, Hh, Hlb⟩
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, so, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr - Hout
  imod Hmask
  iapply Hclose
  iexists so, f'
  iframe Hout Hh Hlb

/-- The client's end, allocated from its fresh end: nothing read, nothing written. -/
theorem cliInv_alloc (cn : Nat) :
    tcpFreshEnd (G (Gg := Gg)) cn false ={⊤}=∗ ∃ γr γw, inv cliN (cliInv G cn γr γw) ∗
      half G γr (0 : Nat) ∗ half G γw (0 : Nat) := by
  iintro Hd
  unfold tcpFreshEnd
  icases Hd with ⟨Hend, Hout⟩
  imod half_alloc (Gg := Gg) (0 : Nat) with ⟨%γr, Hr1, Hr2⟩
  imod half_alloc (Gg := Gg) (0 : Nat) with ⟨%γw, Hw1, Hw2⟩
  imod inv_alloc cliN ⊤ (cliInv (G (Gg := Gg)) cn γr γw) $$ [Hend Hout Hr1 Hw1] with #Hinv
  · inext
    unfold cliInv
    iexists TcpEnd.fresh, 0, [], false, 0
    iframe Hend Hout Hr1 Hw1
    ipureintro; rfl
  imodintro
  iexists γr, γw
  iframe Hinv Hr2 Hw2

/-- The reader's accessor of the client's end (`wire.ReadFull`'s): its position is `γr`'s. -/
theorem cli_read_acc (cn : Nat) (γr γw : GName) :
    inv cliN (cliInv (G (Gg := Gg)) cn γr γw) ⊢
      □ (∀ r, half G γr r -∗ |={⊤,∅}=> ∃ st, tcpEnd G cn false st r ∗
        ∀ st' r', tcpEnd G cn false st' r' ={∅,⊤}=∗ half G γr r') := by
  iintro #Hinv
  imodintro
  iintro %r Hr
  iinv Hinv with Hi Hclose
  unfold cliInv
  icases Hi with ⟨%st, %r0, %out, %f, %w, >Hend, >Hout, >Hr', >Hw, >%Hw⟩
  icases half_agree (Gg := Gg) γr r r0 $$ Hr Hr' with %Heq
  subst Heq
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st
  iframe Hend
  iintro %st' %r' Hend
  imod Hmask
  imod half_update (Gg := Gg) γr r r r' $$ Hr Hr' with ⟨Hr, Hr'⟩
  imod Hclose $$ [Hend Hout Hr' Hw] with -
  · inext
    iexists st', r', out, f, w
    iframe Hend Hout Hr' Hw
    ipureintro; exact Hw
  imodintro
  iexact Hr

theorem dseq_take_succ (i : Nat) (hi : i < 4) :
    dseq.take i ++ [W8 (i + 1)] = dseq.take (i + 1) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- The writer's write of the byte `i + 1` after the first `i` of `dseq`: they are then the first
`i + k`. -/
theorem cli_write_au (cn : Nat) (γr γw : GName) (i : Nat) (hi : i < 4) :
    ⊢ inv cliN (cliInv (G (Gg := Gg)) cn γr γw) -∗ half G γw i -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn false st r ∗ tcpOut G cn false out f ∗
        ∀ k ok st', ⌜WriteRes st [W8 (i + 1)] k ok st'⌝ -∗ tcpEnd G cn false st' r -∗
          tcpOut G cn false (out ++ [W8 (i + 1)].take k) f ={∅,⊤}=∗
          half G γw (i + k) ∗ ⌜ok = true → k = 1⌝ := by
  iintro #Hinv Hw
  iinv Hinv with Hi Hclose
  unfold cliInv
  icases Hi with ⟨%st, %r, %out, %f, %w, >Hend, >Hout, >Hr, >Hw', >%Hout⟩
  icases half_agree (Gg := Gg) γw i w $$ Hw Hw' with %Heq
  subst Heq Hout
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, dseq.take i, f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  have hk : k ≤ 1 ∧ (ok = true → k = 1) := by
    rcases Hwr with ⟨-, rfl, rfl, -⟩ | ⟨-, ⟨rfl, rfl, -⟩ | ⟨hk, rfl, -⟩⟩
    · exact ⟨by omega, fun h => by cases h⟩
    · exact ⟨Nat.le_refl _, fun _ => rfl⟩
    · exact ⟨by simp at hk; omega, fun h => by cases h⟩
  imod half_update (Gg := Gg) γw i i (i + k) $$ Hw Hw' with ⟨Hw, Hw'⟩
  imod Hclose $$ [Hend Hout Hr Hw'] with -
  · inext
    iexists st', r, dseq.take i ++ [W8 (i + 1)].take k, f, i + k
    iframe Hend Hout Hr Hw'
    ipureintro
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk.1 with rfl | rfl
    · simp
    · exact dseq_take_succ i hi
  imodintro
  iframe Hw
  ipureintro; exact hk.2

/-- A close of the client's end, by the reader (the writer may still be writing). -/
theorem cli_close_au (cn : Nat) (γr γw : GName) :
    ⊢ inv cliN (cliInv (G (Gg := Gg)) cn γr γw) -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn false st r ∗ tcpOut G cn false out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn false st' r -∗ tcpOut G cn false out f' ={∅,⊤}=∗ True := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  unfold cliInv
  icases Hi with ⟨%st, %r, %out, %f, %w, >Hend, >Hout, >Hr, >Hw, >%Hout⟩
  iapply fupd_mask_intro (by simp)
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr Hend Hout
  imod Hmask
  imod Hclose $$ [Hend Hout Hr Hw] with -
  · inext
    iexists st', r, out, f', w
    iframe Hend Hout Hr Hw
    ipureintro; exact Hout
  imodintro
  itrivial

/-- The client's check: a reply it read (a prefix `resp` of the server's bytes) is a prefix of
`dseq`. -/
theorem client_check (γm : GName) (cn : Nat) (γ γr γw : GName) (resp : GoString) :
    ⊢ inv srvN (srvState (G (Gg := Gg)) γm) -∗ srvName G γm cn γ -∗
      inv cliN (cliInv G cn γr γw) -∗ tcpOutLb G cn true resp ={⊤}=∗ ⌜resp <+: dseq⌝ := by
  iintro #Hsrv #Hname #Hcli #Hresp
  imod srvState_acc γm cn γ ⊤ (by simp) $$ Hsrv Hname with ⟨Hc, Hclose⟩
  unfold srvConn
  icases Hc with ⟨%so, %f, Hout, Hh, %si, #Hsi, %Hso⟩
  icases tcpOut_lb_prefix _ cn true so f resp $$ Hout Hresp with %Hrs
  iinv Hcli with Hi Hclose'
  · exact ndot_mask nroot "duplex_client" "duplex_conns" (by decide)
  unfold cliInv
  icases Hi with ⟨%st, %r, %out, %f', %w, >Hend, >Hout', >Hr, >Hw, >%Hout'⟩
  icases tcpOut_lb_prefix _ cn false out f' si $$ Hout' Hsi with %Hsio
  imod Hclose' $$ [Hend Hout' Hr Hw] with -
  · inext
    iexists st, r, out, f', w
    iframe Hend Hout' Hr Hw
    ipureintro; exact Hout'
  imod Hclose $$ [Hout Hh] with -
  · iexists so, f
    iframe Hout Hh
    iexists si
    iframe Hsi
    ipureintro; exact Hso
  imodintro
  ipureintro
  subst Hout'
  exact Hrs.trans (Hso.trans (Hsio.trans (List.take_prefix w dseq)))

end wps

end github_com.mit_pdos.etcd_grove.examples.net.duplex
end Perennial
