/-
The protocol of `examples/net/echo`, over the TCP extension's resources (`GooseLang/Ext/Tcp`):

* **Per connection** `cn` (to `SrvAddr`), the echo invariant `echoInv cn γ`: the acceptor's
  written bytes `so` (`tcpOut cn true so f`) are a prefix of what the dialer has written (a lower
  bound `si`, `tcpOutLb cn false si`, with `so <+: si`), or nothing (`so = []`) while the server
  still holds the connection's token `γ` (`echoTok`, exclusive: the right to make the one write).
* **The connection's protocol** `connProto cn`, what the server gets when it accepts `cn`: the
  acceptor end's state (`tcpEnd cn true fresh 0`), the token, and the echo invariant.
* **The address** `SrvAddr`'s invariant `addrInv`: its pending set `S` (`tcpPend`), each pending
  connection's protocol. Every dialer (the client, the junk node) deposits its connection's
  protocol there in `Dial`'s atomic step (`dial_au`), and the server takes it in `Accept`'s
  (`accept_au`).

The client's check (`client_check`): the reply it read is a prefix of the server's bytes, which
are a prefix of the client's own: of `"hello"`. The token makes the server's one write start from
nothing (`server_write_au`). Crashes change nothing here: the invariants are global, and a
connection's protocol stays in `addrInv` until a server (of any incarnation) accepts it.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Base
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

/-- The server's address, as a Go string. -/
def srvAddr : GoString := go!"127.0.0.1:7101"

/-- A set as the map `[∗map]` ranges over (`GSet` has no `[∗set]` instance; as raft's
`Protocol.toMap`). -/
@[reducible] def setMap (X : GSet Nat) : GMap Nat Unit := X

theorem setMap_insert (S : GSet Nat) (c : Nat) :
    setMap (S ∪ {[c]}) = (setMap S).insert c () := by
  apply GMap.ext; intro k
  simp only [setMap, GMap.lookup_insert_eq_iff]
  by_cases h : c = k
  · subst h
    have : c ∈ S ∪ {[c]} := (GMap.elem_of_union _ _ _).2 (.inr (GMap.elem_of_singleton_2 c))
    simpa [GMap.elem_of_gset] using this
  · simp only [h, ↓reduceIte]
    have hiff : k ∈ S ∪ {[c]} ↔ k ∈ S := by
      rw [GMap.elem_of_union, GMap.elem_of_singleton]; constructor
      · rintro (h1 | h1)
        · exact h1
        · exact absurd h1.symm h
      · intro h1; exact .inl h1
    simp only [GMap.elem_of_gset] at hiff
    cases h1 : S !! k <;> cases h2 : (S ∪ {[c]}) !! k <;> simp_all

theorem setMap_lookup_none {S : GSet Nat} {c : Nat} (h : c ∉ S) :
    PartialMap.get? (setMap S) c = none := by
  rw [gmap_get?_eq]
  cases hk : (setMap S).lookup c with
  | none => rfl
  | some u => exact absurd ((GMap.elem_of_gset _ _).2 (by simpa using hk)) h

def addrN : Namespace := nroot.@"echo_addr"
def connN (cn : Nat) : Namespace := (nroot.@"echo_conn").@cn

section defs
variable {GF : BundledGFunctors}

/-- The token of a connection: the server's right to make its one write. -/
def echoTok (G : TcpGS GF) (γ : GName) : IProp GF := @token GF G.allG γ

/-- The echo invariant of the connection `cn`. -/
def echoInv (G : TcpGS GF) (cn : Nat) (γ : GName) : IProp GF :=
  iprop(∃ (so : GoString) (f : Bool), tcpOut G cn true so f ∗
    ((echoTok G γ ∗ ∃ si, tcpOutLb G cn false si ∗ ⌜so <+: si⌝) ∨ ⌜so = []⌝))

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The network's ghost state. -/
abbrev G : TcpGS GF := extGlobalGS tcpExt (G := hG.goose_globalGS)

/-- What the server gets when it accepts `cn`. -/
def connProto (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn true TcpEnd.fresh 0 ∗ echoTok G γ ∗ inv (connN cn) (echoInv G cn γ))

/-- The server address's invariant. -/
def addrInv : IProp GF :=
  iprop(∃ S, tcpPend G srvAddr S ∗ [∗map] cn ↦ _u ∈ setMap S, connProto cn)

/-- What a dialer keeps of its new connection: its end, and the connection's echo invariant. -/
def dialRes (cn : Nat) : IProp GF :=
  iprop(tcpFreshEnd G cn false ∗ ∃ γ, inv (connN cn) (echoInv G cn γ))

theorem echoTok_exclusive (γ : GName) :
    echoTok (G (hG := hG)) γ -∗ echoTok G γ -∗ False := by
  unfold echoTok
  letI := (G (hG := hG)).allG
  iintro H1 H2
  iapply token_exclusive $$ H1 H2

/-- A dial of `SrvAddr` that follows the protocol: the dialer sets up its connection's echo
invariant and deposits its protocol (the acceptor end's state, the token, the invariant) in the
address's invariant. -/
theorem dial_au :
    ⊢ inv addrN (addrInv (hG := hG)) -∗ |={⊤,∅}=> ∃ S, tcpPend G srvAddr S ∗
      ∀ cn, ⌜cn ∉ S⌝ -∗ tcpPend G srvAddr (S ∪ {[cn]}) -∗ tcpConnAt G cn srvAddr -∗
        tcpFreshEnd G cn false -∗ tcpFreshEnd G cn true ={∅,⊤}=∗ dialRes cn := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨%S, >Hpend, Hprotos⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend #Hat Hd Ha
  imod Hmask
  unfold tcpFreshEnd
  icases Ha with ⟨Hae, Hao⟩
  letI := (G (hG := hG)).allG
  imod token_alloc (GF := GF) with ⟨%γ, Htok⟩
  imod inv_alloc (connN cn) _ (echoInv G cn γ) $$ [Hao] with #Hci
  · inext
    unfold echoInv
    iexists [], false
    iframe Hao
    iright
    ipureintro; rfl
  imod Hclose $$ [Hpend Hprotos Hae Htok] with -
  · inext
    iexists S ∪ {[cn]}
    iframe Hpend
    rw [setMap_insert]
    iapply (BigSepM.bigSepM_insert (setMap_lookup_none HcS)).2
    iframe Hprotos
    unfold connProto
    iexists γ
    iframe Hae Hci
    unfold echoTok
    iexact Htok
  imodintro
  unfold dialRes tcpFreshEnd
  iframe Hd
  iexists γ
  iexact Hci

theorem setMap_delete (S : GSet Nat) (c : Nat) :
    PartialMap.delete (setMap S) c = setMap (S \ {[c]}) := by
  apply GMap.ext; intro k
  show (GMap.delete c S).lookup k = (S \ {[c]}).lookup k
  by_cases h : c = k
  · subst h
    rw [GMap.lookup_delete]
    have : c ∉ S \ {[c]} := by
      rw [GMap.elem_of_difference]; intro h1; exact h1.2 (GMap.elem_of_singleton_2 c)
    rw [GMap.elem_of_gset] at this
    cases hk : (S \ {[c]}).lookup c with
    | none => rfl
    | some u => exact absurd (by simpa using hk) this
  · rw [GMap.lookup_delete_ne _ h]
    have hiff : k ∈ S \ {[c]} ↔ k ∈ S := by
      rw [GMap.elem_of_difference, GMap.not_elem_of_singleton]
      exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, Ne.symm h⟩⟩
    simp only [GMap.elem_of_gset] at hiff
    cases h1 : S !! k <;> cases h2 : (S \ {[c]}) !! k <;> simp_all

/-- An accept at `SrvAddr`: the server takes the connection's protocol out of the address's
invariant. -/
theorem accept_au :
    ⊢ inv addrN (addrInv (hG := hG)) -∗ |={⊤,∅}=> ∃ S, tcpPend G srvAddr S ∗
      ∀ cn, ⌜cn ∈ S⌝ -∗ tcpPend G srvAddr (S \ {[cn]}) ={∅,⊤}=∗ connProto cn := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨%S, >Hpend, Hprotos⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend
  imod Hmask
  have hl : PartialMap.get? (setMap S) cn = some () := by
    rw [gmap_get?_eq]; exact (GMap.elem_of_gset _ _).1 HcS
  icases (BigSepM.bigSepM_delete hl).1 $$ Hprotos with ⟨Hp, Hprotos⟩
  rw [setMap_delete]
  imod Hclose $$ [Hpend Hprotos] with -
  · inext
    iexists S \ {[cn]}
    iframe Hpend Hprotos
  imodintro
  iexact Hp

/-- The server's one write on `cn`, of bytes `bs` that are a prefix of the dialer's (`si`), with
the connection's token: the echo invariant's bytes were nothing, and are a prefix of `si` after. -/
theorem server_write_au (cn : Nat) (γ : GName) (bs si : GoString) (st : TcpEnd) (r : Nat)
    (hbs : bs <+: si) :
    ⊢ inv (connN cn) (echoInv (G (hG := hG)) cn γ) -∗ echoTok G γ -∗ tcpOutLb G cn false si -∗
      tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn true st r ∗ tcpOut G cn true out f ∗
        ∀ k ok st', ⌜WriteRes st bs k ok st'⌝ -∗ tcpEnd G cn true st' r -∗
          tcpOut G cn true (out ++ bs.take k) f ={∅,⊤}=∗ ∃ st', tcpEnd G cn true st' r := by
  iintro #Hci Htok #Hsi Hend
  iinv Hci with Hi Hclose
  unfold echoInv
  icases Hi with ⟨%so, %f, >Hout, >Hcase⟩
  icases Hcase with (⟨Htok', -⟩ | %Hso)
  · icases echoTok_exclusive γ $$ Htok Htok' with ⟨⟩
  subst Hso
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, [], f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  imod Hclose $$ [Hout Htok] with -
  · inext
    iexists [] ++ bs.take k, f
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

/-- The server's close of `cn`: the echo invariant's bytes do not change. -/
theorem server_close_au (cn : Nat) (γ : GName) (st : TcpEnd) (r : Nat) :
    ⊢ inv (connN cn) (echoInv (G (hG := hG)) cn γ) -∗ tcpEnd G cn true st r -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn true st r ∗ tcpOut G cn true out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn true st' r -∗ tcpOut G cn true out f' ={∅,⊤}=∗ True := by
  iintro #Hci Hend
  iinv Hci with Hi Hclose
  unfold echoInv
  icases Hi with ⟨%so, %f, >Hout, >Hcase⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, so, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr - Hout
  imod Hmask
  imod Hclose $$ [Hout Hcase] with -
  · inext
    iexists so, f'
    iframe Hout Hcase
  imodintro
  itrivial

/-- The client's check: a reply it read (`resp`, a prefix of the server's bytes) is a prefix of
the client's own bytes `out`. -/
theorem client_check (cn : Nat) (γ : GName) (out : GoString) (f : Bool) (resp : GoString) :
    ⊢ inv (connN cn) (echoInv (G (hG := hG)) cn γ) -∗ tcpOut G cn false out f -∗
      tcpOutLb G cn true resp ={⊤}=∗ ⌜resp <+: out⌝ ∗ tcpOut G cn false out f := by
  iintro #Hci Hmy #Hresp
  iinv Hci with Hi Hclose
  unfold echoInv
  icases Hi with ⟨%so, %f', >Hout, >Hcase⟩
  icases tcpOut_lb_prefix _ cn true so f' resp $$ Hout Hresp with %Hrs
  ihave %Hpre : ⌜resp <+: out⌝ $$ [Hcase]
  · icases Hcase with (⟨-, %si, #Hsi, %Hso⟩ | %Hso)
    · icases tcpOut_lb_prefix _ cn false out f si $$ Hmy Hsi with %Hsio
      ipureintro; exact Hrs.trans (Hso.trans Hsio)
    · subst Hso
      ipureintro
      rw [List.prefix_nil.1 Hrs]
      exact List.nil_prefix
  imod Hclose $$ [Hout Hcase] with -
  · inext
    iexists so, f'
    iframe Hout Hcase
  imodintro
  iframe Hmy
  ipureintro; exact Hpre

end wps

end github_com.mit_pdos.etcd_grove.examples.net.echo
end Perennial
