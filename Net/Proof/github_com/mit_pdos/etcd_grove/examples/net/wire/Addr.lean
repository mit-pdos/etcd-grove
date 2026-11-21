/-
A per-address protocol, for the proofs of `examples/net/`: the invariant of a plan address `a`
(`addrInv a Φ`) holds `a`'s pending set (`netPend`) and, for each connection `cn` pending there,
the resources `Φ cn` its dialer deposited (`Φ` timeless). A dial that deposits `Φ cn`
(`dial_au`, `dial_both_au`; a dial that fails but leaves its connection pending, abandoned, deposits
too) and an accept that takes it (`accept_au`) are the atomic updates of `net.Dial` and
`Listener.Accept` (`Net/Spec/net/`). (`setMap`, sets as the maps `[∗map]` ranges over, is in
`GooseLang/Ext/Net/Stream.lean`.)
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base
public import GooseLang.Ext.Net.Stream

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The network's ghost state. -/
abbrev G : NetGS GF := extGlobalGS netExt (G := Gg)

/-- The invariant of the address `a`: its listening token (`netLisTok`, so that a node that
listens at `a` takes it at its `Listen`'s step, `listen_au`, after every restart), and its pending
connections, each with its dialer's deposit `Φ cn`. -/
def addrInv (a : GoString) (Φ : Nat → IProp GF) : IProp GF :=
  iprop(netLisTok G a ∗ ∃ S, netPend G a S ∗ [∗map] cn ↦ _u ∈ setMap S, Φ cn)

/-- A dial of `a` whose dialer deposits `Φ cn` (made, at the address's invariant's mask, from the
new connection's acceptor end, `mk`) and keeps its own end and `R cn`; a dial that fails leaving
the connection abandoned (D16) deposits `Φ cn` all the same (an acceptor may take it) and keeps
nothing. The update of `net.Dial` with `Qfail := True`. -/
theorem dial_au (N : Namespace) (a : GoString) (Φ R : Nat → IProp GF) [∀ cn, Timeless (Φ cn)] :
    ⊢ inv N (addrInv a Φ) -∗
      (∀ cn, netConnAt G cn a -∗ netFresh G cn true ={⊤ \ ↑N}=∗ Φ cn ∗ R cn) -∗
      |={⊤,∅}=> ∃ S, netPend G a S ∗
        ∀ cn, ⌜cn ∉ S⌝ -∗ netPend G a (S ∪ {[cn]}) -∗ netConnAt G cn a -∗
          netFresh G cn true -∗
          ((netFresh G cn false ={∅,⊤}=∗ netFresh G cn false ∗ R cn) ∧
           (netEnd G cn false { NetEnd.fresh with closed := true } -∗
            netDir G cn false ⟨[], .fin⟩ ={∅,⊤}=∗ True)) := by
  iintro #Hinv Hmk
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨>Htk, %S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend #Hat Ha
  isplit
  · iintro Hd
    imod Hmask
    imod Hmk $$ %cn Hat Ha with ⟨HΦ, HR⟩
    imod Hclose $$ [Htk Hpend Hdeps HΦ] with -
    · inext
      iframe Htk
      iexists S ∪ {[cn]}
      iframe Hpend
      rw [setMap_insert]
      iapply (BigSepM.bigSepM_insert (setMap_lookup_none HcS)).2
      iframe Hdeps HΦ
    imodintro
    iframe Hd HR
  · iintro - -
    imod Hmask
    imod Hmk $$ %cn Hat Ha with ⟨HΦ, -⟩
    imod Hclose $$ [Htk Hpend Hdeps HΦ] with -
    · inext
      iframe Htk
      iexists S ∪ {[cn]}
      iframe Hpend
      rw [setMap_insert]
      iapply (BigSepM.bigSepM_insert (setMap_lookup_none HcS)).2
      iframe Hdeps HΦ
    imodintro
    itrivial

/-- A dial of `a` whose dialer deposits `Φ cn`, made from both new ends (the dialer's too: so the
deposit can tie the dialer's direction to the acceptor's, as a per-connection protocol's state
does), and keeps `R cn`; a dial that fails leaving the connection abandoned (D16) deposits `Φ cn`
made from the acceptor's fresh end and the dialer's closed end and shut, empty direction
(`mkAb`), and keeps nothing. The update of `net.Dial` with `Qfail := True`. -/
theorem dial_both_au (N : Namespace) (a : GoString) (Φ R : Nat → IProp GF)
    [∀ cn, Timeless (Φ cn)] :
    ⊢ inv N (addrInv a Φ) -∗
      (∀ cn, netConnAt G cn a -∗ netFresh G cn false -∗ netFresh G cn true ={⊤ \ ↑N}=∗
        Φ cn ∗ R cn) -∗
      (∀ cn, netConnAt G cn a -∗ netEnd G cn false { NetEnd.fresh with closed := true } -∗
        netDir G cn false ⟨[], .fin⟩ -∗ netFresh G cn true ={⊤ \ ↑N}=∗ Φ cn) -∗
      |={⊤,∅}=> ∃ S, netPend G a S ∗
        ∀ cn, ⌜cn ∉ S⌝ -∗ netPend G a (S ∪ {[cn]}) -∗ netConnAt G cn a -∗
          netFresh G cn true -∗
          ((netFresh G cn false ={∅,⊤}=∗ R cn) ∧
           (netEnd G cn false { NetEnd.fresh with closed := true } -∗
            netDir G cn false ⟨[], .fin⟩ ={∅,⊤}=∗ True)) := by
  iintro #Hinv Hmk HmkAb
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨>Htk, %S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend #Hat Ha
  isplit
  · iintro Hd
    imod Hmask
    imod Hmk $$ %cn Hat Hd Ha with ⟨HΦ, HR⟩
    imod Hclose $$ [Htk Hpend Hdeps HΦ] with -
    · inext
      iframe Htk
      iexists S ∪ {[cn]}
      iframe Hpend
      rw [setMap_insert]
      iapply (BigSepM.bigSepM_insert (setMap_lookup_none HcS)).2
      iframe Hdeps HΦ
    imodintro
    iexact HR
  · iintro He Hd
    imod Hmask
    imod HmkAb $$ %cn Hat He Hd Ha with HΦ
    imod Hclose $$ [Htk Hpend Hdeps HΦ] with -
    · inext
      iframe Htk
      iexists S ∪ {[cn]}
      iframe Hpend
      rw [setMap_insert]
      iapply (BigSepM.bigSepM_insert (setMap_lookup_none HcS)).2
      iframe Hdeps HΦ
    imodintro
    itrivial

/-- An accept at `a`: the acceptor takes the connection's deposit. -/
theorem accept_au (N : Namespace) (a : GoString) (Φ : Nat → IProp GF) [∀ cn, Timeless (Φ cn)] :
    ⊢ inv N (addrInv a Φ) -∗ |={⊤,∅}=> ∃ S, netPend G a S ∗
      ∀ cn, ⌜cn ∈ S⌝ -∗ netPend G a (S \ {[cn]}) ={∅,⊤}=∗ Φ cn := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨>Htk, %S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend
  imod Hmask
  have hl : PartialMap.get? (setMap S) cn = some () := by
    rw [gmap_get?_eq]; exact (GMap.elem_of_gset _ _).1 HcS
  icases (BigSepM.bigSepM_delete hl).1 $$ Hdeps with ⟨Hp, Hdeps⟩
  rw [setMap_delete]
  imod Hclose $$ [Htk Hpend Hdeps] with -
  · inext
    iframe Htk
    iexists S \ {[cn]}
    iframe Hpend Hdeps
  imodintro
  iexact Hp

/-- An accept at `a` on a listener the thread owns (`netLis hL l a o`): the update of
`net.Listener.Accept`, which opens the address's invariant; a failure closes it unchanged and hands
the listener back, a connection hands back the listener and the connection's deposit. -/
theorem accept_lis_au (N : Namespace) (a : GoString) (Φ : Nat → IProp GF) [∀ cn, Timeless (Φ cn)]
    (hL : NetLocalGS GF) (l : w64) (o : Bool) :
    ⊢ inv N (addrInv a Φ) -∗ netLis hL l a o -∗
      |={⊤,∅}=> ∃ o' S, netLis hL l a o' ∗ netPend G a S ∗
        ((netLis hL l a o' -∗ netPend G a S ={∅,⊤}=∗ netLis hL l a o) ∧
          (⌜o' = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis hL l a o' -∗ netPend G a (S \ {[cn]}) -∗
            netConnAt G cn a ={∅,⊤}=∗ netLis hL l a o ∗ Φ cn)) := by
  iintro #Hinv Hl
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨>Htk, %S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists o, S
  iframe Hl Hpend
  isplit
  · iintro Hl Hpend
    imod Hmask
    imod Hclose $$ [Htk Hpend Hdeps] with -
    · inext
      iframe Htk
      iexists S
      iframe Hpend Hdeps
    imodintro
    iexact Hl
  · iintro %ho %cn %HcS Hl Hpend #Hat
    imod Hmask
    have hl : PartialMap.get? (setMap S) cn = some () := by
      rw [gmap_get?_eq]; exact (GMap.elem_of_gset _ _).1 HcS
    icases (BigSepM.bigSepM_delete hl).1 $$ Hdeps with ⟨Hp, Hdeps⟩
    rw [setMap_delete]
    imod Hclose $$ [Htk Hpend Hdeps] with -
    · inext
      iframe Htk
      iexists S \ {[cn]}
      iframe Hpend Hdeps
    imodintro
    iframe Hl Hp

/-- The address's invariant of a fresh network: its listening token, nothing pending. -/
theorem addrInv_alloc (N : Namespace) (a : GoString) (Φ : Nat → IProp GF) :
    netPend G a ∅ -∗ netLisTok G a ={⊤}=∗ inv N (addrInv a Φ) := by
  iintro Hpend Htk
  iapply inv_alloc
  inext
  unfold addrInv
  iframe Htk
  iexists ∅
  iframe Hpend
  iapply BigSepM.bigSepM_empty.2
  iempintro


/-- `Listen` of `a` by any node that knows the address's invariant: the update of `net.Listen`
that gives the listening token at the step and puts it back. -/
theorem listen_au (N : Namespace) (a : GoString) (Φ : Nat → IProp GF) :
    ⊢ inv N (addrInv a Φ) -∗
      |={⊤,∅}=> netLisTok G a ∗ (netLisTok G a ={∅,⊤}=∗ True) := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨>Htk, Hrest⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iframe Htk
  iintro Htk
  imod Hmask
  imod Hclose $$ [Htk Hrest] with -
  · inext; iframe Htk Hrest
  imodintro
  itrivial

end wps

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
