/-
Laws of `fwCore` used inside the replica package (its sealed body is the package's): with the
phase of a deposit known, a lock holder gets the deposited part.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Replica

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

theorem fwRO_def (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    fwRO (GF := GF) γ r id L p ⊢ fwRODef γ r id L p := by
  rw [fwRO_unseal]

theorem fwListening_def (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) :
    fwListening (GF := GF) γ r id L ⊢ fwListeningDef γ r id L := by
  rw [fwListening_unseal]

theorem fwStart_def (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) :
    fwStart (GF := GF) γ r id L p ⊢ fwStartDef γ r id L p := by
  rw [fwStart_unseal]

/-- A replica's own address carries the replica protocols. -/
theorem fwRO_addrProto (γ : EpNames) (L : List GoString) (i : Nat) (hi : i < L.length) :
    listFinal (GF := GF) γ L -∗ clientInvs γ -∗
      addrProto (L.getD i []) (repDialP γ (L.getD i [])) (repAccP γ (L.getD i [])) := by
  iintro #Hlf #Hci
  unfold listFinal finalListOk
  icases Hlf with ⟨-, %Hp⟩
  unfold clientInvs
  icases Hci with ⟨#Hs, -⟩
  have hmem : L.getD i [] ∈ replicaAddrs := by
    apply Hp.subset
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  iapply (BigSepL.bigSepL_mem hmem) $$ Hs

theorem fwFrozen_epaxos (γ : EpNames) (r : Loc) (id : Nat) (p : FwPtrs) :
    fwFrozen γ r id p ⊢
      isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos := by
  rw [fwFrozen_unseal]; unfold fwFrozenDef
  iintro ⟨-, -, -, #H⟩
  iexact H

theorem isReplicaFw_def (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) : isReplicaFw γ r id L p Rext ⊢ isReplicaFwDef γ r id L p Rext := by
  rw [isReplicaFw_unseal]

/-- After phase 1, a lock holder gets the peer cells (and gives them back). -/
theorem fwCore_peers_acc (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) (E : CoPset)
    (hE : ↑fwDepN ⊆ E) :
    ⊢ fwPhase1 (GF := GF) γ id -∗ fwCore γ id L p -∗ £ 1 ={E}=∗
      fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma ∗
      (fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma -∗ fwCore γ id L p) := by
  rw [fwCore_unseal]; unfold fwCoreDef fwPhase1
  iintro ⟨%ns', #Hn', #Hd⟩ ⟨%ns, %CWm, %CW, %RT, %sm, #Hn, #Hi1, #Hi2, Hp, Hr, Hrest⟩ Hlc
  ihave %Heq := fwNames_agree $$ Hn Hn'
  subst Heq
  ihave Hp : fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma ∨ token ns.1 $$ [Hp]
  · icases Hp with (Hp | ⟨Hk, -⟩)
    · ileft; iexact Hp
    · iright; iexact Hk
  imod dep_take _ _ _ E hE $$ Hi1 Hd Hp Hlc with Hp
  imodintro
  iframe Hp
  iintro Hp
  iexists ns, CWm, CW, RT, sm
  iframe
  iframe #

/-- After phase 2, a lock holder gets the readers slice (and gives it back). -/
theorem fwCore_readers_acc (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) (E : CoPset)
    (hE : ↑fwDepN ⊆ E) :
    ⊢ fwPhase2 (GF := GF) γ id -∗ fwCore γ id L p -∗ £ 1 ={E}=∗
      fwReaders L p.readers ∗ (fwReaders L p.readers -∗ fwCore γ id L p) := by
  rw [fwCore_unseal]; unfold fwCoreDef fwPhase2
  iintro ⟨%ns', #Hn', #Hd⟩ ⟨%ns, %CWm, %CW, %RT, %sm, #Hn, #Hi1, #Hi2, Hp, Hr, Hrest⟩ Hlc
  ihave %Heq := fwNames_agree $$ Hn Hn'
  subst Heq
  imod dep_take _ _ _ E hE $$ Hi2 Hd Hr Hlc with Hr
  imodintro
  iframe Hr
  iintro Hr
  iexists ns, CWm, CW, RT, sm
  iframe
  iframe #

/-- After both phases, a lock holder gets the peer cells and the readers slice. -/
theorem fwCore_acc (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) (E : CoPset)
    (hE : ↑fwDepN ⊆ E) :
    ⊢ fwPhase1 (GF := GF) γ id -∗ fwPhase2 γ id -∗ fwCore γ id L p -∗ £ 1 -∗ £ 1 ={E}=∗
      fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma ∗ fwReaders L p.readers ∗
      (fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma -∗ fwReaders L p.readers -∗
        fwCore γ id L p) := by
  rw [fwCore_unseal]; unfold fwCoreDef fwPhase1 fwPhase2
  iintro ⟨%ns1, #Hn1, #Hd1⟩ ⟨%ns2, #Hn2, #Hd2⟩
    ⟨%ns, %CWm, %CW, %RT, %sm, #Hn, #Hi1, #Hi2, Hp, Hr, Hrest⟩ Hlc1 Hlc2
  ihave %Heq1 := fwNames_agree $$ Hn Hn1
  ihave %Heq2 := fwNames_agree $$ Hn Hn2
  subst Heq1 Heq2
  ihave Hp : fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma ∨ token ns.1 $$ [Hp]
  · icases Hp with (Hp | ⟨Hk, -⟩)
    · ileft; iexact Hp
    · iright; iexact Hk
  imod dep_take _ _ _ E hE $$ Hi1 Hd1 Hp Hlc1 with Hp
  imod dep_take _ _ _ E hE $$ Hi2 Hd2 Hr Hlc2 with Hr
  imodintro
  iframe Hp Hr
  iintro Hp Hr
  iexists ns, CWm, CW, RT, sm
  iframe
  iframe #

theorem getD_set_ne {A : Type} (l : List A) (d k : Nat) (x y : A) (h : k ≠ d) :
    (l.set d x).getD k y = l.getD k y := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem set_getD_self {A : Type} (l : List A) (i : Nat) (x : A) (h : i < l.length) :
    l.set i (l.getD i x) = l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; simp

/-- Open peer `d`'s slot in the peer cells, to update its cells and slot. -/
theorem fwPeers_open (γ : EpNames) (id : Nat) (L : List GoString)
    (peers writers alive lat ew : GoSlice) (d : Nat) (hd : d < L.length) (hdi : d ≠ id) :
    fwPeers (GF := GF) γ id L peers writers alive lat ew ⊢
      ∃ (cs : List GoInterface) (ws : List Loc) (als : List Bool) (ls : List w64),
        peers ↦* cs ∗ writers ↦* ws ∗ alive ↦* als ∗ lat ↦* ls ∗
        ⌜cs.length = L.length ∧ ws.length = L.length ∧ als.length = L.length ∧
          ls.length = L.length⌝ ∗
        peerSlotX γ id L ew d (cs.getD d interface.nil) (ws.getD d null) ∗
        (∀ (c' : GoInterface) (w' : Loc) (a' : Bool),
          peers ↦* cs.set d c' -∗ writers ↦* ws.set d w' -∗ alive ↦* als.set d a' -∗
          lat ↦* ls -∗ peerSlotX γ id L ew d c' w' -∗ fwPeers γ id L peers writers alive lat ew) := by
  unfold fwPeers
  iintro ⟨%cs, %ws, %als, %ls, Hp, Hw, Ha, Hl, %Hlen, Hs⟩
  have hlk : (List.range L.length)[d]? = some d := by simp [hd]
  icases BigSepL.bigSepL_lookup_acc_impl hlk $$ Hs with ⟨Hd, Hs⟩
  simp only [hdi, ite_false]
  iexists cs, ws, als, ls
  iframe Hp Hw Ha Hl Hd
  isplitr
  · ipureintro; exact Hlen
  iintro %c' %w' %a' Hp Hw Ha Hl Hd
  iexists cs.set d c', ws.set d w', als.set d a', ls
  iframe Hp Hw Ha Hl
  isplitr
  · ipureintro; simp [Hlen]
  iapply Hs
  · imodintro
    iintro %k %y %hk %hkd H
    have hy : y = k := by
      obtain ⟨_, h2⟩ := List.getElem?_eq_some_iff.mp hk
      simp only [List.getElem_range] at h2; exact h2.symm
    subst hy
    by_cases hki : y = id
    · simp only [hki, ite_true]; itrivial
    · simp only [hki, ite_false, getD_set_ne _ _ _ _ _ hkd]
      iexact H
  · simp only [hdi, ite_false, List.getD_eq_getElem?_getD]
    rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega)]
    simp only [Option.getD_some]
    iexact Hd

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
