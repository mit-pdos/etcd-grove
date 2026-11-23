/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecQuorum.lean`, run `rabia-r1wake-1`.)

The executor's reads of a frozen round (`n - f` counted messages): `RecvBCMsgsMajT/MajV` of a
frozen round of states or votes are the majority of its values; `RecvProposalsMajT/MajV` of the
frozen round 0 are the first of its proposals' sorted tallies (`propHead`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecRead

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section reads
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS]

instance factJust_persistent (γ : Names) (key : FKey) (val : FVal) :
    Persistent (factJust (GF := GF) γ key val) := by
  unfold factJust; infer_instance

instance nextJust_persistent (γ : Names) (k t : Nat) (pv : PrivSt) :
    Persistent (nextJust (GF := GF) γ k t pv) := by
  unfold nextJust; split
  · infer_instance
  · split <;> infer_instance

instance frozenVals_persistent (γl : SrvNames) (γc : ConsNames) (t ρ : Nat) (vs : List Nat) :
    Persistent (frozenVals (GF := GF) cf γl γc t ρ vs) := by
  unfold frozenVals; infer_instance

instance majPropW_persistent (γ : Names) (t : Nat) (id : ObjId) :
    Persistent (majPropW (GF := GF) γ cf t id) := by
  unfold majPropW; infer_instance

instance decJust_persistent (γ : Names) (t : Nat) (d : DVal) :
    Persistent (decJust (GF := GF) γ cf t d) := by
  unfold decJust; infer_instance

instance bitEvW_persistent (γ : Names) (t b : Nat) :
    Persistent (bitEvW (GF := GF) γ cf t b) := by
  unfold bitEvW; infer_instance

/-- The values of a frozen round. -/
abbrev valsOf (T : List Ent) : List Nat := T.map (fun e => e.2.2.2.value.toNat)

/-- The proposals of a frozen round. -/
abbrev objsOf (T : List Ent) : List ObjV := T.filterMap (fun e => e.2.2.2.obj)

/-- `RecvBCMsgsMajT(p, r)` of a frozen round. -/
theorem wp_bcMajT_frozen (hspec : Slot.RecvBCMsgsMajT.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (p r : w32) (hr : r = 1 ∨ r = 2) (hpr : (r.toNat = 1 ∧ 1 ≤ p.toNat) ∨ r.toNat = 2)
    (ρ : Nat) (hρ : ρ = 2 * p.toNat + r.toNat - 1)
    (ents0 : List Ent) (h2 : (tally ents0 ρ).length = cf.q) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ monoListLbOwn (entName γl γc s) ents0 -∗
        Φ #(W64 (majT (valsOf (tally ents0 ρ)) : Nat)) -∗
      WP (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvBCMsgsMajT"))
        (Val #p)) (Val #r)) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi #Hlb HΦ
  iapply wp_RecvBCMsgsMajT_inv hspec γ k γl γc s e he p r hr iprop(True)
    (fun st => iprop(⌜(st.counts p.toNat r.toNat).majT =
      majT (valsOf (tally ents0 ρ))⌝))
  iframe Hp Hs Hi
  isplitr
  · itrivial
  isplitr
  · iintro %st Hg -
    ihave ⟨Hg, %h⟩ := slotGhost_tally γ k γl γc s st ents0 _ h2 $$ [Hg Hlb]
    · iframe Hg Hlb
    obtain ⟨ents, ht, he'⟩ := h
    imodintro
    iframe Hg
    ipureintro
    rw [(ht.majT_eq hpr).1, ← hρ, he']
  · iintro %st %h
    rw [h]; iexact HΦ

/-- `RecvBCMsgsMajV(p, r)` of a frozen round. -/
theorem wp_bcMajV_frozen (hspec : Slot.RecvBCMsgsMajV.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (p r : w32) (hr : r = 1 ∨ r = 2) (hpr : (r.toNat = 1 ∧ 1 ≤ p.toNat) ∨ r.toNat = 2)
    (ρ : Nat) (hρ : ρ = 2 * p.toNat + r.toNat - 1)
    (ents0 : List Ent) (h2 : (tally ents0 ρ).length = cf.q) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ monoListLbOwn (entName γl γc s) ents0 -∗
        Φ #(W32 (majV (valsOf (tally ents0 ρ)) : Nat)) -∗
      WP (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvBCMsgsMajV"))
        (Val #p)) (Val #r)) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi #Hlb HΦ
  iapply wp_RecvBCMsgsMajV_inv hspec γ k γl γc s e he p r hr iprop(True)
    (fun st => iprop(⌜(st.counts p.toNat r.toNat).majV =
      majV (valsOf (tally ents0 ρ))⌝))
  iframe Hp Hs Hi
  isplitr
  · itrivial
  isplitr
  · iintro %st Hg -
    ihave ⟨Hg, %h⟩ := slotGhost_tally γ k γl γc s st ents0 _ h2 $$ [Hg Hlb]
    · iframe Hg Hlb
    obtain ⟨ents, ht, he'⟩ := h
    imodintro
    iframe Hg
    ipureintro
    rw [(ht.majT_eq hpr).2, ← hρ, he']
  · iintro %st %h
    rw [h]; iexact HΦ

theorem slotGhost_sort (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (st : SlotSt) :
    slotGhost (GF := GF) γ cf k γl γc s st ⊢
      slotGhost γ cf k γl γc s { st with props := sortProps st.props } := by
  unfold slotGhost
  iintro ⟨%ents, %ql', %pend, %exd, %dl, %rl, He, Hql, Hp, Hx, Hdl, Hrl, Hents, %hok⟩
  iexists ents, ql', pend, exd, dl, rl
  iframe
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hok
  exact ⟨h1.sort, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- `RecvProposalsMajT()` of the frozen round 0: the count of its first sorted tally. -/
theorem wp_propMajT_frozen (hspec : Slot.RecvProposalsMajT.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (ents0 : List Ent) (h2 : (tally ents0 0).length = cf.q)
    (hne : objsOf (tally ents0 0) ≠ []) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ monoListLbOwn (entName γl γc s) ents0 -∗
        Φ #(W64 (((propHead (objsOf (tally ents0 0))).map (·.2)).getD 0 : Nat)) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajT"))
        (Val #())) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi #Hlb HΦ
  iapply wp_RecvProposalsMajT_inv hspec γ k γl γc s e he iprop(True)
    (fun st => iprop(⌜((sortProps st.props).head?.map (·.2)).getD 0 =
      ((propHead (objsOf (tally ents0 0))).map (·.2)).getD 0⌝))
  iframe Hp Hs Hi
  isplitr
  · itrivial
  isplitr
  · imodintro
    iintro %st Hg -
    ihave ⟨Hg, %h⟩ := slotGhost_tally γ k γl γc s st ents0 _ h2 $$ [Hg Hlb]
    · iframe Hg Hlb
    obtain ⟨ents, ht, he'⟩ := h
    iframe Hg
    ipureintro
    exact (ht.props_head (by rw [he']; exact hne)).1
  isplitr
  · iintro %st Hg -
    ihave ⟨Hg, %h⟩ := slotGhost_tally γ k γl γc s st ents0 _ h2 $$ [Hg Hlb]
    · iframe Hg Hlb
    obtain ⟨ents, ht, he'⟩ := h
    ihave Hg := slotGhost_sort γ k γl γc s st $$ Hg
    imodintro
    iframe Hg
    ipureintro
    rw [ht.sort_eq, he']; rfl
  · iintro %st %n %hn %h
    rw [hn, h]; iexact HΦ

/-- `RecvProposalsMajV()` of the frozen round 0: the object of its first sorted tally. -/
theorem wp_propMajV_frozen (hspec : Slot.RecvProposalsMajV.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (ents0 : List Ent) (h2 : (tally ents0 0).length = cf.q)
    (hne : objsOf (tally ents0 0) ≠ []) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ monoListLbOwn (entName γl γc s) ents0 -∗
        (∀ v : ConsensusObj, objRep v ((propHead (objsOf (tally ents0 0))).map (·.1)).get! -∗
          Φ #v) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajV"))
        (Val #())) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi #Hlb HΦ
  iapply wp_RecvProposalsMajV_inv hspec γ k γl γc s e he iprop(True)
    (fun st => iprop(⌜((sortProps st.props).head?.map (·.1)).get! =
      ((propHead (objsOf (tally ents0 0))).map (·.1)).get!⌝))
  iframe Hp Hs Hi
  isplitr
  · itrivial
  isplitr
  · imodintro
    iintro %st Hg -
    ihave ⟨Hg, %h⟩ := slotGhost_tally γ k γl γc s st ents0 _ h2 $$ [Hg Hlb]
    · iframe Hg Hlb
    obtain ⟨ents, ht, he'⟩ := h
    iframe Hg
    ipureintro
    exact (ht.props_head (by rw [he']; exact hne)).1
  isplitr
  · iintro %st Hg -
    ihave ⟨Hg, %h⟩ := slotGhost_tally γ k γl γc s st ents0 _ h2 $$ [Hg Hlb]
    · iframe Hg Hlb
    obtain ⟨ents, ht, he'⟩ := h
    ihave Hg := slotGhost_sort γ k γl γc s st $$ Hg
    imodintro
    iframe Hg
    ipureintro
    rw [ht.sort_eq, he']; rfl
  · iintro %st %v Hv %h
    rw [h]; iapply HΦ $$ Hv

end reads

end Perennial.rabia.roles.server.layers.consensus
