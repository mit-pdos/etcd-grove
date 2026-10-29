/-
(U8 v2, 2026-10-29) **How raft's view of its storage moves** (`InvStorage.lean`'s `ownStorage`): what
were the contract's laws until U8 v2 (`Hhandout`, `Habsorb`, `Hfloor`, the snapshot loan) are now
lemmas about the ranges raft holds (candidate 17 rev 3 §3-§4):

- `ownStorage_handout`: a `Ready` with entries from `k` hands out the log from `k` on, with the end
  (`appendRight`);
- `ownStorage_absorb`: `Advance` takes the batch back as a frozen prefix `a` and an owned rest `b`
  (`appendReceipt`); raft freezes its own part below `k` when `a ≠ []` (it is committed and
  delivered), so its frozen prefix stays one range;
- `ownStorage_floor`: raising the floor publishes an applied lower bound (`storFloor`, the API's
  `nodeAppliedLb`);
- `ownStorage_lend` / `ownStorage_absorb_snap`: a snapshot `Ready` hands out everything above the
  frozen prefix with the end and `snapGiven` (`storGiven`); its `Advance` returns the compaction point
  at the snapshot, the dummy there and the log after it;
- `ownStorage_freeze`: freezing the view's log up to `j` (a `Ready`'s committed entries below `k`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvStorageRead

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

theorem drop_split {α : Type _} (L : List α) (m k : Nat) (h : m ≤ k) (hk : k ≤ L.length) :
    L.drop m = (L.take k).drop m ++ L.drop k := by
  calc L.drop m = (L.take k ++ L.drop k).drop m := by rw [List.take_append_drop]
    _ = (L.take k).drop m ++ L.drop k :=
      List.drop_append_of_le_length (by rw [List.length_take]; omega)

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What a client holds for the entries `p` a `Ready` handed out: nothing for no entries, otherwise
the log from their first index `k` on (its current contents `old`), with the end, to write. -/
def appendRight (st : Storage) (p : List EntryM) : IProp GF :=
  iprop(⌜p = []⌝ ∨ ∃ (e0 : EntryM) (old : List EntryM), ⌜p.head? = some e0⌝ ∗
    storLog st (uint.nat e0.Index') (DFrac.own 1) old ∗
    storEnd st (uint.nat e0.Index' + old.length))

/-- ... and what it gives back at `Advance`: the batch written, as a frozen prefix `a` (possibly
empty) and an owned rest, with the end. -/
def appendReceipt (st : Storage) (p a : List EntryM) : IProp GF :=
  iprop(⌜p = []⌝ ∨ ∃ (e0 : EntryM) (b : List EntryM), ⌜p.head? = some e0 ∧ p = a ++ b⌝ ∗
    storLog st (uint.nat e0.Index') DFrac.discard a ∗
    storLog st (uint.nat e0.Index' + a.length) (DFrac.own 1) b ∗
    storEnd st (uint.nat e0.Index' + p.length))

/-- (D19i part 1; U8 v2: the authority's lower bound) The floor raft published is at least `x`:
the API's `nodeAppliedLb`. -/
def storFloor (sn : StorNames) (x : w64) : IProp GF := monoNatLbOwn sn.ga (uint.nat x)

/-- (U8 v2) A snapshot at index `k` was handed out to install: the API's `snapGiven`. -/
def storGiven (sn : StorNames) (k : Nat) : IProp GF := monoNatLbOwn sn.gg k

instance storFloor_pers (sn : StorNames) (x : w64) : Persistent (storFloor (GF := GF) sn x) := by
  unfold storFloor; infer_instance

instance storGiven_pers (sn : StorNames) (k : Nat) : Persistent (storGiven (GF := GF) sn k) := by
  unfold storGiven; infer_instance

/-- The authorities read only `fl` and `sg`. -/
theorem storAuths_eq (sn : StorNames) (σ σ' : StorState) (h1 : σ'.fl = σ.fl) (h2 : σ'.sg = σ.sg)
    (h3 : σ'.dt = σ.dt := by rfl) :
    ⊢ storAuths (GF := GF) sn σ -∗ storAuths sn σ' := by
  unfold storAuths; rw [h1, h2, h3]; iintro H; iexact H

/-- The view's frozen prefix, for good. -/
theorem ownStorage_frozen (sn : StorNames) (st : Storage) (σ : StorState) :
    ownStorage (GF := GF) sn st σ ⊢ ∃ e0, ⌜e0.Term' = σ.prev.term'⌝ ∗
      storLog st (uint.nat σ.prev.index') DFrac.discard
        (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')) := by
  unfold ownStorage
  iintro ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
  iexists e0
  iframe HFr
  ipureintro; exact Hw.1

/-- **Hand-out**: with nothing out, a batch `p` starting at `k` above the frozen prefix and at most
one past the log hands out the log from `k` on, with the end. -/
theorem ownStorage_handout (sn : StorNames) (st : Storage) (σ : StorState) (p : List EntryM)
    (Hp0 : σ.pend = []) (Hpo : PendOk σ p)
    (Hfr : ∀ e0, p.head? = some e0 → σ.fr < uint.nat e0.Index') :
    ⊢ ownStorage (GF := GF) sn st σ ==∗ ownStorage sn st { σ with pend := p } ∗ appendRight st p := by
  unfold ownStorage
  iintro ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
  obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
  obtain ⟨Hne, Hhd⟩ := Hpo
  obtain ⟨q0, rest, rfl⟩ := List.exists_cons_of_ne_nil Hne
  obtain ⟨Hq1, Hq2, -⟩ := Hhd q0 rfl
  have Hq3 := Hfr q0 rfl
  icases Hend with (%Hpn | Hend)
  · exact absurd Hp0 Hpn
  have Hk0 : σ.kOut = uint.nat σ.prev.index' + 1 + σ.ents.length := by
    unfold StorState.kOut; rw [Hp0]; rfl
  have h1 := uint_nat_eq q0.Index'; have h2 := uint_nat_eq σ.prev.index'
  -- split the owned part at `k`
  have Hk : ({ σ with pend := q0 :: rest } : StorState).kOut = uint.nat q0.Index' := rfl
  have Hsplit : (σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
        (σ.fr - uint.nat σ.prev.index') =
      (σ.ents.take (uint.nat q0.Index' - uint.nat σ.prev.index' - 1)).drop
        (σ.fr - uint.nat σ.prev.index') ++ σ.ents.drop (uint.nat q0.Index' - uint.nat σ.prev.index' - 1) := by
    rw [Hk0]
    have : uint.nat σ.prev.index' + 1 + σ.ents.length - uint.nat σ.prev.index' - 1 =
        σ.ents.length := by omega
    rw [this, List.take_length]
    exact drop_split σ.ents _ _ (by omega) (by omega)
  have Hlen1 : ((σ.ents.take (uint.nat q0.Index' - uint.nat σ.prev.index' - 1)).drop
        (σ.fr - uint.nat σ.prev.index')).length = uint.nat q0.Index' - (σ.fr + 1) := by
    simp only [List.length_drop, List.length_take]; omega
  rw [Hsplit]
  ihave ⟨HO1, HO2⟩ := (StorageModel.storLog_app st _ _ _ _).1 $$ HO
  rw [Hlen1]
  have Hix : σ.fr + 1 + (uint.nat q0.Index' - (σ.fr + 1)) = uint.nat q0.Index' := by omega
  rw [Hix]
  have Hend' : uint.nat σ.prev.index' + 1 + σ.ents.length = uint.nat q0.Index' +
      (σ.ents.drop (uint.nat q0.Index' - uint.nat σ.prev.index' - 1)).length := by
    rw [List.length_drop]; omega
  ihave Hend : storEnd st (uint.nat q0.Index' +
      (σ.ents.drop (uint.nat q0.Index' - uint.nat σ.prev.index' - 1)).length) $$ [Hend]
  · rw [← Hend']; iexact Hend
  imodintro
  isplitl [HO1 Hau]
  · iexists e0
    iframe Hcomp HFr
    rw [Hk]
    iframe HO1
    isplitr
    · ileft; ipureintro; exact List.cons_ne_nil _ _
    isplitl [Hau]
    · iapply (storAuths_eq sn σ { σ with pend := q0 :: rest } rfl rfl); iexact Hau
    ipureintro; exact ⟨Ht0, H1, by simp only [Hk]; omega, by simp only [Hk]; omega, H4⟩
  unfold appendRight
  iright
  iexists q0, σ.ents.drop (uint.nat q0.Index' - uint.nat σ.prev.index' - 1)
  iframe HO2 Hend
  ipureintro; rfl

/-- The view's ranges are kept across a change of its authorities only. -/
theorem ownStorage_auths (sn : StorNames) (st : Storage) (σ σ' : StorState)
    (hp : σ'.prev = σ.prev) (he : σ'.ents = σ.ents) (hpd : σ'.pend = σ.pend) (hf : σ'.fr = σ.fr)
    (hsg : σ'.sg ≤ σ.sg) :
    ⊢ ownStorage (GF := GF) sn st σ -∗ (storAuths sn σ -∗ storAuths sn σ') -∗
      ownStorage sn st σ' := by
  have hk : σ'.kOut = σ.kOut := by unfold StorState.kOut; rw [hp, he, hpd]
  unfold ownStorage
  iintro ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩ Hu
  ihave Hau := Hu $$ Hau
  rw [hp, he, hpd, hf, hk]
  iexists e0
  iframe Hcomp HFr HO Hend Hau
  ipureintro
  obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
  exact ⟨Ht0, H1, H2, H3, by omega⟩

/-- **Raising the floor** to `x`: an applied lower bound published (`storFloor`). -/
theorem ownStorage_floor (sn : StorNames) (st : Storage) (σ : StorState) (x : w64)
    (Hx : uint.nat σ.fl ≤ uint.nat x) :
    ⊢ ownStorage (GF := GF) sn st σ ==∗ ownStorage sn st { σ with fl := x } ∗ storFloor sn x := by
  unfold storFloor
  iintro H
  ihave Hu : (storAuths (GF := GF) sn σ ==∗ storAuths sn { σ with fl := x } ∗
      monoNatLbOwn sn.ga (uint.nat x)) $$ []
  · unfold storAuths
    iintro ⟨Ha, Hg, Hd⟩
    imod mono_nat_own_update (uint.nat x) Hx $$ Ha with ⟨Ha, #Hlb⟩
    imodintro
    iframe Ha Hg Hd Hlb
  unfold ownStorage
  icases H with ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
  imod Hu $$ Hau with ⟨Hau, #Hlb⟩
  imodintro
  iframe Hlb
  have hk : ({ σ with fl := x } : StorState).kOut = σ.kOut := rfl
  rw [hk]
  iexists e0
  iframe Hcomp HFr HO Hend Hau
  ipureintro; exact Hw

/-- **A snapshot `Ready`'s hand-out** (with nothing out): every range above the frozen prefix,
with the end, and the right to install the snapshot at `s` (`storGiven`), above the frozen prefix
(M2). Raft keeps its authorities (`lentStor`). -/
theorem ownStorage_lend (sn : StorNames) (st : Storage) (σ : StorState) (s : Nat)
    (Hp0 : σ.pend = []) (Hsg : σ.sg ≤ s) :
    ⊢ ownStorage (GF := GF) sn st σ ==∗ storAuths sn { σ with sg := s } ∗
      storLog st (σ.fr + 1) (DFrac.own 1) (σ.ents.drop (σ.fr - uint.nat σ.prev.index')) ∗
      storEnd st (σ.fr + 1 + (σ.ents.drop (σ.fr - uint.nat σ.prev.index')).length) ∗
      storGiven sn s := by
  unfold ownStorage storGiven
  iintro ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
  obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
  icases Hend with (%Hpn | Hend)
  · exact absurd Hp0 Hpn
  have Hk0 : σ.kOut = uint.nat σ.prev.index' + 1 + σ.ents.length := by
    unfold StorState.kOut; rw [Hp0]; rfl
  have : σ.kOut - uint.nat σ.prev.index' - 1 = σ.ents.length := by omega
  rw [this, List.take_length]
  have He : uint.nat σ.prev.index' + 1 + σ.ents.length =
      σ.fr + 1 + (σ.ents.drop (σ.fr - uint.nat σ.prev.index')).length := by
    rw [List.length_drop]; omega
  rw [He]
  unfold storAuths
  icases Hau with ⟨Ha, Hg, Hd⟩
  imod mono_nat_own_update s Hsg $$ Hg with ⟨Hg, #Hlb⟩
  imodintro
  iframe Ha Hg Hd HO Hend Hlb

/-- Raft's view after a snapshot's `Advance`: at the snapshot `sid`, frozen at it, the log `es`
after it. -/
def snapView (σ : StorState) (sid : entryID) (es : List EntryM) : StorState :=
  { prev := sid, ents := es, pend := [], fl := σ.fl, fr := uint.nat sid.index', sg := σ.sg,
    dt := σ.dt }

/-- **A snapshot's `Advance`**: the compaction point at the snapshot `sid`, the dummy there (of its
term) and the log after it, owned, with the end: raft's view becomes the snapshot's, frozen at it. -/
theorem ownStorage_absorb_snap (sn : StorNames) (st : Storage) (σ : StorState) (sid : entryID)
    (e : EntryM) (es : List EntryM) (He : e.Term' = sid.term') (Hsg : σ.sg ≤ uint.nat sid.index') :
    ⊢ storAuths (GF := GF) sn σ -∗ storCompacted st (uint.nat sid.index') -∗
      storLog st (uint.nat sid.index') DFrac.discard [e] -∗
      storLog st (uint.nat sid.index' + 1) (DFrac.own 1) es -∗
      storEnd st (uint.nat sid.index' + 1 + es.length) -∗
      ownStorage sn st (snapView σ sid es) := by
  iintro Hau #Hcomp #HF HO Hend
  unfold ownStorage
  iexists e
  have hk : (snapView σ sid es).kOut = uint.nat sid.index' + 1 + es.length := rfl
  rw [hk]
  simp only [snapView, storAuths, Nat.sub_self, List.take_zero, List.drop_zero]
  have : uint.nat sid.index' + 1 + es.length - uint.nat sid.index' - 1 = es.length := by omega
  rw [this, List.take_length]
  iframe Hcomp HF HO
  isplitl [Hend]
  · iright; iexact Hend
  isplitl [Hau]
  · iexact Hau
  ipureintro
  exact ⟨He, Nat.le_refl _, by omega, Nat.le_refl _, Hsg⟩

/-- Raft's view once the batch is back (`storAbsorb`), its frozen prefix extended past the batch's
frozen part `a` when `a ≠ []`. -/
def absorbView (σ : StorState) (a : List EntryM) : StorState :=
  { storAbsorb σ with fr := if a = [] then σ.fr else σ.kOut - 1 + a.length }

omit [GoGlobalContext] in
theorem storAbsorb_ents (σ : StorState) (e0 : EntryM) (Hhd : σ.pend.head? = some e0)
    (Hlo : uint.nat σ.prev.index' < uint.nat e0.Index') :
    (storAbsorb σ).ents =
      σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1) ++ σ.pend := by
  obtain ⟨q, rest, Hq⟩ : ∃ q rest, σ.pend = q :: rest := by
    cases h : σ.pend with
    | nil => rw [h] at Hhd; cases Hhd
    | cons q rest => exact ⟨q, rest, rfl⟩
  rw [Hq] at Hhd
  simp only [List.head?_cons, Option.some.injEq] at Hhd
  subst Hhd
  simp only [storAbsorb, Hq, storApp]
  have h1 := uint_nat_eq q.Index'; have h2 := uint_nat_eq σ.prev.index'
  congr 2
  omega

/-- **The batch back** (`Advance`): its frozen part `a` and owned rest `b`, with the end. -/
theorem ownStorage_absorb (sn : StorNames) (st : Storage) (σ : StorState) (e0 : EntryM)
    (a b : List EntryM) (Hhd : σ.pend.head? = some e0) (Hab : σ.pend = a ++ b) :
    ⊢ ownStorage (GF := GF) sn st σ -∗ storLog st (uint.nat e0.Index') DFrac.discard a -∗
      storLog st (uint.nat e0.Index' + a.length) (DFrac.own 1) b -∗
      storEnd st (uint.nat e0.Index' + σ.pend.length) ==∗
      ownStorage sn st (absorbView σ a) := by
  unfold ownStorage
  iintro ⟨%d0, #Hcomp, #HFr, HO, Hend0, Hau, %Hw⟩ #HA HB Hend
  obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
  have Hk : σ.kOut = uint.nat e0.Index' := by unfold StorState.kOut; rw [Hhd]
  have HE := storAbsorb_ents σ e0 Hhd (by omega)
  have Hents : (absorbView σ a).ents =
      σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1) ++ σ.pend := HE
  have Htl : (σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1)).length =
      uint.nat e0.Index' - uint.nat σ.prev.index' - 1 := by rw [List.length_take]; omega
  have HkO : (absorbView σ a).kOut = uint.nat e0.Index' + σ.pend.length := by
    unfold StorState.kOut
    have : (absorbView σ a).pend = [] := rfl
    rw [this]; simp only [List.head?_nil]
    rw [Hents, List.length_append, Htl]
    have : (absorbView σ a).prev = σ.prev := rfl
    rw [this]; omega
  have Hp : (absorbView σ a).prev = σ.prev := rfl
  have Hpn : (absorbView σ a).pend = [] := rfl
  rw [Hp, Hpn, HkO, Hents]
  have Hall : uint.nat e0.Index' + σ.pend.length - uint.nat σ.prev.index' - 1 =
      (σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1) ++ σ.pend).length := by
    rw [List.length_append, Htl]; omega
  rw [Hall, List.take_length]
  have Hendeq : uint.nat σ.prev.index' + 1 +
      (σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1) ++ σ.pend).length =
      uint.nat e0.Index' + σ.pend.length := by
    rw [List.length_append, Htl]; omega
  rw [Hendeq]
  iclear Hend0
  by_cases Ha : a = []
  · subst Ha
    have Hfr : (absorbView σ []).fr = σ.fr := by simp [absorbView]
    rw [Hfr]
    simp only [List.nil_append] at Hab
    simp only [List.length_nil, Nat.add_zero] at *
    rw [List.take_append_of_le_length (by rw [Htl]; omega),
      List.take_take, List.drop_append_of_le_length (by rw [Htl]; omega)]
    have : min (σ.fr - uint.nat σ.prev.index') (uint.nat e0.Index' - uint.nat σ.prev.index' - 1) =
        σ.fr - uint.nat σ.prev.index' := by omega
    rw [this]
    ihave HO : storLog st (σ.fr + 1) (DFrac.own 1)
        ((σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1)).drop
          (σ.fr - uint.nat σ.prev.index')) $$ [HO]
    · rw [← Hk]; iexact HO
    have HOl := view_owned_len σ H1 H2 H3
    rw [Hk] at HOl
    ihave HJ : storLog st (σ.fr + 1) (DFrac.own 1)
        ((σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1)).drop
          (σ.fr - uint.nat σ.prev.index') ++ σ.pend) $$ [HO HB]
    · iapply (StorageModel.storLog_app st _ _ _ _).2
      iframe HO
      rw [HOl, Hab]
      have : σ.fr + 1 + (uint.nat e0.Index' - 1 - σ.fr) = uint.nat e0.Index' := by omega
      rw [this]; iexact HB
    imodintro
    iexists d0
    iframe Hcomp HFr HJ
    isplitl [Hend]
    · iright; iexact Hend
    isplitl [Hau]
    · iapply (storAuths_eq sn σ (absorbView σ []) rfl rfl); iexact Hau
    ipureintro
    exact ⟨Ht0, H1, by omega, by omega, H4⟩
  · have Hfr : (absorbView σ a).fr = uint.nat e0.Index' - 1 + a.length := by
      simp [absorbView, Ha, Hk]
    rw [Hfr]
    rw [Hab] at Hall Hendeq ⊢
    have Hfa : uint.nat e0.Index' - 1 + a.length - uint.nat σ.prev.index' =
        (σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1)).length + a.length := by
      rw [Htl]; omega
    rw [Hfa, ← List.append_assoc, List.take_left' (by simp), List.drop_left' (by simp)]
    -- freeze raft's own part below `k`, and join the frozen pieces
    ihave HO : storLog st (σ.fr + 1) (DFrac.own 1)
        ((σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1)).drop
          (σ.fr - uint.nat σ.prev.index')) $$ [HO]
    · rw [← Hk]; iexact HO
    imod StorageModel.storLog_persist st _ _ _ $$ HO with #HO
    have HFl := view_frozen_len σ d0 H1 H2 H3
    have HPa := view_pieces_app σ d0 H1 H2
    rw [Hk] at HPa
    ihave #HFO : storLog st (uint.nat σ.prev.index') DFrac.discard
        (d0 :: σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1)) $$ []
    · rw [← HPa]
      iapply (StorageModel.storLog_app st _ _ _ _).2
      iframe HFr
      have : uint.nat σ.prev.index' + (σ.fr + 1 - uint.nat σ.prev.index') = σ.fr + 1 := by omega
      rw [HFl, this]
      iexact HO
    ihave #HFA : storLog st (uint.nat σ.prev.index') DFrac.discard
        (d0 :: (σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1) ++ a)) $$ []
    · rw [← List.cons_append]
      iapply (StorageModel.storLog_app st _ _ _ _).2
      iframe HFO
      have : uint.nat σ.prev.index' +
          (d0 :: σ.ents.take (uint.nat e0.Index' - uint.nat σ.prev.index' - 1)).length =
          uint.nat e0.Index' := by
        rw [List.length_cons, Htl]; omega
      rw [this]; iexact HA
    have Hb : uint.nat e0.Index' - 1 + a.length + 1 = uint.nat e0.Index' + a.length := by omega
    rw [Hb]
    imodintro
    iexists d0
    iframe Hcomp HFA HB
    isplitl [Hend]
    · iright; iexact Hend
    isplitl [Hau]
    · iapply (storAuths_eq sn σ (absorbView σ a) rfl rfl); iexact Hau
    ipureintro
    rw [List.length_append] at Hall Hendeq
    exact ⟨Ht0, by omega, by simp only [List.length_append]; omega, by omega, H4⟩

/-- **Freezing** the view's log up to `j` (below the batch out): what a `Ready` does to its
committed entries below `k`, and an `Advance` to its delivered ones. -/
theorem ownStorage_freeze (sn : StorNames) (st : Storage) (σ : StorState) (j : Nat)
    (Hj : σ.fr ≤ j) (Hjk : j < σ.kOut) :
    ⊢ ownStorage (GF := GF) sn st σ ==∗ ownStorage sn st { σ with fr := j } := by
  unfold ownStorage
  iintro ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
  obtain ⟨Ht0, H1, H2, H3, H4⟩ := Hw
  have hk : ({ σ with fr := j } : StorState).kOut = σ.kOut := rfl
  rw [hk]
  have HOl := view_owned_len σ H1 H2 H3
  have Hsp : (σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
      (σ.fr - uint.nat σ.prev.index') =
      ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
        (σ.fr - uint.nat σ.prev.index')).take (j - σ.fr) ++
      (σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop (j - uint.nat σ.prev.index') := by
    have : j - uint.nat σ.prev.index' = (j - σ.fr) + (σ.fr - uint.nat σ.prev.index') := by omega
    rw [this]
    first
      | (rw [← List.drop_drop, List.take_append_drop])
      | (rw [Nat.add_comm, ← List.drop_drop, List.take_append_drop])
  rw [Hsp]
  ihave ⟨HO1, HO2⟩ := (StorageModel.storLog_app st _ _ _ _).1 $$ HO
  imod StorageModel.storLog_persist st _ _ _ $$ HO1 with #HO1
  have HFl := view_frozen_len σ e0 H1 H2 H3
  have Hl1 : (((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
      (σ.fr - uint.nat σ.prev.index')).take (j - σ.fr)).length = j - σ.fr := by
    rw [List.length_take, HOl]; omega
  ihave #HF2 : storLog st (uint.nat σ.prev.index') DFrac.discard
      ((e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')) ++
        ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
          (σ.fr - uint.nat σ.prev.index')).take (j - σ.fr)) $$ []
  · iapply (StorageModel.storLog_app st _ _ _ _).2
    iframe HFr
    have : uint.nat σ.prev.index' + (σ.fr + 1 - uint.nat σ.prev.index') = σ.fr + 1 := by omega
    rw [HFl, this]; iexact HO1
  have Heq : (e0 :: σ.ents.take (σ.fr - uint.nat σ.prev.index')) ++
        ((σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).drop
          (σ.fr - uint.nat σ.prev.index')).take (j - σ.fr) =
      e0 :: σ.ents.take (j - uint.nat σ.prev.index') := by
    rw [List.cons_append]
    congr 1
    have h1 : σ.ents.take (σ.fr - uint.nat σ.prev.index') =
        (σ.ents.take (σ.kOut - uint.nat σ.prev.index' - 1)).take (σ.fr - uint.nat σ.prev.index') := by
      rw [List.take_take]; congr 1; omega
    rw [h1, ← List.take_add, List.take_take]
    congr 1; omega
  rw [Heq] at *
  have Hix : σ.fr + 1 + (j - σ.fr) = j + 1 := by omega
  rw [Hl1, Hix] at *
  imodintro
  iexists e0
  iframe Hcomp HF2 HO2 Hend
  isplitl [Hau]
  · iapply (storAuths_eq sn σ { σ with fr := j } rfl rfl); iexact Hau
  ipureintro
  exact ⟨Ht0, show uint.nat σ.prev.index' ≤ j by omega, show j + 1 ≤ σ.kOut by omega, H3, H4⟩

/-- The hand-out at a batch that may be empty (nothing out for `[]`, N2). -/
theorem ownStorage_handout_opt (sn : StorNames) (st : Storage) (σ : StorState) (p : List EntryM)
    (Hpo : σ.pend = [] ∧ (p ≠ [] → PendOk σ p ∧
      ∀ e0, p.head? = some e0 → σ.fr < uint.nat e0.Index')) :
    ⊢ ownStorage (GF := GF) sn st σ ==∗ ownStorage sn st { σ with pend := p } ∗ appendRight st p := by
  iintro H
  by_cases Hne : p = []
  · have Hσ : ({ σ with pend := p } : StorState) = σ := by rw [Hne, ← Hpo.1]
    rw [Hσ]
    imodintro
    iframe H
    unfold appendRight
    ileft; ipureintro; exact Hne
  iapply ownStorage_handout sn st σ p Hpo.1 (Hpo.2 Hne).1 (Hpo.2 Hne).2 $$ H

end laws

end EtcdGrove
end Perennial
