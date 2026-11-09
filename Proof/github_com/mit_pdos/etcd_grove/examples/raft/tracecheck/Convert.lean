/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09).

# Raft's events as the checker reads them: the pure part of `ConvertEvents`

`ConvertEvents` (`examples/raft/tracecheck/main.go`) copies raft's events (`TracingEvent`s) into
the checker's (`etcdraft.Event`s), field by field; `evConv` (`TraceSim.lean`) is that conversion on
the abstract values. The checker's representation (`eventsRO`, `etcdraft/Rep.lean`) relates its Go
strings to Lean strings byte by character (`strRel`), which only an ASCII string satisfies, while
`evConv` maps every byte `c` to the character `Char.ofNat c` (`gsStr`): the two agree exactly on
ASCII strings. So `ConvertEvents`'s spec takes the events' strings ASCII (`TraceEv.Ascii`: raft's
event names, roles, message types and ids, `strconv.FormatUint`'s, are).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSim
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open go_etcd_io.raft.v3 TraceSim

section ascii
variable [GooseExts]

theorem gsStr_toList (b : GoString) : (gsStr b).toList = b.map (fun c => Char.ofNat c.toNat) :=
  String.toList_ofList

theorem char_ofNat_toNat_ascii (n : Nat) (h : n < 128) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dite_eq_left (by unfold Nat.isValidChar; omega)]
  rfl

/-- An ASCII Go string holds its `gsStr`. -/
theorem strRel_gsStr (b : GoString) (h : gsAscii b) : Etcdraft.strRel b (gsStr b) := by
  have hc : ∀ c ∈ b, (Char.ofNat c.toNat).toNat = c.toNat := by
    intro c hc
    exact char_ofNat_toNat_ascii _ (h c hc)
  refine ⟨?_, ?_⟩
  · intro c hc'
    rw [gsStr_toList, List.mem_map] at hc'
    obtain ⟨x, hx, rfl⟩ := hc'
    rw [hc x hx]; exact h x hx
  · rw [gsStr_toList, List.map_map]
    conv => lhs; rw [← List.map_id b]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp, id, hc x hx]
    simp

/-- A list of ASCII Go strings holds its `gsStr`s. -/
theorem forall₂_strRel_gsStr : ∀ (xs : List GoString), (∀ s ∈ xs, gsAscii s) →
    List.Forall₂ Etcdraft.strRel xs (xs.map gsStr)
  | [], _ => List.Forall₂.nil
  | x :: xs, h => List.Forall₂.cons (strRel_gsStr x (h x List.mem_cons_self))
      (forall₂_strRel_gsStr xs (fun s hs => h s (List.mem_cons_of_mem _ hs)))

/-- A raft `SingleConfChange` as `ConvertEvents` copies it. -/
def changeOf (x : SingleConfChange) : Etcdraft.G.EventChange := { NID' := x.NodeID', Action' := x.Action' }

/-- The checker's copies of a configuration change's changes hold `ccConv`'s. -/
theorem forall₂_changeRel (chs : List SingleConfChange)
    (h : ∀ p ∈ chs.map (fun x => (x.NodeID', x.Action')), gsAscii p.1 ∧ gsAscii p.2) :
    List.Forall₂ Etcdraft.changeRel
      (chs.map changeOf)
      ((chs.map (fun x => (x.NodeID', x.Action'))).map
        (fun p => ({ nid := gsStr p.1, action := gsStr p.2 } : Etcdraft.EventChange))) := by
  induction chs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    have hx := h _ List.mem_cons_self
    exact List.Forall₂.cons ⟨strRel_gsStr _ hx.1, strRel_gsStr _ hx.2⟩
      (ih (fun p hp => h p (List.mem_cons_of_mem _ hp)))

end ascii

section reps
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [etcdraft_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A Go `*EventMsg` holding `o` (nil for `none`): `eventRO`'s statement about an event's `Msg`. -/
def eventMsgRO (p : Loc) (o : Option Etcdraft.EventMsg) : IProp GF :=
  match o with
  | none => iprop(⌜p = null⌝)
  | some m => iprop(∃ gm : Etcdraft.G.EventMsg, p ↦□ gm ∗ ⌜Etcdraft.eventMsgRel gm m⌝)

instance eventMsgRO_persistent (p : Loc) (o : Option Etcdraft.EventMsg) :
    Persistent (eventMsgRO (GF := GF) p o) := by
  cases o <;> unfold eventMsgRO <;> infer_instance

open Iris.ProofMode in
/-- A traced message's pointer is nil exactly when the event has none. -/
theorem tracingMsgRep_null (p : Loc) (o : Option TraceMsg) :
    tracingMsgRep (GF := GF) p o ⊢ ⌜o = none ↔ p = null⌝ := by
  cases o with
  | none =>
    unfold tracingMsgRep
    iintro %h
    ipureintro; simp [h]
  | some m =>
    unfold tracingMsgRep
    iintro ⟨%g, Hp, -⟩
    ihave %h := typedPointsto_not_null _ _ _ $$ Hp
    ipureintro; simp [h]

open Iris.ProofMode in
/-- A configuration change's pointer is nil exactly when there is none. -/
theorem tracingCCRep_null (p : Loc) (o : Option TraceCC) :
    tracingCCRep (GF := GF) p o ⊢ ⌜o = none ↔ p = null⌝ := by
  cases o with
  | none =>
    unfold tracingCCRep
    iintro %h
    ipureintro; simp [h]
  | some m =>
    unfold tracingCCRep
    iintro ⟨%g, %chs, Hp, -⟩
    ihave %h := typedPointsto_not_null _ _ _ $$ Hp
    ipureintro; simp [h]

open Iris.ProofMode in
/-- A checker's event value built from raft's event `e` (its fields copied, its `Conf` slices
raft's) holds `evConv e`, given its message and properties. -/
theorem eventRO_intro (v : Etcdraft.G.Event) (e : TraceEv) (a b : GoSlice) (ha : TraceEv.Ascii e)
    (h : v.Name' = e.name ∧ v.NID' = e.nid ∧ v.State'.Term' = e.term ∧ v.State'.Vote' = e.vote ∧
      v.State'.Commit' = e.commit ∧ v.Role' = e.role ∧ v.Log' = e.logSize ∧ v.Conf'.arr = [a, b]) :
    a ↦*□ e.conf.1 -∗ b ↦*□ e.conf.2 -∗ eventMsgRO (GF := GF) v.Msg' (evConv e).msg -∗
      Etcdraft.propsRO v.Prop' (evConv e).prop -∗ Etcdraft.eventRO v (evConv e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6, -, -⟩ := ha
  iintro #Ha #Hb #Hm #Hp
  unfold Etcdraft.eventRO
  isplitr
  · ipureintro
    simp only [evConv, gInt]
    rw [h1, h2, h3, h4, h5, h6, h7]
    exact ⟨strRel_gsStr _ a1, strRel_gsStr _ a2, rfl, strRel_gsStr _ a3, rfl, strRel_gsStr _ a4, rfl⟩
  isplitl []
  · iexists a, b
    isplitr
    · ipureintro; exact h8
    isplitl []
    · iexists e.conf.1
      isplitr
      · iexact Ha
      ipureintro; exact forall₂_strRel_gsStr _ a5
    · iexists e.conf.2
      isplitr
      · iexact Hb
      ipureintro; exact forall₂_strRel_gsStr _ a6
  isplitl []
  · unfold eventMsgRO
    cases (evConv e).msg <;> iexact Hm
  · iexact Hp

end reps

end TraceCheck
end EtcdGrove
end Perennial
