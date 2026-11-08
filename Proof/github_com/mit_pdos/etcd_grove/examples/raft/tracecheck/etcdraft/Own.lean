/-
Lean-first (no Rocq counterpart).

# The search's copy-on-write: owned copies (Probe, 2026-11-08)

The checker's search never writes a state it was handed: an action `clone`s the state (a new
struct and a new server map sharing the servers) and `mut`s the server it changes (a `copy`: a
new struct and a new `MatchIndex` map), writes the copies, and returns the clone, which nobody
writes again. So a state or a server is read-only (`stateRO`, `serverRO`, `Rep.lean`) except
while the action building it holds it: `serverOwn` is a server copy being written, persisted into
`serverRO` once done (`serverOwn_persist`). Layer C's Probe (`notes/trace-validation-plan.md`,
"Probe set") checks this design on `(*State).Timeout`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

/-- `ByteArray.toList`'s loop, from position `i` with the reversed prefix `r`. -/
theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) (hi : i ≤ bs.size) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction h : bs.size - i generalizing i r with
  | zero =>
    have : i = bs.size := by omega
    subst this
    rw [ByteArray.toList.loop, ite_eq_right_of_eq_false _ _ (eq_false (Nat.lt_irrefl _))]
    have : bs.data.toList.drop bs.size = [] := by
      apply List.drop_of_length_le
      show bs.data.toList.length ≤ bs.data.size
      rw [Array.length_toList]; exact Nat.le_refl _
    rw [this, List.append_nil]
  | succ n ih =>
    have hlt : i < bs.size := by omega
    rw [ByteArray.toList.loop, ite_eq_left_of_eq_true _ _ (eq_true hlt), ih (i + 1) (bs.get! i :: r) (by omega) (by omega)]
    have hg : bs.get! i = bs.data.toList[i] := by
      rcases bs with ⟨d⟩
      show d[i]! = d.toList[i]
      rw [Array.getElem_toList, getElem!_pos d i hlt]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, hg, List.getElem_cons_drop]

/-- `ByteArray.toList` is its array's list. -/
theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [byteArray_toList_loop bs 0 [] (Nat.zero_le _)]
  simp

/-- `stringToGoString` is injective (UTF-8 encoding is). A fact about Perennial's definition
(`Perennial/Std/ByteString.lean`), proved here for the Probe, to move to Perennial
(`notes/perennial-changes.md`, "stringToGoString_inj"). -/
theorem stringToGoString_inj {a b : String} (h : stringToGoString a = stringToGoString b) : a = b := by
  unfold stringToGoString at h
  have hf : Function.Injective (fun x : UInt8 => (BitVec.ofNat 8 x.toNat : w8)) := by
    intro x y hxy
    simp only at hxy
    apply UInt8.toNat_inj.1
    have h1 := congrArg BitVec.toNat hxy
    simp only [BitVec.toNat_ofNat] at h1
    have := x.toNat_lt; have := y.toNat_lt
    omega
  have h2 := (List.map_inj_right (fun x y hxy => hf hxy)).1 h
  rw [← String.toByteArray_inj]
  simp only [String.toUTF8_eq_toByteArray, byteArray_toList_eq] at h2
  exact ByteArray.ext (Array.toList_inj.1 h2)

/-- An id below `2^64` read back from its word. -/
theorem uint_nat_W64_of_lt (j : Nat) (h : j < 2 ^ 64) : uint.nat (W64 (Int.ofNat j)) = j := by
  show BitVec.toNat (BitVec.ofInt 64 (Int.ofNat j)) = j
  rw [BitVec.toNat_ofInt]
  have : (j : Int) < 2 ^ 64 := by exact_mod_cast h
  simp only [Int.ofNat_eq_natCast]
  omega

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A `*Server` copy being written: `serverRO`'s, with the struct and the `MatchIndex` map owned. -/
def serverOwn (p : Loc) (v : Server) : IProp GF :=
  iprop(∃ (g : G.Server) (mm : GMap w64 w64), p ↦ g ∗
    ⌜sint.Z g.CurrentTerm' = v.currentTerm ∧ g.State' = stringToGoString v.state ∧
      uint.nat g.VotedFor' = v.votedFor ∧ sint.Z g.CommitIndex' = v.commitIndex ∧
      sint.Z g.PendingConfChangeIndex' = v.pendingConfChangeIndex⌝ ∗
    logRO g.Log' v.log ∗ setRO g.VotesResponded' v.votesResponded ∗
    setRO g.VotesGranted' v.votesGranted ∗
    g.MatchIndex' ↦$ mm ∗
    ⌜∀ j : w64, sint.Z ((mm !! j).getD (W64 0)) = v.matchIndex (uint.nat j)⌝ ∗
    configRO g.Config' v.config ∗ durableRO g.Durable' v.durable)

/-- A written copy, frozen. -/
theorem serverOwn_persist (p : Loc) (v : Server) :
    serverOwn (GF := GF) p v ⊢ |==> serverRO p v := by
  iintro H
  iunfold serverOwn at H
  icases H with ⟨%g, %mm, Hp, %Hf, #Hl, #Hr, #Hg, Hm, %Hmi, #Hc, #Hd⟩
  ipersist Hp
  ipersist Hm
  imodintro
  iunfold serverRO
  iexists g, mm
  iframe Hp Hl Hr Hg Hm Hc Hd
  ipureintro; exact ⟨Hf, Hmi⟩

/-- A `*State` clone being built: the struct and the server map owned; the servers in `M` are
copies being written (`serverOwn`), the others shared (`serverRO`). -/
def stateOwn (p : Loc) (st : State) (M : List ID) : IProp GF :=
  iprop(∃ (g : G.State) (sm : GMap w64 Loc), p ↦ g ∗ setRO g.Server' st.server ∗
    g.S' ↦$ sm ∗
    ⌜∀ k : w64, (sm !! k).isSome ↔ uint.nat k ∈ st.server⌝ ∗
    ([∗list] i ∈ st.server, ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗
      (if i ∈ M then serverOwn q (st.s i) else serverRO q (st.s i))) ∗
    bagRO g.Messages' st.messages ∗ bagRO g.PendingMessages' st.pendingMessages ∗
    ⌜sint.Z g.ReconfigCount' = st.reconfigCount⌝)

/-- A built clone, frozen. -/
theorem stateOwn_persist (p : Loc) (st : State) (M : List ID) :
    stateOwn (GF := GF) p st M ⊢ |==> stateRO p st := by
  iintro H
  iunfold stateOwn at H
  icases H with ⟨%g, %sm, Hp, #Hsrv, Hm, %Hkeys, Hsrvs, #Hb1, #Hb2, %Hrc⟩
  ipersist Hp
  ipersist Hm
  ihave Hsrvs : iprop([∗list] i ∈ st.server, |==> ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗
      serverRO (GF := GF) q (st.s i)) $$ [Hsrvs]
  · iapply (BigSepL.bigSepL_mono (fun {_ i} _ => ?_)) $$ Hsrvs
    iintro ⟨%q, %Hq, Hs⟩
    by_cases hi : i ∈ M
    · simp only [hi, ite_true]
      imod serverOwn_persist $$ Hs with Hs
      imodintro; iexists q; iframe Hs; ipureintro; exact Hq
    · simp only [hi, ite_false]
      imodintro; iexists q; iframe Hs; ipureintro; exact Hq
  imod BigSepL.bigSepL_bupd _ _ $$ Hsrvs with Hsrvs
  imodintro
  iunfold stateRO
  iexists g, sm
  iframe Hp Hsrv Hm Hb1 Hb2 Hsrvs
  ipureintro; exact ⟨Hkeys, Hrc⟩

/-- A clone whose server `i` is a copy at `c` held apart (`mut`'s result, being written): `stateOwn`
without server `i`'s resource. -/
def stateOwnHole (p : Loc) (st : State) (M : List ID) (i : ID) (c : Loc) : IProp GF :=
  iprop(∃ (g : G.State) (sm : GMap w64 Loc), p ↦ g ∗ setRO g.Server' st.server ∗
    g.S' ↦$ sm ∗
    ⌜∀ k : w64, (sm !! k).isSome ↔ uint.nat k ∈ st.server⌝ ∗
    ⌜sm !! (W64 (Int.ofNat i)) = some c⌝ ∗
    ([∗list] j ∈ st.server, if j = i then emp else ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
      (if j ∈ M then serverOwn q (st.s j) else serverRO q (st.s j))) ∗
    bagRO g.Messages' st.messages ∗ bagRO g.PendingMessages' st.pendingMessages ∗
    ⌜sint.Z g.ReconfigCount' = st.reconfigCount⌝)

/-- Server `i`, written to `v`, put back: the clone holds `st` with server `i` set to `v`. -/
theorem stateOwnHole_close (p : Loc) (st : State) (M : List ID) (i : ID) (c : Loc) (v : Server)
    (hi : i ∈ st.server) (hnd : st.server.Nodup) :
    stateOwnHole (GF := GF) p st M i c ∗ serverOwn c v ⊢
      stateOwn p (st.upd i (fun _ => v)) (i :: M) := by
  iintro ⟨H, Hc⟩
  iunfold stateOwnHole at H
  icases H with ⟨%g, %sm, Hp, #Hsrv, Hm, %Hkeys, %Hci, Hsrvs, #Hb1, #Hb2, %Hrc⟩
  obtain ⟨l1, l2, Hsplit⟩ := List.append_of_mem hi
  have hnd' := hnd
  rw [Hsplit] at hnd'
  have hi1 : i ∉ l1 := by
    intro h
    have := (List.nodup_append.1 hnd').2.2
    exact this i h i List.mem_cons_self rfl
  have hi2 : i ∉ l2 := (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).1
  iunfold stateOwn
  iexists g, sm
  iframe Hp Hm
  simp only [State.upd]
  iframe Hsrv Hb1 Hb2
  isplitr
  · ipureintro; exact Hkeys
  isplitl [Hsrvs Hc]
  · rw [Hsplit]
    icases BigSepL.bigSepL_append.1 $$ Hsrvs with ⟨H1, H2⟩
    icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨-, H2⟩
    iapply BigSepL.bigSepL_append.2
    isplitl [H1]
    · iapply (BigSepL.bigSepL_mono (fun {_ j} hj => ?_)) $$ H1
      have hji : j ≠ i := fun h => hi1 (h ▸ List.mem_of_getElem? hj)
      simp only [hji, ite_false, List.mem_cons, false_or]
      exact .rfl
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc]
    · simp only [ite_true, List.mem_cons, true_or]
      iexists c; iframe Hc; ipureintro; exact Hci
    iapply (BigSepL.bigSepL_mono (fun {_ j} hj => ?_)) $$ H2
    have hji : j ≠ i := fun h => hi2 (h ▸ List.mem_of_getElem? hj)
    simp only [hji, ite_false, List.mem_cons, false_or]
    exact .rfl
  ipureintro; exact Hrc

end defs

end Etcdraft
end EtcdGrove
end Perennial
