/-
**One response of watchkv's watch, read from the KV state** (2026-10-26). Lean-first (no Rocq
counterpart).

`resp_state`: `Collect`'s premise (`Hresp`) at the client's Watch spec's responses (`stateOk` at the
read update's `wkReadQ`, `Writes.lean`): the response read a state `σ` of a watchkv log the program
saw. From the watch's position after `n` events (`Cur n c`):

* an error contradicts the premise; a response without events that is no progress notification
  stays at the position;
* a progress notification at `p` either stays (the watch's start) or has no event of the prefix
  in `(c, p]`, so (`rangeEvents_plan`, `StateEvents.lean`: every revision from `2` on is one put
  under the prefix) `p` is at most the position (or `1`, before the first event);
* events are those of the revisions `c + 1, ..., c'`, one each from `2` on (`rangeEvents_plan`):
  the `j`-th the put of revision `2 + n + j` (`revEvents_plan`), a pair of the plan, and that
  revision of a state the program saw (`wkRevAt`, from the read's lower bound of the changes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.StateEvents
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Writes
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.RespChan
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem sint_nat_cast (x : w64) (h : 0 ≤ sint.Z x) : ((sint.nat x : Nat) : Int) = sint.Z x := by
  show ((x.toInt.toNat : Nat) : Int) = sint.Z x
  exact Int.toNat_of_nonneg h

/-- **One response of the watch** (see the file header). -/
theorem resp_state (γc : GName) (P : List (GoString × GoString)) (hpk : ∀ kv ∈ P, wkPfx <+: kv.1)
    (o : OpFull) (hk : o.key = wkPfx) (he : o.base.rangeEnd = prefixRangeEnd wkPfx) (n : Nat)
    (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (hne : ¬ watchErr v) (hcur : common.Cur n c) :
    ⊢ common.stateOk (GF := GF) o (wkReadQ γc P) c c' v r ={⊤}=∗
      ⌜common.Cur (n + r.events.length) c'⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        common.evFactR (wkRevAt γc) P (2 + n + j) e := by
  have hrange : ∀ k, inRange o.key o.base.rangeEnd k = true ↔ wkPfx <+: k := by
    intro k; rw [hk, he]; exact concurrency.inRange_prefix wkPfx k (by decide)
  have hc0 : 0 ≤ sint.Z c := by unfold common.Cur at hcur; omega
  have hcn : ((sint.nat c : Nat) : Int) = sint.Z c := sint_nat_cast c hc0
  iintro Hok
  unfold common.stateOk
  icases Hok with ⟨%σ, #HQ, #Hr⟩
  unfold wkReadQ
  icases HQ with ⟨#Hlb, %HW⟩
  have hW : WkLog P σ.log := HW.1
  unfold watchStateRespOk
  icases Hr with (⟨%H, -⟩ | %H | %H | ⟨%H, #Hev⟩)
  · exact absurd H.1 hne
  · obtain ⟨-, he0, -, rfl⟩ := H
    imodintro
    rw [he0]
    isplitr
    · ipureintro; simpa using hcur
    iintro !> %j %e %h
    simp at h
  · obtain ⟨-, hp, -, hle, rfl, hcase⟩ := H
    have he0 := isProgressNotify_events hp
    have hpn : ((sint.nat r.hdrRev : Nat) : Int) = sint.Z r.hdrRev := sint_nat_cast _ (by omega)
    have hc' : common.Cur n r.hdrRev := by
      rcases hcase with ⟨heq, -⟩ | ⟨-, hnil, hok⟩
      · have : c = r.hdrRev := by word
        rw [← this]; exact hcur
      · rw [rangeEvents_plan P wkPfx o hrange hpk σ (sint.nat r.hdrRev) hW hok (sint.nat c + 1)
          (sint.nat r.hdrRev + 1) (by omega) (by omega)] at hnil
        simp only [List.map_eq_nil_iff, List.range'_eq_nil_iff] at hnil
        unfold common.Cur at hcur ⊢
        omega
    imodintro
    rw [he0]
    isplitr
    · ipureintro; simpa using hc'
    iintro !> %j %e %h
    simp at h
  · obtain ⟨-, hne', -, hlt, -, -, hok⟩ := H
    have hcn' : ((sint.nat c' : Nat) : Int) = sint.Z c' := sint_nat_cast _ (by omega)
    have h63 := hok.2.2.1
    rw [rangeEvents_plan P wkPfx o hrange hpk σ (sint.nat c') hW hok (sint.nat c + 1)
      (sint.nat c' + 1) (by omega) (by omega)]
    iunfold eventsIs at Hev
    icases Hev with ⟨%hlen, #Hall⟩
    simp only [List.length_map, List.length_range'] at hlen
    have hs : max (sint.nat c + 1) 2 = 2 + n := by unfold common.Cur at hcur; omega
    have hlen0 : 0 < r.events.length := List.length_pos_iff.2 hne'
    imodintro
    isplitr
    · ipureintro
      unfold common.Cur at hcur ⊢
      right; omega
    iintro !> %j %e %hj
    have hjl : j < r.events.length := (List.getElem?_eq_some_iff.mp hj).1
    have hm2 : 2 ≤ 2 + n + j := by omega
    have hmc : 2 + n + j ≤ sint.nat c' := by omega
    obtain ⟨k, val, nv, hkv, hlog, hrev, hkey, hval, hmod⟩ :=
      revEvents_plan P σ (sint.nat c') hW hok (2 + n + j) hm2 hmc
    have hpe : planEv σ (2 + n + j) = ⟨false, nv, none⟩ := by unfold planEv; rw [hrev]; rfl
    have hev : ((List.range' (max (sint.nat c + 1) 2) (sint.nat c' + 1 - max (sint.nat c + 1) 2)).map
        (planEv σ))[j]? = some ⟨false, nv, none⟩ := by
      rw [List.getElem?_map, List.getElem?_range' (by omega), hs]
      simp only [Option.map_some, Nat.one_mul, hpe]
    ihave #Hei := Hall $$ %j %e %_ %hj %hev
    iunfold eventIs at Hei
    icases Hei with ⟨%Hp, #Hkv⟩
    obtain ⟨hty, hek, herev⟩ := Hp
    simp only [Bool.false_eq_true, ↓reduceIte] at hty hek herev
    unfold common.evFactR
    isplitr
    · ipureintro
      refine ⟨hty, ?_⟩
      rw [herev, hmod]
      word
    iexists val, nv
    iframe Hkv
    isplitr
    · ipureintro
      refine ⟨hval, ?_⟩
      rw [hek, hkey]; exact hkv
    unfold wkRevAt
    iexists σ.changes
    iframe Hlb
    ipureintro
    rw [hek, hkey]
    exact hlog

end facts

end watchkv
end EtcdGrove
end Perennial
