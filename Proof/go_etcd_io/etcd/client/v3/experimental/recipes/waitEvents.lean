/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/waitEvents.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.waitEvents

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem waitEvents.wp_proof : waitEvents.spec (GF := GF) (hG := hG) := by
  intro wc γ pfx o rev rcv sl ts typ
  wp_start as ⟨#Hwc, Hcons, #Hsl, %Hlast⟩
  have Hts : ts ≠ [] := by intro h; rw [h] at Hlast; simp at Hlast
  ihave %Htl := ownSlice_len $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (rcv' : List go_etcd_io.etcd.client.v3.WatchResponse)
      (v : go_etcd_io.etcd.client.v3.WatchResponse) (i : w64),
      "Hcons" ∷ spscConsumer γ.spsc rcv' ∗ "wresp" ∷ wresp_ptr ↦ v ∗ "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i < (ts.length : Int)⌝) $$ [Hcons wresp i]
  · iexists rcv, _, W64 0
    simp only [named]
    iframe
    ipureintro
    constructor
    · decide
    · have : 0 < ts.length := by
        cases ts with
        | nil => exact absurd rfl Hts
        | cons _ _ => simp
      simp; omega
  wp_for IH
  wp_bind (App (Val (chan.receive _)) _)
  wp_apply wp_spsc_receive γ.spsc wc (rangeWatchElem γ pfx o rev) (fun _ => iprop(False)) rcv'
    $$ [$Hwc $Hcons] as %v' %ok H
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨HF, -⟩
    iexfalso
    iexact HF
  simp only [↓reduceIte]
  icases H with ⟨HP, Hcons⟩
  iunfold rangeWatchElem at HP
  icases HP with ⟨%r, %c, %c', #Hevs, -, -, -, -, #Hok⟩
  iunfold rangeWatchRespOk at Hok
  icases Hok with ⟨-, #Hok⟩
  iunfold eventsAt at Hevs
  icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
  wp_auto
  ihave %Hsll := ownSlice_len $$ Hls
  -- `slice.forRange`'s own counter is `i_ptr` now; the Go variable `i` is `ig`
  rename_i ig
  irename : (ig ↦ i : IProp GF) => gi
  ihave IH2 : iprop(∃ (n : w64) (e0 : Loc) (i : w64),
      "j" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗ "gi" ∷ ig ↦ i ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝ ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i < (ts.length : Int)⌝) $$ [i ev gi]
  · iexists W64 0, _, i
    simp only [named]
    iframe
    ipureintro; refine ⟨by constructor <;> word, Hi⟩
  wp_for IH2
  wp_if_destruct
  · have Hlt : sint.nat n < ls.length := by word
    obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨e, He⟩ : ∃ e, r.events[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z v'.Events'.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) l v'.Events' DFrac.discard ls Hn.1 Hl $$ Hls
      with ⟨#Hle, -⟩
    ihave #He := Hev $$ %(sint.nat n) %l %e %Hl %He
    ihave #He' := He
    iunfold eventAt at He'
    icases He' with ⟨%keySl, #Htyp, -⟩
    obtain ⟨t, Ht⟩ : ∃ t, ts[sint.nat i]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, by word⟩
    (try wp_auto)
    rw [ite_eq_left Hbi]
    icases ownSlice_elem_acc (sint.Z i) t sl DFrac.discard ts Hi.1 Ht $$ Hsl with ⟨#Hte, -⟩
    (try wp_auto)
    wp_if_destruct
    · -- the awaited type
      (try wp_auto)
      wp_if_destruct
      · -- the last one: `ev` is the event
        wp_for_post
        wp_for_post
        iapply HΦ
        isplitl []
        · unfold waitedEvent
          iexists e
          iframe He
          isplitr
          · ipureintro
            have hlast : sint.nat i + 1 = ts.length := by word
            rw [List.getLast?_eq_getElem?] at Hlast
            rw [show ts.length - 1 = sint.nat i by omega, Ht] at Hlast
            cases Hlast; rfl
          ihave #Hok' := Hok $$ %(sint.nat n) %e %He
          iexact Hok'
        iexists _
        iexact Hcons
      · -- not yet the last
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, l, i + W64 1
        simp only [named]
        iframe
        ipureintro; refine ⟨by constructor <;> word, by constructor <;> word⟩
    · -- another type
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, l, i
      simp only [named]
      iframe
      ipureintro; refine ⟨by constructor <;> word, Hi⟩
  · -- the response is done: the next one
    (try wp_auto)
    wp_for_post
    iframe
    iexists rcv' ++ [v'], v', i
    simp only [named]
    iframe
    ipureintro; exact Hi

end proof

end recipes
end EtcdGrove
end Perennial
