/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/list__Register.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.list__Register

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

/-- `start_handoff` (`cache/v3/Handoff.lean`) for a value predicate that names the handoff's own
ghost names (`waitVal γh Ψ` mentions the consumer token `γh`). -/
theorem start_handoff_dep {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (ch : Loc) (P : HandoffNames → V → IProp GF) (Ws Wc : IProp GF) (γ : ChanNames) :
    ⊢ isChan ch γ V -∗ ownChan γ V (.Buffered []) ={⊤}=∗
      ∃ γh : HandoffNames, ⌜γh.chanName = γ⌝ ∗ isHandoff γh ch (P γh) Ws Wc ∗
        handoffProducer γh false ∗ handoffConsumer γh false := by
  iintro #Hch Hoc
  imod dghostVar_alloc false with ⟨%γs, Hs⟩
  icases dghostVar_halves _ _ $$ Hs with ⟨HsA, HsB⟩
  imod dghostVar_alloc false with ⟨%γg, Hg⟩
  icases dghostVar_halves _ _ $$ Hg with ⟨HgA, HgB⟩
  imod inv_alloc nroot ⊤ (handoffInv ⟨γ, γs, γg⟩ (P ⟨γ, γs, γg⟩) Ws Wc) $$ [Hoc HsA HgA] with #Hinv
  · inext
    unfold handoffInv
    iexists .Buffered [], false, false
    iframe
    simp only [handoffMatch]
    itrivial
  imodintro
  iexists ⟨γ, γs, γg⟩
  unfold isHandoff handoffProducer handoffConsumer
  iframe
  iframe #
  ipureintro; rfl

theorem wait.list.Register.wp_proof : wait.list.Register.spec (GF := GF) (hG := hG) := by
  intro l γi γw R id Ψ
  wp_start as ⟨#Hl, Hslot, #HR⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold waitList at Hl
  icases Hl with ⟨%sl, #He, %Hlen, #Hreg, #Hsh⟩
  have hidx : 0 ≤ sint.Z (id % W64 64) ∧ sint.Z (id % W64 64) < sint.Z sl.len := by
    rw [Hlen]; word
  generalize hn : (sint.Z (id % W64 64)).toNat = n
  have hn' : sint.Z (id % W64 64) = (n : Int) := by omega
  have hn64 : n < 64 := by omega
  ihave #Hs := Hsh $$ %n %hn64
  iunfold waitShard at Hs
  icases Hs with ⟨%mref, %γs, #Hm, #Hg, #Hinv⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  (try simp only [show (W64 1 = W64 0) = False by decide, ↓reduceIte] at *)
  imod start_handoff_dep ch (fun γh => waitVal γh Ψ) iprop(True) iprop(False) γc $$ Hch Hoc
    with ⟨%γh, %Hγh, #Hh, Hp, Hc⟩
  (try wp_auto)
  (try simp only [hidx, and_self, ↓reduceIte])
  (try rw [hn'])
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hlk, HP⟩
  iunfold waitShardP at HP
  icases HP with ⟨%M, Hmap, Hga⟩
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  wp_auto
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hmap] as Hmap
  cases hM : M !! id with
  | some ch' =>
    simp only [Option.isSome_some, decide_true, Bool.not_true]
    wp_auto_lc 1
    imod waitShard_regd γw R γs id M ch' hM $$ Hinv Hlc1 Hga with ⟨Hga, %t, #Hr⟩
    imod waitReg_absurd γi γw id t $$ Hreg Hr Hslot with Hf
    iexfalso; iexact Hf
  | none =>
    wp_auto_lc 1
    simp only [hidx, and_self, ↓reduceIte]
    rw [hn']
    wp_auto
    wp_apply wp_mapInsert $$ [$Hmap] as Hmap
    imod waitReg_insert γi γw id γh.takenName $$ Hreg Hslot with #Hr
    imod waitShard_put γw R γs id M ch hM $$ Hinv Hlc1 Hga [Hp] with Hga
    · iunfold waitEntry; iexists γh, Ψ; iframe Hp; iframe #
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hga Hmap]
    · inext; iunfold waitShardP; iexists _; iframe
    (try wp_auto)
    iapply HΦ
    iexists γh
    iframe Hr
    iunfold waitRecv
    iframe Hc Hh

end proof

end EtcdGrove
end Perennial
