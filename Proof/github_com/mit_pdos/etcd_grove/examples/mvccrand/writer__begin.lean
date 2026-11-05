/- Lean-first (no Rocq counterpart). The proof of `writer.begin`: the snapshot is the writer's
revisions exactly (its lower bound and its half of the list), so `len(st) - 1` is the published
revision and `st[cur]` the last state, which `copyState` copies. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__cur
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.copyState
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.begin.wp_proof (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_cur : writer.cur.spec (GF := GF) (hG := hG))
    (wp_copyState : copyState.spec (GF := GF) (hG := hG)) :
    writer.begin.spec (GF := GF) (hG := hG) := by
  intro w wv dq γ σ Hs
  wp_start as ⟨Hw, Hrd, #Hinv, Hidle⟩
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  obtain ⟨Hpend, Hlen, Hbound, Hmatch⟩ := Hid
  icases histW_lb γ.h Hs $$ HW with ⟨HW, #Hlb⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hw with ⟨Hw, %Hwnn⟩
  iStructNamedSuffix Hw "W"
  wp_auto
  wp_apply wp_snapshot wv.h' γ.h Hs $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs', %Hpre, #Hlb', #Hms, #Hst⟩
  -- the snapshot is the writer's revisions
  ihave %Hle : ⌜Hs' <+: Hs⌝ $$ [HW]
  · iunfold histW at HW
    icases HW with ⟨%x, %Hx, -, Hl, -, -⟩
    ihave %H := mono_list_auth_lb_valid γ.h.l _ _ _ $$ Hl Hlb'
    ipureintro; exact H.2
  have hHs : Hs' = Hs := List.IsPrefix.eq_of_length Hle (Nat.le_antisymm Hle.length_le Hpre.1.length_le)
  subst hHs
  ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hsl := ownSlice_len $$ Hms
  have h2 := Hpre.2
  (try wp_auto)
  have hrev : σ.rev = Hs'.length - 1 := by unfold MvccState.rev; omega
  ihave Hw : w ↦{dq} wv $$ [kvW leW hW rW leasesW nextIDW valsW applyingW savedW ticksW]
  · iapply typedPointsto_combine _ _ _ Hwnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  wp_apply wp_cur w wv dq γ (W64 (σ.rev : Int)) $$ [$Hw $Hinv $Hpv] as ⟨Hw, Hpv⟩
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; rw [hrev]
    have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    word
  (try wp_auto)
  have hsl : sint.Z s.len = (Hs'.length : Int) := by
    have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    omega
  have hb : 0 ≤ sint.Z (s.len - W64 1) ∧ sint.Z (s.len - W64 1) < sint.Z s.len := by
    constructor <;> word
  simp only [hb, _root_.and_self, ↓reduceIte]
  have hi : (sint.Z (s.len - W64 1)).toNat = Hs'.length - 1 := by word
  have hidx : Hs'.length - 1 < ms.length := by omega
  wp_apply wp_load_slice_index s (sint.Z (s.len - W64 1)) ms DFrac.discard
    (ms[Hs'.length - 1]'hidx) hb.1 $$ [Hms] as -
  · iframe #; ipureintro; rw [hi]; exact List.getElem?_eq_getElem hidx
  -- the last state's map
  have hidx2 : Hs'.length - 1 < Hs'.length := by omega
  have hz : (ms.zip Hs')[Hs'.length - 1]? = some (ms[Hs'.length - 1]'hidx, Hs'[Hs'.length - 1]'hidx2) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hidx2⟩
  ihave #Hm : (ms[Hs'.length - 1]'hidx ↦$□ (Hs'[Hs'.length - 1]'hidx2).1 : IProp GF) $$ [Hst]
  · iunfold statesP at Hst
    icases Hst with ⟨-, #Hst⟩
    iapply BigSepL.bigSepL_lookup hz $$ Hst
  (try wp_auto)
  wp_apply wp_copyState _ _ DFrac.discard $$ [$Hm] as %c ⟨-, Hc⟩
  (try wp_auto)
  iapply HΦ
  iframe
  iunfold writerIdle
  iframe
  isplitr
  · ipureintro; exact ⟨Hpend, Hlen, Hbound, Hmatch⟩
  iunfold ownPending
  have hlast : lastSt Hs' = (Hs'[Hs'.length - 1]'hidx2).1 := by
    unfold lastSt; rw [List.getElem?_eq_getElem hidx2]; rfl
  rw [hlast]
  iexists _
  iframe
  isplitr
  · ipureintro; simp only; word
  isplitl
  · iapply ownSlice_nil
  iapply ownSliceCap_nil

end proof

end mvccrand
end EtcdGrove
end Perennial
