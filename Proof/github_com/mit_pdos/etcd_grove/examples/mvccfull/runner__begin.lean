/- Lean-first (no Rocq counterpart). The proof of `runner.begin`: proved.

The outline: `history.snapshot` (its states extend `Hs`, so its `m.rev`-th is `Hs`'s last);
`revHi.Store(m.rev + 1)` in the incarnation's invariant (`memberInv_live` with the writer's share,
`ghostVar_agree`/`update` of `m.bnd`'s halves); `copyState`; the struct allocated.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.copyState
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RestoreLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.begin.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_copyState : copyState.spec (GF := GF) (hG := hG)) :
    runner.begin.spec (GF := GF) (hG := hG) := by
  intro x ks h γh i mp m ι kv qw σ b Hs hlen hpend h62
  haveI : Persistent (isInc (GF := GF) ks γh i mp m ι kv) := by
    haveI := hpers.1; unfold isInc; infer_instance
  wp_start as ⟨Hh, Hrd, #Hlb, Hrev, Hinc⟩
  iunfold runnerH at Hh
  icases Hh with #Hh
  iunfold incW at Hinc
  icases Hinc with ⟨#HisInc, Hret, Hσw, Hbw⟩
  wp_auto
  wp_apply wp_snapshot h γh Hs $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs', ⟨%Hpre, %H2⟩, %Hscap, #Hlb', #Hms, #Hst⟩
  ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hsl := ownSlice_len $$ Hms
  have hle : Hs.length ≤ Hs'.length := Hpre.length_le
  (try wp_auto)
  have hrZ : sint.Z (W64 (σ.rev : Int)) = σ.rev := by word
  -- `m.revHi.Store(m.rev + 1)`, in the incarnation's invariant
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"revHi" mp) (W64 (σ.rev : Int) + W64 1) $$ [] [-]
  · iPkgInit
  imod bnd_acc hpers ks γh i mp m ι kv qw σ b $$ [Hret Hσw Hbw] with ⟨%Hl, %Hok, Hrl, Hrh, Hcl, Hch, Hcls⟩
  · iframe #; iframe
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN i) from Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iexists _
  iframe Hrh
  iintro Hrh
  imod Hcl2 with -
  have hplus : W64 (σ.rev : Int) + W64 1 = W64 (σ.rev + 1 : Int) := by word
  have hp1Z : sint.Z (W64 (σ.rev + 1 : Int)) = σ.rev + 1 := by word
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hok
  have hok' : bndOk ks σ (b.1, W64 (σ.rev + 1 : Int), b.2.2) Hl := by
    refine ⟨h1, h2, ?_, ?_, ?_, h6, h7, h8, h9, h10⟩
    · show (σ.rev : Int) ≤ sint.Z (W64 (σ.rev + 1 : Int)); rw [hp1Z]; omega
    · show sint.Z (W64 (σ.rev + 1 : Int)) < 2 ^ 62; rw [hp1Z]; omega
    · show (σ.notifiedLog.length : Int) ≤ sint.Z (W64 (σ.rev + 1 : Int)) + 1
      rw [hp1Z]
      have hn : σ.notifiedLog = σ.log := by unfold MvccState.notifiedLog; rw [hpend]
      rw [hn]
      have : σ.rev = σ.log.length - 1 := rfl
      omega
  rw [hplus]
  imod Hcls $$ %(b.1, W64 (σ.rev + 1 : Int), b.2.2) %hok' Hrl Hrh Hcl Hch with ⟨Hret, Hσw, Hbw⟩
  imodintro
  (try wp_auto)
  -- `st[m.rev]`: the last revision of `Hs`
  have hrev1 : 1 ≤ σ.rev := by have := h2; omega
  have hrevl : σ.rev = Hs.length - 1 := by unfold MvccState.rev at hrev1 ⊢; omega
  have hsl : sint.Z s.len = (ms.length : Int) := by
    have : sint.nat s.len = (sint.Z s.len).toNat := rfl
    omega
  have hb : 0 ≤ sint.Z (W64 (σ.rev : Int)) ∧ sint.Z (W64 (σ.rev : Int)) < sint.Z s.len := by
    rw [hrZ, hsl]; omega
  simp only [hb, _root_.and_self, ↓reduceIte]
  have hi : (sint.Z (W64 (σ.rev : Int))).toNat = σ.rev := by rw [hrZ]; omega
  have hidx : σ.rev < ms.length := by omega
  wp_apply wp_load_slice_index s (sint.Z (W64 (σ.rev : Int))) ms DFrac.discard
    (ms[σ.rev]'hidx) hb.1 $$ [Hms] as -
  · iframe #; ipureintro; rw [hi]; exact List.getElem?_eq_getElem hidx
  have hidx2 : σ.rev < Hs'.length := by omega
  have hz : (ms.zip Hs')[σ.rev]? = some (ms[σ.rev]'hidx, Hs'[σ.rev]'hidx2) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hidx2⟩
  ihave #Hm : (ms[σ.rev]'hidx ↦$□ (Hs'[σ.rev]'hidx2).1 : IProp GF) $$ [Hst]
  · iunfold statesP at Hst
    icases Hst with ⟨-, #Hst⟩
    iapply BigSepL.bigSepL_lookup hz $$ Hst
  (try wp_auto)
  wp_apply wp_copyState _ _ DFrac.discard $$ [$Hm] as %c ⟨-, Hc⟩
  (try wp_auto)
  iapply HΦ
  iframe
  isplitl [Hret Hσw Hbw]
  · iunfold incW; iframe; iframe #
  iunfold ownPending
  have hidx3 : σ.rev < Hs.length := by omega
  have hlast : lastSt Hs = (Hs'[σ.rev]'hidx2).1 := by
    obtain ⟨t, rfl⟩ := Hpre
    unfold lastSt
    rw [← hrevl, List.getElem?_eq_getElem hidx3]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getElem_append_left hidx3]
  rw [hlast]
  iexists _
  iframe
  isplitr
  · ipureintro; simp only; word
  isplitl
  · iapply ownSlice_nil
  iapply ownSliceCap_nil

end proof

end mvccfull
end EtcdGrove
end Perennial
