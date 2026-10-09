/-
Proof of `Spec/demux__Init.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__Init
public import Spec.go_etcd_io.etcd.cache.v3.demux__purge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-- `DemuxInv` of a reset state with some `minRev`. -/
theorem demuxInit_inv_reset {cap : Nat} {c : DemuxCore} (Hinv : DemuxInv cap c) (m : w64) :
    DemuxInv cap { DemuxCore.init with minRev := m, base := sint.Z m - 1 } := by
  constructor <;> (try simp [DemuxCore.init]) <;>
    first | omega | exact Hinv.cap_pos | exact Hinv.cap_le | exact ⟨by simp, by simp [RevSorted], by simp⟩ | word

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.Init.wp_proof (wp_purge : demux.purge.spec (GF := GF) (hG := hG)) :
    demux.Init.spec (GF := GF) (hG := hG) := by
  intro d γd cap C c m
  wp_start as ⟨#Hd, Hw⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxWriter
  icases Hw with ⟨Hgw, Hmu, %Hinv⟩
  unfold demuxHandle
  wp_apply (lc := 3) sync.RWMutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
  icombine Hlc1 Hlc2 as Hlc12
  imod demux_lock_acquire d γd cap $$ [$Hd $HP $Hlc12] with ⟨%c', %regs, %views, Hcore, Hl, %Hinv'⟩
  icombine Hgw Hcore gives % ⟨_, Heq⟩
  subst Heq
  iNamed Hl
  wp_if_destruct
  · -- `minRev == 0`: nothing
    have Hc : (initCore c (W64 0)).1 = c := by simp [initCore]
    ihave Hl : demuxLocked d γd cap C c c.stream.length regs views $$
      [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
    · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
    imod demux_lock_release d γd cap c regs views $$ [$Hd $Hcore $Hl $Hlc3] with HP
    · ipureintro; exact Hinv
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hmu
    iapply HΦ
    rw [Hc]
    iframe
    ipureintro; exact Hinv
  rename ¬m = W64 0 => Hm0
  wp_if_destruct
  · -- `d.minRev == 0`: set it
    obtain ⟨Hs, Hmx⟩ := Hinv.uninit Hif
    have Hh : c.history = [] := by
      have := Hinv.hist_suffix; rw [Hs] at this; exact List.eq_nil_of_suffix_nil this
    have Hc : (initCore c m).1 = { DemuxCore.init with minRev := m, base := sint.Z m - 1 } := by
      rw [initCore, if_neg Hm0, if_pos Hif]; cases c; simp_all [DemuxCore.init]
    have Hc' : { c with minRev := m, base := sint.Z m - 1 } = { DemuxCore.init with minRev := m, base := sint.Z m - 1 } := by
      cases c; simp_all [DemuxCore.init]
    have Hinv'' : DemuxInv cap { c with minRev := m, base := sint.Z m - 1 } := by
      rw [Hc']; exact demuxInit_inv_reset Hinv m
    have Hok' : RegsOk { c with minRev := m, base := sint.Z m - 1 } c.stream.length regs views :=
      ⟨Hok.dom, Hok.mapped, Hok.active_up⟩
    ihave Hl : demuxLocked d γd cap C { c with minRev := m, base := sint.Z m - 1 }
        ({ c with minRev := m, base := sint.Z m - 1 } : DemuxCore).stream.length regs views $$
      [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
    · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe
      isplitr
      · rw [Hs]; iapply (certChain_nil (GF := GF) (C := C) _)
      ipureintro; exact ⟨Hok', RegsStart.uninit Hstart Hif⟩
    imod ghostVar_update_halves ({ c with minRev := m, base := sint.Z m - 1 }) γd.core c c $$ Hgw Hcore with ⟨Hgw, Hcore⟩
    imod demux_lock_release d γd cap ({ c with minRev := m, base := sint.Z m - 1 }) regs views $$ [$Hd $Hcore $Hl $Hlc3] with HP
    · ipureintro; exact Hinv''
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hmu
    iapply HΦ
    rw [Hc, ← Hc']
    iframe
    ipureintro; exact Hinv''
  rename ¬c.minRev = W64 0 => Hmin0
  wp_if_destruct
  · -- `d.maxRev == 0`: purge, set `minRev`
    ihave Hl : demuxLocked d γd cap C c c.stream.length regs views $$
      [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
    · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
    iclear Hcerts
    wp_apply wp_purge $$ [$Hl] as ⟨%views', Hl⟩
    · ipureintro; exact Hinv
    have Hc : (initCore c m).1 = { DemuxCore.init with minRev := m, base := sint.Z m - 1 } := by
      rw [initCore, if_neg Hm0, if_neg Hmin0, if_pos Hif]
    have Hinv'' := demuxInit_inv_reset Hinv m
    iNamed Hl
    wp_auto
    ihave Hl : demuxLocked d γd cap C { DemuxCore.init with minRev := m, base := sint.Z m - 1 }
        ({ DemuxCore.init with minRev := m, base := sint.Z m - 1 } : DemuxCore).stream.length regs views' $$
      [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
    · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe
      isplitr
      · dsimp only [DemuxCore.init]; iapply (certChain_nil (GF := GF) (C := C) _)
      ipureintro
      exact ⟨⟨Hok.dom, Hok.mapped, Hok.active_up⟩, RegsStart.uninit Hstart rfl⟩
    imod ghostVar_update_halves ({ DemuxCore.init with minRev := m, base := sint.Z m - 1 }) γd.core c c $$ Hgw Hcore with ⟨Hgw, Hcore⟩
    imod demux_lock_release d γd cap ({ DemuxCore.init with minRev := m, base := sint.Z m - 1 }) regs views' $$ [$Hd $Hcore $Hl $Hlc3] with HP
    · ipureintro; exact Hinv''
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hmu
    iapply HΦ
    rw [Hc]
    iframe
    ipureintro; exact Hinv''
  rename ¬c.maxRev = W64 0 => Hmax0
  wp_if_destruct
  · -- `minRev == d.maxRev + 1`: nothing
    have Hc : (initCore c (c.maxRev + W64 1)).1 = c := by
      rw [initCore, if_neg Hm0, if_neg Hmin0, if_neg Hmax0, if_pos rfl]
    ihave Hl : demuxLocked d γd cap C c c.stream.length regs views $$
      [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
    · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
    imod demux_lock_release d γd cap c regs views $$ [$Hd $Hcore $Hl $Hlc3] with HP
    · ipureintro; exact Hinv
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hmu
    iapply HΦ
    rw [Hc]
    iframe
    ipureintro; exact Hinv
  -- otherwise: purge, set `minRev`
  rename ¬m = c.maxRev + W64 1 => Hne
  ihave Hl : demuxLocked d γd cap C c c.stream.length regs views $$
    [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
  · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
  iclear Hcerts
  wp_apply wp_purge $$ [$Hl] as ⟨%views', Hl⟩
  · ipureintro; exact Hinv
  have Hc : (initCore c m).1 = { DemuxCore.init with minRev := m, base := sint.Z m - 1 } := by
    rw [initCore, if_neg Hm0, if_neg Hmin0, if_neg Hmax0, if_neg Hne]
  have Hinv'' := demuxInit_inv_reset Hinv m
  iNamed Hl
  wp_auto
  ihave Hl : demuxLocked d γd cap C { DemuxCore.init with minRev := m, base := sint.Z m - 1 }
      ({ DemuxCore.init with minRev := m, base := sint.Z m - 1 } : DemuxCore).stream.length regs views' $$
    [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
  · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe
    isplitr
    · dsimp only [DemuxCore.init]; iapply (certChain_nil (GF := GF) (C := C) _)
    ipureintro
    exact ⟨⟨Hok.dom, Hok.mapped, Hok.active_up⟩, RegsStart.uninit Hstart rfl⟩
  imod ghostVar_update_halves ({ DemuxCore.init with minRev := m, base := sint.Z m - 1 }) γd.core c c $$ Hgw Hcore with ⟨Hgw, Hcore⟩
  imod demux_lock_release d γd cap ({ DemuxCore.init with minRev := m, base := sint.Z m - 1 }) regs views' $$ [$Hd $Hcore $Hl $Hlc3] with HP
  · ipureintro; exact Hinv''
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hmu
  iapply HΦ
  rw [Hc]
  iframe
  ipureintro; exact Hinv''

end proof

end EtcdGrove
end Perennial
