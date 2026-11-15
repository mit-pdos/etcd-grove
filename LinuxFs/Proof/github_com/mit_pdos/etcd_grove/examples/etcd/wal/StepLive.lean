/- Lean-first (no Rocq counterpart).

**The running member between operations, rebuilt** (W4c U5, tenth session): `memLive` from its parts
(`memLive_intro`), and from a successful `save`-based operation's postcondition with the fields it left
(`memLive_post`). `member.step`'s arms use them.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberInv

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section pure
variable [GooseExts]

theorem tOrSmall_of_room {o : TOracle} (h : tOrRoom o 0) : tOrSmall o := by
  unfold tOrRoom at h; unfold tOrSmall; omega

/-- **`step`'s room gives a save's oracle its well-formedness.** -/
theorem tCheckWf_step {o : TOracle} (hw : tCheckWf o) (hr : tOrRoom o 256) (h : THs) {es : List TEnt}
    (hl : es.length ≤ 4) (hes : ∀ x ∈ es, tEntWf x) (ht : uint.nat h.term' < 2 ^ 63) :
    tCheckWf (tSaveO o h es) :=
  tCheckWf_saveO hw h es hes ht (tOrSmall_of_room (tOrRoom_saveO (tOrRoom_mono hr (by omega)) h))

end pure

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- The member's raft-like fields and choice source. -/
def memFields (m : Loc) (t vo cm bs l : w64) (tm : Loc) (M : GMap w64 w64) (r : Loc) (rv : rnd) :
    IProp GF :=
  iprop(m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
    m.[member, go!"base"] ↦ bs ∗ m.[member, go!"last"] ↦ l ∗ m.[member, go!"terms"] ↦ tm ∗
    tm ↦$ M ∗ m.[member, go!"r"] ↦ r ∗ r ↦ rv)

theorem memLive_intro (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle)
    (c : TCand) (d : WalDur) (qc : Qp) (t vo cm bs l : w64) (tm : Loc) (M : GMap w64 w64) (r : Loc)
    (rv : rnd) (hok : tMemOk o c d) (hhs : tMemHs o d) (hfl : tMemFields t M) (hcw : tCheckWf o)
    (hms : tMemSim o c bs l cm) :
    memSaveRes W e γ m w v o os c d qc ∗ memFields m t vo cm bs l tm M r rv ∗
      WalFs.walPurgeW (W := W) w (tWalDir e.area) ⊢ memLive W e γ m qc o := by
  iintro ⟨Hres, Hf, Hpw⟩
  iunfold memFields at Hf
  icases Hf with ⟨Ht, Hv, Hc, Hb, Hl, Htm, HM, Hr, Hrv⟩
  iunfold memLive
  iexists w, v, os, c, d, t, vo, cm, bs, l, tm, M, r, rv
  iframe
  ipureintro; exact ⟨hok, hhs, hfl, hcw, hms⟩

/-- **A successful `save`-based operation leaves a running member.** -/
theorem memLive_post (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (o : TOracle) (c : TCand) (qc : Qp)
    (h : THs) (es : List TEnt) (t vo cm bs l : w64) (tm : Loc) (M : GMap w64 w64) (r : Loc) (rv : rnd)
    (hfl : tMemFields t M) (hcw : tCheckWf (tSaveO o h es)) (hms : tMemSim (tSaveO o h es) c bs l cm) :
    memSavePers W e γ ∗ memSavePost W e γ m w o c qc h es true ∗ memFields m t vo cm bs l tm M r rv ∗
      WalFs.walPurgeW (W := W) w (tWalDir e.area) ⊢ memLive W e γ m qc (tSaveO o h es) := by
  iintro ⟨#Hp, Hpost, Hf, Hpw⟩
  ihave Hres := memSaveRes_post W e γ m w o c qc h es $$ [$Hp $Hpost]
  icases Hres with ⟨%v', %os', %d', Hres, %Hok⟩
  iapply memLive_intro W e γ m w v' (tSaveO o h es) os' c d' qc t vo cm bs l tm M r rv Hok.1 Hok.2 hfl
    hcw hms
  iframe

theorem osCallPerm_join2 :
    osCallPerm (L := hG.goose_localGS) (1 : Qp).half ∗ osCallPerm (L := hG.goose_localGS) (1 : Qp).half ⊢
      osCallPerm (L := hG.goose_localGS) 1 := by
  have h := osCallPerm_split (L := hG.goose_localGS) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.2

end rep

end etcd_wal
end EtcdGrove
end Perennial
