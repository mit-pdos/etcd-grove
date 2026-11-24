/- ReadAll's earlier-file probe. A non-crashed Go step reserves the segment
before the call and the next such step returns it after the deferred close. -/
module
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPrefixAccess
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.segmentContainsSnapshot

@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove.WalFs
open Iris Iris.BI Iris.ProofMode Fs WalEnc
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [go.Semantics] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

def probeHandles (R : Roots) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH)
    (qd qc : Qp) (o : WalOut) (γ : GName) (Lk : GMap GoString Nat) : IProp GF :=
  iprop(osPathS R dir (DFrac.own qd) j ∗ osCallPerm (callKey R dir) qc ∗
    osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗ walOutFrag (W := W) o ∗
    walTailsFrag (W := W) (<[dir := γ]> ∅) Lk)

/-- The previous probe's file can be returned before the next Go step. -/
def probeAccess (P : IProp GF) : IProp GF :=
  iprop(notCrashed (hC := hG.goose_localGS.goose_crashGS) ={⊤}=∗
    notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ P)

def prefixScanState (R : Roots) (jr : Ino) (r dir : GoString) (j : Ino) (X : List GoString)
    (hj : NamesH) (qd qc : Qp) (o : WalOut) (γ : GName) (Lk : GMap GoString Nat)
    (M : WalMarshal) (lg : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
    osInv ∗ osSharedInv R ∗ walInv (L := hG.goose_localGS) (W := W) walCodec M R jr r ∗
    walDirKey (W := W) dir j X ∗ probeAccess (probeHandles R dir j X hj qd qc o γ Lk))

theorem readAll_prefix_file (M : WalMarshal) (U : WalUnmarshal) (hU : U.Ok M)
    (wp_probe : wal.segmentContainsSnapshot.spec (GF := GF) U)
    (R : Roots) (jr : Ino) (r dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH)
    (qd qc : Qp) (γ : GName) (Lk : GMap GoString Nat) (gs : List SegG) (o : WalOut)
    (lg : Loc) (k i : Nat) (name : GoString) (index : w64)
    (hdir : PathFits dir) (hX : ∀ b ∈ X, walNameP b = false)
    (ho : o.O = gs.map (·.ino)) (hi : i < k) (hk : k < (walNames hj.cur).length)
    (hn : (walNames hj.cur)[i]? = some name) (hdrop : (walNames hj.cur).drop k = gs.map (·.name))
    (hnm : ∀ g ∈ gs, hj.cur !! g.name = some (.file g.ino))
    (hhead : ∀ nm, (walNames hj.cur)[k]? = some nm → ∀ sq ix,
      nm = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat index) :
    wal.prefixFileMiss (prefixScanState (W := W) R jr r dir j X hj qd qc o γ Lk M lg) lg dir name index := by
  iintro %Φ HP HΦ
  iunfold prefixScanState at HP
  icases HP with ⟨#Hpkg, #Hzap, #Hoi, #Hsi, #Hinv, #Hk, Hget⟩
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  iunfold probeAccess at Hget
  imod Hget $$ Hnc with ⟨Hnc, HP⟩
  iunfold probeHandles at HP
  icases HP with ⟨Hpd, Hperm, Hn, Ho, Htf⟩
  imod walInv_open walCodec M R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc
    with ⟨⟨%st, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_takeProbe M U hU R jr r st dir j X hj _ Lk gs o k i name index
    ho hi hk hn hdrop hnm hhead $$ Hb Hk Hn Htf Ho with
    ⟨Hb, Hn, Htf, %g, ⟨%hname, %hino, %hsize, %hok, %hlen, %hp, %hbelow⟩, Ho, Hg⟩
  imod Hcl $$ [Hb] with -
  · iexists st; iexact Hb
  imodintro; iframe Hnc
  have hm : (NameSet.except X).Mem g.name := by
    intro hx
    have hf := hX g.name hx
    rw [hp] at hf; cases hf
  have wp := wp_probe lg R dir j (DFrac.own qd) qc (.except X) (DFrac.own (1 : Qp).half) hj g index
    hdir hm hok hlen (hname ▸ hino) hsize hbelow
  unfold wal.prefixFileMiss at wp
  rw [← hname]
  wp_apply wp $$ [Hg Hpd Hperm Hn] as %e HH
  · unfold wal.probeOwn; iframe; iframe #
  icases HH with ⟨-, -, -, -, HH⟩
  iunfold wal.probeOwn at HH
  icases HH with ⟨Hpd, Hperm, Hn, Hg⟩
  iapply HΦ
  unfold prefixScanState
  iframe Hpkg Hzap Hoi Hsi Hinv Hk
  unfold probeAccess
  iintro Hnc
  imod walInv_open walCodec M R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc
    with ⟨⟨%st', Hb⟩, Hnc, Hcl⟩
  imod walInvBody_putProbe M R jr r st' dir j X hj γ Lk gs o k i name g ho hi hk hn hdrop hnm hino hsize
    $$ Hb Hk Hn Htf [Ho Hg] with ⟨Hb, Hn, Htf, Ho⟩
  · iframe
  imod Hcl $$ [Hb] with -
  · iexists st'; iexact Hb
  imodintro; unfold probeHandles; iframe

end Perennial.EtcdGrove.WalFs
