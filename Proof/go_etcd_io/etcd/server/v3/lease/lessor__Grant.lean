/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Grant.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLease
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__isPrimary
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__refresh
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__forever
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__persistTo
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__RegisterOrUpdate
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__scheduleCheckpointIfNeeded
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Grant.wp_proof
    (hNew : lease.NewLease.spec (GF := GF) (hG := hG))
    (hPrim : lease.lessor.isPrimary.spec (GF := GF) (hG := hG))
    (hRefresh : lease.Lease.refresh.spec (GF := GF) (hG := hG))
    (hForever : lease.Lease.forever.spec (GF := GF) (hG := hG))
    (hPersist : lease.Lease.persistTo.spec (GF := GF) (hG := hG))
    (hReg : lease.LeaseExpiredNotifier.RegisterOrUpdate.spec (GF := GF) (hG := hG))
    (hSched : lease.lessor.scheduleCheckpointIfNeeded.spec (GF := GF) (hG := hG)) :
    lease.lessor.Grant.spec (GF := GF) (hG := hG) := by
  intro lp γl id ttl L P f Pre Q Post
  wp_start as ⟨#Hinv, #Hcfg, #Hbe, Hown, Hcs⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨#Hnf, #Hex, #Htl, -, ⟨%cg, #Hcg, #Hcgs⟩, -, ⟨%ht, #Hht, #Hhts⟩⟩
  ihave #Hnf' := Hnf
  iunfold leaseErrVar at Hnf'
  icases Hnf' with ⟨%enf, #Henf, -⟩
  ihave #Hex' := Hex
  iunfold leaseErrVar at Hex'
  icases Hex' with ⟨%eex, #Heex, -⟩
  ihave #Htl' := Htl
  iunfold leaseErrVar at Htl'
  icases Htl' with ⟨%etl, #Hetl, -⟩
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu⟩
  ihave #Hcfg' := Hcfg
  iunfold lessorCfg at Hcfg'
  icases Hcfg' with ⟨%mt, %cpp, %cl, %ci, %lg, %rr, #Hmt, #Hcpp, #Hcl, #Hclok, #Hci, #Hlg, -⟩
  ihave #Hbe' := Hbe
  iunfold lessorBackend at Hbe'
  icases Hbe' with ⟨%b, #Hb, #Hbk⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_if_destruct
  · -- `id == NoLease`
    (try wp_auto)
    iapply HΦ
    ileft
    iunfold mvcc.csContract at Hcs
    icases Hcs with ⟨HPre, -, -⟩
    iframe Hown HPre
    isplitr
    · ipureintro; intro h; cases h
    iunfold lessorErrIs
    iexists ErrLeaseNotFound, enf
    iframe Henf
    ipureintro; exact ⟨Or.inl rfl, rfl⟩
  (try wp_auto)
  wp_if_destruct
  · -- `ttl > MaxLeaseTTL`
    (try wp_auto)
    iapply HΦ
    ileft
    iunfold mvcc.csContract at Hcs
    icases Hcs with ⟨HPre, -, -⟩
    iframe Hown HPre
    isplitr
    · ipureintro; intro h; cases h
    iunfold lessorErrIs
    iexists ErrLeaseTTLTooLarge, etl
    iframe Hetl
    ipureintro; exact ⟨Or.inr (Or.inr rfl), rfl⟩
  (try wp_auto)
  wp_apply hNew as %l ⟨%Hlnn, HID, Httl, Hrem, HexMu, Hexp, Hmu0, ⟨%sm, HiS, Hsm⟩, ⟨%rc, Hrc⟩⟩
  ipersist HID
  ipersist Hrc
  -- the new lease's locks
  icases ptsto_halves_split _ _ $$ Hexp with ⟨Hexp, HexpG⟩
  imod (sync.init_RWMutex (leaseExpiry l) (E := ⊤) (lsF go!"expiryMu" l)) $$ [HexpG] HexMu
    with HexRs
  · inext; iunfold leaseExpiry; iexists _; iexact HexpG
  have hmax : sync.rwmutex.actualMaxReaders.toNat = (sync.rwmutex.actualMaxReaders.toNat - 1) + 1 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  rw [hmax, List.replicate_succ]
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HexRs with ⟨HexR, -⟩
  icases sync.ownRWMutex_guard _ _ $$ HexR with ⟨-, #HexG⟩
  imod (sync.init_RWMutex (leaseItems l) (E := ⊤) (lsF go!"mu" l)) $$ [HiS Hsm] Hmu0
    with HmuRs
  · inext; iunfold leaseItems; iexists sm, ∅; iframe
  rw [hmax, List.replicate_succ]
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HmuRs with ⟨HmuR, -⟩
  icases sync.ownRWMutex_guard _ _ $$ HmuR with ⟨-, #HmuG⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hls, Hx⟩
  iunfold leaseOwn at Hown
  ihave %Hag := leaseFrag_agree γl _ _ _ _ $$ [$Hown $Hg]
  subst Hag
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %cp, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta⟩
  (try wp_auto)
  wp_apply (wp_map_lookup2 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  cases hM : M !! id with
  | some l0 =>
    simp only [Option.getD_some, Option.isSome_some, decide_true]
    (try wp_auto)
    ihave Hx : lessorExtra lp M 1 $$ [Hdc Hnp Hnot Hh Hhq Hcp Hmeta]
    · iunfold lessorExtra; iexists dc, np, h, hx, cp; iframe
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hls
      ipureintro; exact HL
    iapply HΦ
    ileft
    iunfold mvcc.csContract at Hcs
    icases Hcs with ⟨HPre, -, -⟩
    iunfold leaseOwn
    iframe Hown HPre
    isplitr
    · ipureintro; intro h; cases h
    iunfold lessorErrIs
    iexists ErrLeaseExists, eex
    iframe Heex
    ipureintro; exact ⟨Or.inr (Or.inl rfl), rfl⟩
  | none =>
    simp only [Option.isSome_none]
    (try wp_auto)
    have hnot : id ∉ L := by
      intro h; have := (HL id).1 h; rw [hM] at this; cases this
    -- `if l.ttl < le.minLeaseTTL { l.ttl = le.minLeaseTTL }`
    wp_join iprop(le_ptr ↦ lp ∗ l_ptr ↦ l ∗ ∃ t : w64, lsF go!"ttl" l ↦ t) with [le l Httl]
      as ⟨le, l, %t, Httl⟩
    ipersist Httl
    wp_apply (hPrim lp dc (DFrac.own 1)) $$ [$Hdc] as Hdc
    wp_join iprop(l_ptr ↦ l ∗ lsF go!"remainingTTL" l ↦ (W64 0) ∗
        ∃ e : _root_.Perennial.time.Time, lsF go!"expiry" l ↦{DFrac.own (1 : Qp).half} e)
      with [l Hrem Hexp] as ⟨l, Hrem, %e, Hexp⟩
    · (try wp_auto)
      wp_apply (hForever l _) $$ [$Hpkg $Hexp $HexG] as Hexp
      wp_join_done
    · (try wp_auto)
      wp_apply (hRefresh l (W64 0) (W64 0) t (DFrac.own 1) DFrac.discard _) $$
        [$Hpkg $Hrem $Httl $Hexp $HexG] as ⟨Hrem, -, Hexp⟩
      wp_join_done
    wp_apply (wp_mapInsert LeaseID.ty lm M id l) $$ HM as HM
    wp_apply (hPersist l b P f Pre Q Post id t (W64 0) DFrac.discard DFrac.discard (DFrac.own 1))
      $$ [$Hpkg $Hbk $Hcs $HID $Httl $Hrem] as ⟨HPost, -, -, Hrem⟩
    (try wp_auto)
    iunfold go_etcd_io.etcd.server.v3.storage.backend.histSpec at Hhts
    icases Hhts with #Hhts
    wp_apply Hhts
    (try wp_auto)
    iunfold counterSpec at Hcgs
    icases Hcgs with #Hcgs
    wp_apply Hcgs
    (try wp_auto)
    wp_apply (hPrim lp dc (DFrac.own 1)) $$ [$Hdc] as Hdc
    wp_join iprop(le_ptr ↦ lp ∗ l_ptr ↦ l ∗ lsF go!"remainingTTL" l ↦ (W64 0) ∗
        lsF go!"expiry" l ↦{DFrac.own (1 : Qp).half} e ∗
        lF go!"leaseExpiredNotifier" lp ↦ np ∗ notifierAt np 1 ∗ lF go!"cp" lp ↦ cp ∗
        ∃ (h' : GoSlice) (hx' : List (Loc × w64)), lF go!"leaseCheckpointHeap" lp ↦ h' ∗
          queueAt h' hx' 1)
      with [le l Hrem Hexp Hnp Hnot Hcp Hh Hhq]
      as ⟨le, l, Hrem, Hexp, Hnp, Hnot, Hcp, %h', %hx', Hh, Hhq⟩
    · (try wp_auto)
      iStructNamed «$r0»
      ipersist id
      wp_apply (hReg np «$r0_ptr» id (W64 0)) $$ [$Hpkg $Hnot id time index] as Hnot
      · iunfold lwtAt; iframe; iframe #
      (try wp_auto)
      wp_apply (hSched lp l cp h hx (W64 0) t (DFrac.own 1) (DFrac.own 1) DFrac.discard)
        $$ [$Hpkg $Hcfg $Hcp $Hh $Hhq $Hrem $Httl] as ⟨Hcp, ⟨%h', %hx', Hh, Hhq⟩, Hrem, -⟩
      wp_join_done
    (try wp_auto)
    -- the live set grows; the lessor's state with the new lease
    imod lessor_live_update γl lp L (L ++ [id]) $$ [$Ha $Hg $Hown] with ⟨Ha, Hg, Hown⟩
    ihave Hml : leaseMeta id l 1 $$ [Hrem Hexp]
    · iunfold leaseMeta
      iframe HID HexG
      isplitr
      · iexists t; iexact Httl
      isplitr
      · iexists rc; iexact Hrc
      isplitl [Hrem]
      · iexists _; iexact Hrem
      iexists _; iexact Hexp
    ihave #Hlo : isLeaseObj l $$ []
    · iunfold isLeaseObj; iframe HmuG; ipureintro; exact Hlnn
    ihave Hmeta := (BigSepM.bigSepM_insert (Φ := fun i x => leaseMeta (GF := GF) i x 1) hM).2
      $$ [$Hml $Hmeta]
    ihave #Hls' := (BigSepM.bigSepM_insert (Φ := fun _ x => isLeaseObj (GF := GF) x) hM).2
      $$ [$Hlo $Hls]
    ihave Hx : lessorExtra lp (<[id := l]> M) 1 $$ [Hdc Hnp Hnot Hh Hhq Hcp Hmeta]
    · iunfold lessorExtra; iexists dc, np, h', hx', cp; iframe
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, (<[id := l]> M), I, rd0, (L ++ [id])
      iframe
      iframe Hls'
      ipureintro
      intro x
      rw [GMap.lookup_insert_is_Some, List.mem_append, List.mem_singleton, HL x]
      constructor
      · rintro (h | rfl)
        · by_cases hx : id = x
          · left; exact hx
          · right; exact ⟨hx, h⟩
        · left; rfl
      · rintro (rfl | ⟨_, h⟩)
        · right; rfl
        · left; exact h
    iapply HΦ
    iright
    iunfold leaseOwn
    iframe Hown HPost HID
    isplitr
    · ipureintro; exact ⟨rfl, Hlnn, hnot⟩
    iexists t; iexact Httl

end proof

end EtcdGrove
end Perennial
