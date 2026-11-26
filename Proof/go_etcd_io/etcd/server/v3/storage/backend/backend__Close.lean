/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Close.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.DB__Close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical `DB.Close.spec` in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `DB.Close_kv`): no error (`Close`'s error case is `¬ FsNoErr`, which `theFs`'s
`FsNoErrAll` refutes); the file it gives back (`fileHoldsM`, S3g), at the inode the database kept
(`dbRestF`): `bClosed` (S5; until then, with the claim the database kept, `fileHolds`). -/
private theorem bbolt.kvGlue_DB__Close
    (h :
      bbolt.DB.Close.spec (GF := GF) (hG := hG)) :
  ∀ (db : Loc) (γ : DBNames) (D : backend.Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db γ ∗ ownDB db γ D ∗ dbHalf γ D }}
    (App (Val (db @!! go.GoType.PointerType go_etcd_io.bbolt.DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ backend.bClosed γ D }} := by
  intro db γ D
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, nex⟩
  · simp only [backend.isDB, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · have h' := h
    simp only [backend.bClosed, backend.ownDB, backend.dbHalf, backend.isDB, onFs_some hfs]
    obtain ⟨Sio, hino, hpath', hs1, hs2⟩ := nex.ok
    have hne : Fs.FsNoErr := Fs.fsNoErr_of Sio hino hpath'
    iintro %Φ ⟨-, #Hdb, ⟨-, Hst, Hrest⟩, Hh⟩ HΦ
    -- (backend-snapshot B1) the batch lock's half and the commit invariant's, the whole
    ihave Hst := (backend.boltState_halves γ D).2 $$ [Hst Hh]
    · iframe Hst Hh
    unfold dbRestF
    icases Hrest with ⟨%i, #Hino, Hcl⟩
    wp_apply (h' db γ i D) $$ [$Hdb $Hino $Hst $Hcl] as %err Hres
    icases Hres with (⟨%He, Hf⟩ | %Hbad)
    rotate_left
    · exact absurd hne Hbad
    iapply HΦ
    isplitr
    · ipureintro; exact He
    iexists i
    iframe Hino Hf

theorem backend.backend.Close.wp_proof
    (hClose :
      bbolt.DB.Close.spec (GF := GF) (hG := hG)) :
    backend.backend.Close.spec (GF := GF) (hG := hG) := by
  replace hClose := bbolt.kvGlue_DB__Close hClose
  intro γ P W Pk b X Y
  wp_start as ⟨#Hb, #Hsc, Ho, HX, #Hreq⟩
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t, %rt, %db, %lg, #Ht, #Hrt, #Hlg, #Hlgn, #Hmi, #Hbe, #Hm, #Hrg, #Hmug, #Hisdb, #Hci, %HP⟩
  unfold isStopChans isStopChansAt
  icases Hsc with ⟨%sc, %dc, %γsc, %γdc, #Hscf, #Hdcf, #Hscb, #Hdcb, #Hinv⟩
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdcb
  wp_auto
  wp_apply (lc := 2) wp_with_defer as %defer defer
  imod (stop_take γ P Pk b sc γsc X Y) $$ [$Hinv $Ho $HX $Hreq $Hlc1] with ⟨Hpend, #Hq, Hclaim, Hrq⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc2 Hpend with Hpend
  wp_apply (wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
    sc γsc (stopQ γ)) $$ [$Hpend $Hq] as -
  wp_apply_core chan.wp_receive (V := Unit) dc γdc $$ Hdcc
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hdcb
  iintro ⟨#Hesc, -⟩
  -- (R2b-3c) bbolt's database out of the stop's escrow, with `Close`'s claim
  icases isBackend_dbFile γ P W Pk b $$ Hb with ⟨%db2, %path, #Hmug2, #Hisdb2, #Hdbat, #Hfile⟩
  imod (bDoneEsc_take γ P W Pk b sc γsc) $$ Hesc Hinv Hq Hclaim Hlc1 Hlc2 with ⟨Hout, %Y', Hrq', HY'⟩
  -- (R2b-3d stage 3) the request's result, by the saved proposition's halves
  ihave #Heq := saved_prop_agree γ.rq _ _ Y Y' $$ Hrq Hrq'
  ihave HY : ▷ Y $$ [HY']
  · inext
    ihave Hiff := internalEq_iff _ _ $$ Heq
    icases Hiff with ⟨-, Hiff⟩
    iapply Hiff $$ HY'
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc3 HY with HY
  iunfold bDBOut at Hout
  iunfold bDBOutG at Hout
  icases Hout with ⟨⟨%db', %C, #Hbdb, Hown, Hhalf, Hg⟩, HW, HPk⟩
  -- (R2b-3c part 2) what the stopped lock held, at the committed data
  ihave Hsv := bStopG_view γ P W Pk C $$ [$Hg $HW $HPk]
  iunfold bDB at Hbdb
  icases Hbdb with ⟨%path', #Hdbat'⟩
  ihave %Hag := bDBAt_agree γ db' db2 path' path $$ [Hdbat' Hdbat]
  · iframe Hdbat' Hdbat
  obtain ⟨rfl, rfl⟩ := Hag
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmug2] as ⟨Hwl, Hdbp⟩
  wp_apply (hClose db' γ.db C) $$ [$Hisdb2 $Hown $Hhalf] as %err ⟨%He, Hf⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $Hdbp]
  iapply HΦ
  iframe HY
  iexists C
  iframe Hsv
  ileft; iframe %He; iframe Hf

end proof

end EtcdGrove
end Perennial
