/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Close.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close
public import Spec.go_etcd_io.bbolt.DB__Close_kv

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

theorem backend.backend.Close.wp_proof
    (hClose : bbolt.DB.Close_kv.spec (GF := GF) (hG := hG)) :
    backend.backend.Close.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b
  wp_start as ⟨#Hb, #Hsc, Ho⟩
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t, %rt, %db, %lg, #Ht, #Hrt, #Hlg, %Hlgn, #Hmi, #Hbe, #Hm, #Hrg, #Hmug, #Hisdb, #Hci, %HP⟩
  unfold isStopChans isStopChansAt
  icases Hsc with ⟨%sc, %dc, %γsc, %γdc, #Hscf, #Hdcf, #Hscb, #Hdcb, #Hinv⟩
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdcb
  wp_auto
  wp_apply (lc := 1) wp_with_defer as %defer defer
  imod (stop_take γ sc γsc) $$ [$Hinv $Ho] with ⟨Hpend, #Hq, Hclaim⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hpend with Hpend
  wp_apply (wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
    sc γsc (stopQ γ)) $$ [$Hpend $Hq] as -
  wp_apply_core chan.wp_receive (V := Unit) dc γdc $$ Hdcc
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hdcb
  iintro ⟨#Hesc, -⟩
  -- (R2b-3c) bbolt's database out of the stop's escrow, with `Close`'s claim
  icases isBackend_dbFile γ P W Pk b $$ Hb with ⟨%db2, %path, #Hmug2, #Hisdb2, #Hdbat, #Hfile⟩
  imod (bDoneEsc_take γ sc γsc) $$ Hesc Hinv Hq Hclaim Hlc1 Hlc2 with Hout
  iunfold bDBOut at Hout
  icases Hout with ⟨%db', %C, #Hbdb, Hown⟩
  iunfold bDB at Hbdb
  icases Hbdb with ⟨%path', #Hdbat'⟩
  ihave %Hag := bDBAt_agree γ db' db2 path' path $$ [Hdbat' Hdbat]
  · iframe Hdbat' Hdbat
  obtain ⟨rfl, rfl⟩ := Hag
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmug2] as ⟨Hwl, Hdbp⟩
  wp_apply (hClose db' γ.db C path') $$ [$Hisdb2 $Hfile $Hown] as %err Herr
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $Hdbp]
  iapply HΦ
  icases Herr with (⟨%He, Hf⟩ | %Hbad)
  · ileft; iframe %He; iexists path', C; iframe Hf; iunfold bFile; iexists db'; iexact Hdbat
  · iright; ipureintro; exact Hbad

end proof

end EtcdGrove
end Perennial
