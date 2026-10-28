/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/startStreamWriter.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startStreamWriter
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__run

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.startStreamWriter.wp_proof
    (hRun : rafthttp.streamWriter.run.spec (GF := GF) (hG := hG)) :
    rafthttp.startStreamWriter.spec (GF := GF) (hG := hG) := by
  intro Rh ty lid pid Rr lg ps fs r γd
  wp_start as ⟨%Hlgnn, #Hps, %Hfsnn, #Hraft, HR⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 4096))
  · ipureintro; exact ⟨by decide, by decide⟩
  iintro %mc %γm ⟨#Hmcc, %Hcap, Hmo⟩
  simp only [show ¬ (W64 4096 = W64 0) by decide, ↓reduceIte]
  imod start_bag (swMsg Rh ty lid pid) _ mc γm (by trivial) $$ Hmcc Hmo with #Hbag
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Loc) as %cc %γc ⟨#Hccc, %-, Hcco⟩
  imod start_bag (outConnOk Rh ty lid pid) _ cc γc (by trivial) $$ Hccc Hcco with #Hcbag
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %sc %γs ⟨#Hscc, %-, Hsco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γs sc $$ Hscc Hsco with Hsb
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %dc %γdn ⟨#Hdcc, %-, Hdco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γdn dc $$ Hdcc Hdco with Hdb
  (try wp_auto)
  iStructNamed «$r0»
  ipersist lg; ipersist localID; ipersist peerID; ipersist status; ipersist fs; ipersist r
  ipersist connc; ipersist stopc; ipersist done
  ihave ⟨msgc, msgc0⟩ := (typedPointsto_halves _ _).1 $$ msgc
  ihave ⟨working, working0⟩ := (typedPointsto_halves _ _).1 $$ working
  ihave ⟨closer, closer0⟩ := (typedPointsto_halves _ _).1 $$ closer
  imod sync.init_Mutex (swLockInv Rh ty lid pid «$r0_ptr») ⊤
    («$r0_ptr».[rafthttp.streamWriter, go!"mu"]) $$ mu [msgc0 working0 closer0] with #Hmu
  · inext
    iunfold swLockInv
    iexists mc, γm, false, GoInterface.nil
    iframe; iframe #
  -- the stop and done channels' receivers' copies
  icases ownBroadcastChan_open _ _ _ _ $$ Hsb with ⟨%γsch, #Hsint, Hsown⟩
  ihave #Hsunk : ownBroadcastChan sc γs iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γsch
    iframe #
  ihave Hsb := ownBroadcastChan_close sc γs iprop(True) .Pending γsch $$ [$Hsint $Hsown]
  icases ownBroadcastChan_open _ _ _ _ $$ Hdb with ⟨%γdch, #Hdint, Hdown⟩
  ihave #Hdunk : ownBroadcastChan dc γdn iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γdch
    iframe #
  ihave Hdb := ownBroadcastChan_close dc γdn iprop(True) .Pending γdch $$ [$Hdint $Hdown]
  ihave #Hfixed : swFixed Rh ty lid pid Rr «$r0_ptr» $$ []
  · iunfold swFixed
    iexists lg, ps, fs, r, γd, cc, sc, dc, γc, γs, γdn
    iframe #
    ipureintro; exact ⟨Hlgnn, Hfsnn⟩
  wp_apply wp_fork $$ [HR msgc working closer Hdb]
  · (try wp_auto)
    wp_apply hRun Rh ty lid pid Rr «$r0_ptr» mc $$ [$HR msgc working closer Hdb]
    · iframe #
      isplitl [msgc working closer]
      · iunfold swRunOwn
        iexists γm
        iframe; iframe #
      · iunfold swDoneRight
        iexists dc, γdn
        iframe; iframe #
    ipureintro; exact isPanic_intoVal _
  (try wp_auto)
  iapply HΦ
  iframe #
  iunfold swStopRight
  iexists sc, γs
  iframe; iframe #

end proof

end EtcdGrove
end Perennial
