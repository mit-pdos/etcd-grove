/-
Proof of `Spec/.../dist/client/writerOp.lean` (#50 N10a). Lean-first (no Rocq counterpart).

`ps := in.([]etcdstart.KV)`; the log `w := &etcdstart.Writes{}` under its mutex, at `wsInvT` with the
log's facts `okFactKM γ` and a fresh token (`token_alloc`), which `Writer` holds while it runs;
`etcdstart.Writer` across machines (`Writer_dist`, a hypothesis) with each Put's update the adapter's
write update after the start's changes (`km_put_au0`) and its logged fact `okFactKM_of_write`; the log
read under the lock, the lock left with the token in its place (the call keeps the slice it returns);
a `nil` log replaced by an empty one; the log's facts `okFactK` (`okFactK_of_KM`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerOp
public import Perennial.Proof.sync.Link
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
theorem writerOp.wp_proof (wp_Writer : Writer_dist.spec (GF := GF) (hG := hG)) :
    writerOp.spec (GF := GF) (hG := hG) := by
  intro π cl api eps V Γ γ P sl ps hauth hAs hγk hW hps
  wp_start as ⟨Hlt, #Hkc, #Hps, #Hkm, #Hl0⟩
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Hpl := ownSlice_len $$ Hps
  imod token_alloc (GF := GF) with ⟨%γt, Htk⟩
  (try wp_auto)
  -- `w := &etcdstart.Writes{}`: the log under its mutex
  icases typedPointsto_split _ _ _ $$ «$r0» with Hr0
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hr0 with ⟨mu, ok, -⟩
  imod sync.init_Mutex (wsInvT «$r0_ptr» (okFactKM γ) γt) ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" «$r0_ptr»)
    $$ mu [ok] with #Hmu
  · inext
    iunfold wsInvT
    ileft
    iunfold wsInvF
    iexists slice.nil, []
    iframe ok
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  (try wp_auto)
  -- `etcdstart.Writer(sys.(*clientv3.Client), w, ps, 0, len(ps))`
  have hlen : sint.Z sl.len ≤ ps.length := by have := Hpl.1; word
  wp_apply (wp_Writer cl api eps V Γ
      (fun k v => kmWriteQ γ [[]] (.put (putKeyOp k v))) (okFactKM γ) «$r0_ptr» γt sl ps (W64 0)
      sl.len hauth (fun _ => inferInstance) hAs (by decide) (by have := Hpl.2; word) hlen
      (fun x hx => (hps x hx).2)) $$ [$Hlt $Htk] as ⟨Hlt, Htk⟩
  · iframe #
    isplitr
    · iintro !> %k' %v' %hkv
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hkv
      have hkvP : (k', v') ∈ P := by rw [← hpe]; exact (hps p hp).1
      ihave Hw := km_put_au0 γ P hW k' v' hkvP $$ [$Hkm $Hl0]
      iunfold kvOpAu1 at Hw
      iunfold kvAu1 at Hw
      rw [show putWireOf (opPutModel k' v' []) = putKeyOp k' v' from rfl, ← hγk]
      iexact Hw
    iintro !> %k' %v' %σ HQ %Hb
    iapply (okFactKM_of_write γ k' v' σ) $$ HQ
    ipureintro; exact Hb
  (try wp_auto)
  -- the log, read under the lock; the lock left with the token
  wp_apply (sync.Mutex.wp_Lock (structFieldRef
      github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" «$r0_ptr»)
      (wsInvT «$r0_ptr» (okFactKM γ) γt)) $$ [] as ⟨Hown, Hinv⟩
  · iframe #
  iunfold wsInvT at Hinv
  icases Hinv with (Hinv | ⟨%sl0, -, Htk'⟩)
  rotate_left
  · iexfalso; iapply (token_exclusive γt) $$ Htk Htk'
  iunfold wsInvF at Hinv
  icases Hinv with ⟨%osl, %oks, Hok, Hos, Hocap, #Hoks⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef
      github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" «$r0_ptr»)
      (wsInvT «$r0_ptr» (okFactKM γ) γt)) $$ [Hown Hok Htk]
  · iframe #
    iframe Hown
    inext
    iunfold wsInvT
    iright
    iexists osl
    iframe Hok Htk
  ihave #Hoks' : □ [∗list] p ∈ oks, etcd_partition.okFactK (GF := GF) γ p $$ []
  · iintro !>
    iapply (BigSepL.bigSepL_mono (Φ := fun _ p => okFactKM (GF := GF) γ p)
      (fun _ => okFactK_of_KM γ _)) $$ Hoks
  (try wp_auto)
  -- `if oks == nil { oks = []etcdstart.PutRec{} }`
  wp_if_destruct
  · ihave %Hol := ownSlice_len $$ Hos
    wp_apply wp_slice_literal (l := ([] : List wrec))
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, _⟩
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iexists _, []
    iframe Hl1
    isplitr
    · ipureintro; rfl
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  · (try wp_auto)
    iapply HΦ
    iframe Hlt
    iexists osl, oks
    iframe Hos
    isplitr
    · ipureintro; rfl
    iexact Hoks'

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
