/-
Proof of `Spec/.../dist/client/writerOp.lean` (#50 N10a). Lean-first (no Rocq counterpart).

`ps := in.([]etcdstart.KV)`; the log `w := &etcdstart.Writes{}` under its mutex, at `wsInvT` with the
log's facts `okFactKM γ` and a fresh token (`token_alloc`), which `Writer` holds while it runs;
`etcdstart.Writer` across machines (`Writer_dist`, a hypothesis) with each Put's update the adapter's
write update after the start's changes (`km_put_au0`) and its logged fact `okFactKM_of_write`; the log
read under the lock, the lock left with the token in its place (the call keeps the slice it returns);
a `nil` log replaced by an empty one; the log's facts `okFactK` (`okFactK_of_KM`). Its records are
small (each a Put's, `wrecSmall`) and at most as many as the Puts (the log's length at the ghost variable
`γn`, `Writer_dist`'s post), so the log encodes in a message (`recsBytes_length_le`).
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

set_option maxHeartbeats 1600000 in
theorem writerOp.wp_proof (wp_Writer : Writer_dist.spec (GF := GF) (hG := hG)) :
    writerOp.spec (GF := GF) (hG := hG) := by
  intro π Γ eps V hauth hAs sys x i
  simp only [writerWire_ivAt, writerWire_ovAt, wP, wQ, writerTok, ← kmInv_eq_G, ← okFactK_eq_G]
  wp_start as ⟨⟨%cl, %api, %Hsys, Hlt, #Hkc⟩, ⟨%sl, ⟨%Hx, %Hb⟩, #Hps⟩, #Hkm, #Hl0, %Hpre⟩
  obtain ⟨hps, hlen56⟩ := Hpre
  subst Hsys Hx
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Hpl := ownSlice_len $$ Hps
  ihave #Hl0' : monoListLbOwn (kmOf Γ i.1).ch ([[]] : List (List mvcc.Change)) $$ []
  · iexact Hl0
  imod token_alloc (GF := GF) with ⟨%γt, Htk⟩
  imod (ghostVar_alloc (GF := GF) (0 : Nat)) with ⟨%γn, Hgn⟩
  icases (ghostVar_split_half γn 1 (0 : Nat)).1 $$ Hgn with ⟨Hgi, Hgn⟩
  (try wp_auto)
  -- `w := &etcdstart.Writes{}`: the log under its mutex
  icases typedPointsto_split _ _ _ $$ «$r0» with Hr0
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hr0 with ⟨mu, ok, -⟩
  imod sync.init_Mutex (wsInvT «$r0_ptr» (fun p => iprop(okFactKM (kmOf Γ i.1) p ∗ ⌜wrecSmall p⌝)) γt γn) ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" «$r0_ptr»)
    $$ mu [ok Hgi] with #Hmu
  · inext
    iunfold wsInvT
    ileft
    iexists slice.nil, []
    iframe ok Hgi
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  (try wp_auto)
  -- `etcdstart.Writer(sys.(*clientv3.Client), w, ps, 0, len(ps))`
  have hlen : sint.Z sl.len ≤ i.2.length := by have := Hpl.1; word
  wp_apply (wp_Writer cl api eps V Γ
      (fun k v => kmWriteQ (kmOf Γ i.1) [[]] (.put (putKeyOp k v)))
      (fun p => iprop(okFactKM (kmOf Γ i.1) p ∗ ⌜wrecSmall p⌝)) «$r0_ptr» γt γn 0 sl i.2 (W64 0)
      sl.len hauth (fun _ => inferInstance) hAs (by decide) (by have := Hpl.2; word) hlen
      (fun x hx => (hps x hx).2.sizeOk)) $$ [$Hlt $Htk $Hgn] as ⟨Hlt, Htk, %c, Hgn, %Hc⟩
  · iframe #
    isplitr
    · iintro !> %k' %v' %hkv
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hkv
      have hkvP : (k', v') ∈ i.1.2.2 := by rw [← hpe]; exact (hps p hp).1
      ihave Hw := km_put_au0 (kmOf Γ i.1) i.1.2.2 rfl k' v' hkvP $$ [$Hkm $Hl0']
      iunfold kvOpAu1 at Hw
      iunfold kvAu1 at Hw
      rw [show putWireOf (opPutModel k' v' []) = putKeyOp k' v' from rfl]
      iexact Hw
    iintro !> %k' %v' %σ %hkv HQ %Hb
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hkv
    have hsm := (hps p hp).2
    simp only [pairOf, Prod.mk.injEq] at hpe
    obtain ⟨rfl, rfl⟩ := hpe
    isplitl
    · iapply (okFactKM_of_write (kmOf Γ i.1) p.Key' p.Val' σ) $$ HQ
      obtain ⟨h1, h2⟩ := Hb
      ipureintro; exact ⟨by unfold kvRevFits at h1; omega, h2⟩
    · ipureintro; exact hsm
  (try wp_auto)
  -- the log, read under the lock; the lock left with the token
  wp_apply (sync.Mutex.wp_Lock (structFieldRef
      github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" «$r0_ptr»)
      (wsInvT «$r0_ptr» (fun p => iprop(okFactKM (kmOf Γ i.1) p ∗ ⌜wrecSmall p⌝)) γt γn)) $$ []
      as ⟨Hown, Hinv⟩
  · iframe #
  iunfold wsInvT at Hinv
  icases Hinv with (Hinv | ⟨%sl0, -, Htk'⟩)
  rotate_left
  · iexfalso; iapply (token_exclusive γt) $$ Htk Htk'
  icases Hinv with ⟨%osl, %oks, Hok, Hos, Hocap, #Hoks, Hgi⟩
  ihave %Heq := ghostVar_agree γn _ _ _ _ $$ Hgi Hgn
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (structFieldRef
      github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" «$r0_ptr»)
      (wsInvT «$r0_ptr» (fun p => iprop(okFactKM (kmOf Γ i.1) p ∗ ⌜wrecSmall p⌝)) γt γn))
      $$ [Hown Hok Htk]
  · iframe #
    iframe Hown
    inext
    iunfold wsInvT
    iright
    iexists osl
    iframe Hok Htk
  ihave ⟨#Hoks', %Hsm⟩ := okFacts_small (kmOf Γ i.1) oks $$ Hoks
  have hol : oks.length ≤ i.2.length := by have := Hpl.1; rw [Heq]; word
  have hbytes : (recsBytes oks).length < 2 ^ 63 := by
    have := recsBytes_length_le oks Hsm; omega
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  -- `if oks == nil { oks = []etcdstart.PutRec{} }`
  wp_if_destruct
  · wp_apply wp_slice_literal (l := ([] : List wrec))
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, _⟩
    imod ownSlice_persist _ _ _ $$ Hl1 with #Hl1
    (try wp_auto)
    iapply HΦ
    isplitl [Hlt]
    · iexists cl, api
      iframe Hlt Hkc
      ipureintro; rfl
    iexists []
    isplitr
    · iexists _
      iframe Hl1
      ipureintro; exact ⟨rfl, by simp [recsBytes, github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.encU64_length]⟩
    iintro !>
    iapply BigSepL.bigSepL_nil.2; itrivial
  · (try wp_auto)
    iapply HΦ
    isplitl [Hlt]
    · iexists cl, api
      iframe Hlt Hkc
      ipureintro; rfl
    iexists oks
    isplitr
    · iexists osl
      iframe Hos
      ipureintro; exact ⟨rfl, hbytes⟩
    iexact Hoks'

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
