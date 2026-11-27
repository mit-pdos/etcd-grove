/-
The proof of `KvRaft/Spec/.../kvraft/nextBoot.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.nextBoot
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.BootFileOf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putUint64
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

theorem nextBoot.wp_proof
    (wp_BootFileOf : BootFileOf.spec (GF := GF) (hG := hG))
    (wp_Read : github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec (GF := GF) (hG := hG))
    (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG)) :
    nextBoot.spec (GF := GF) (hG := hG) := by
  intro γu id dir bn qc
  wp_start as ⟨#Hmi, Hbs⟩
  iunfold udpBootStart at Hbs
  icases Hbs with ⟨%cur, #Hos, #Hsh, #Hdi, Hdh, Hcp, #Hbi, Hwr, %hdf⟩
  ihave #Hdur : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable
    $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_BootFileOf dir id $$ [$Hpkg]
  try wp_auto
  -- the file's number, before the read: the generation has not crashed, so the invariant holds the
  -- bound over the state, which the writer's half pins
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  ihave #Hbi' := Hbi
  iunfold udpBootInv at Hbi'
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hbi' with ⟨Hb, Hclose⟩
  iunfold udpBootBody at Hb
  imod later_exists_except0 $$ Hb with ⟨%s0, Hb⟩
  icases Hb with ⟨>Hds, >Hwv, Hb⟩
  ihave %Hag := ghostVar_agree bn.wr _ _ _ _ $$ Hwr Hwv
  subst Hag
  imod notCrashed_or_crashed $$ [$Hnc $Hb] with ⟨Hnc, Hb⟩
  iunfold udpHi at Hb
  imod later_exists_except0 $$ Hb with ⟨%hi, >Hhi, >%hok⟩
  obtain ⟨n, hn, -⟩ := hok.1
  imod Hclose $$ [Hds Hwv Hhi] with -
  · inext
    iunfold udpBootBody
    iexists _
    iframe Hds Hwv
    ileft
    iexists hi
    unfold udpHi
    iframe Hhi
    ipureintro
    exact hok
  imodintro
  iframe Hnc
  -- the read, inside the invariant: the state, which the writer's half pins
  rw [← hdf.2]
  wp_bind (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Read)) _)
  iapply (wp_Read bn.γd bn.df bn.fR qc hdf.1) $$ Hdur Hos Hsh Hdi Hdh Hcp
  iauintro
  unfold atomic_acc
  ihave #Hbi' := Hbi
  iunfold udpBootInv at Hbi'
  imod inv_acc (E := DurFs.durAuMask) (udpBootN_sub_durAu _) $$ Hbi' with ⟨Hb, Hclose⟩
  iunfold udpBootBody at Hb
  imod later_exists_except0 $$ Hb with ⟨%s1, Hb⟩
  icases Hb with ⟨>Hds, >Hwv, Hb⟩
  ihave %Hag := ghostVar_agree bn.wr _ _ _ _ $$ Hwr Hwv
  subst Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑(udpBootN .@ uint.nat id) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ⟨cur, none⟩
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hwv Hb] with -
    · inext
      iunfold udpBootBody
      iexists _
      iframe Hds Hwv Hb
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod Hclose $$ [Hds Hwv Hb] with -
  · inext
    iunfold udpBootBody
    iexists _
    iframe Hds Hwv Hb
  imodintro
  iintro Hdh Hcp
  simp only [DurFs.readRes]
  try wp_auto
  -- the file's number: none (no file), or `n`'s 8 bytes (this package's: no panic)
  wp_bind (If _ _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ boot_ptr ↦ n)))
  isplitl [boot data]
  · rcases hn with ⟨rfl, rfl⟩ | rfl
    · simp only [Option.isSome_none]
      try wp_auto
      iframe boot
      ipureintro; rfl
    · simp only [Option.isSome_some, Option.getD_some]
      try wp_auto
      wp_apply wp_string_to_bytes (u64Le n) as %sl ⟨Hsl, -⟩
      rw [show u64Le n = u64Le n ++ [] from (List.append_nil _).symm]
      wp_apply wp_getUint64 sl (DFrac.own 1) n [] $$ [$Hpkg $Hsl] as %rest ⟨-, -⟩
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
      simp only [List.append_nil, u64Le_length]
      try wp_auto
      iframe boot
      ipureintro; rfl
  iintro %v ⟨%hv, boot⟩
  subst hv
  try wp_auto
  wp_for
  try wp_auto
  by_cases hmax : n = W64 18446744073709551615
  · -- at the largest number, it never returns
    simp only [hmax, decide_true, ↓reduceIte]
    try wp_auto
    wp_apply time.wp_Sleep
    try wp_auto
    wp_for_post
    iframe
  simp only [hmax, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hlt : uint.nat n < uint.nat (n + W64 1) := by word
  try wp_auto
  ihave Hn := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hnc := ownSliceCap_nil (V := w8) (GF := GF)
  wp_apply wp_putUint64 slice.nil [] (n + W64 1) $$ [$Hpkg $Hn $Hnc] as %s1 ⟨Hs1, -⟩
  wp_apply wp_bytes_to_string s1 _ (DFrac.own 1) $$ [$Hs1] as -
  try wp_auto
  simp only [List.nil_append]
  have e1 : (n + 1 : w64) = n + W64 1 := rfl
  -- the write: the rename keeps the bound; the directory's sync raises it to `n + 1` and allocates
  -- the process's counter
  wp_bind (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Write)) _) _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #()⌝ ∗ DurFs.durHandle bn.γd bn.df bn.fR ∗
      Fs.osCallPerm (Fs.callKey bn.fR bn.df.d) qc ∗
      ghostVar bn.wr (1 : Qp).half (⟨some (u64Le (n + W64 1)), none⟩ : DurFs.DurSt) ∗
      udpCtr γu id (n + W64 1) (W64 0))))
  isplitl [Hdh Hcp Hwr]
  · iapply (wp_Write bn.γd bn.df bn.fR qc (u64Le (n + W64 1)) hdf.1
      (by rw [u64Le_length]; decide)) $$ Hdur Hos Hsh Hdi Hdh Hcp
    -- the rename
    iauintro
    unfold atomic_acc
    imod inv_acc (E := DurFs.durAuMask) (udpBootN_sub_durAu _) $$ Hbi' with ⟨Hb, Hclose⟩
    iunfold udpBootBody at Hb
    imod later_exists_except0 $$ Hb with ⟨%s2, Hb⟩
    icases Hb with ⟨>Hds, >Hwv, Hb⟩
    ihave %Hag := ghostVar_agree bn.wr _ _ _ _ $$ Hwr Hwv
    subst Hag
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑(udpBootN .@ uint.nat id) from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists ⟨cur, none⟩
    iframe Hds
    isplit
    · iintro Hds
      imod Hclose2 with -
      imod Hclose $$ [Hds Hwv Hb] with -
      · inext
        iunfold udpBootBody
        iexists _
        iframe Hds Hwv Hb
      imodintro
      iframe
    iintro Hds
    imod Hclose2 with -
    imod ghostVar_update_halves (⟨some (u64Le (n + W64 1)), some cur⟩ : DurFs.DurSt) bn.wr _ _
      $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    ihave Hb' : iprop(▷ ((∃ hi, udpHi γu id hi ∗
        ⌜BootOk hi ⟨some (u64Le (n + W64 1)), some cur⟩⌝) ∨ crashed ∗ token bn.tk)) $$ [Hb]
    · icases later_or.1 $$ Hb with (Hb | Hb)
      · inext
        ileft
        icases Hb with ⟨%hi', Hhi, %hok'⟩
        iexists hi'
        iframe Hhi
        ipureintro
        exact bootOk_rename hok' hn hlt
      · inext
        iright
        iexact Hb
    imod Hclose $$ [Hds Hwv Hb'] with -
    · inext
      iunfold udpBootBody
      iexists _
      iframe Hds Hwv Hb'
    imodintro
    -- the directory's sync: not crashed, so the bound is the invariant's
    iintro Hnc
    iauintro
    unfold atomic_acc
    imod inv_acc (E := DurFs.durAuMask) (udpBootN_sub_durAu _) $$ Hbi' with ⟨Hb, Hclose⟩
    iunfold udpBootBody at Hb
    imod later_exists_except0 $$ Hb with ⟨%s3, Hb⟩
    icases Hb with ⟨>Hds, >Hwv, Hb⟩
    ihave %Hag := ghostVar_agree bn.wr _ _ _ _ $$ Hwr Hwv
    subst Hag
    imod notCrashed_or_crashed $$ [$Hnc $Hb] with ⟨Hnc, Hb⟩
    iunfold udpHi at Hb
    imod later_exists_except0 $$ Hb with ⟨%hi', >Hhi, >%hok'⟩
    have hle : uint.nat hi' ≤ uint.nat n := by
      obtain ⟨m, hm, hle⟩ := hok'.2 cur rfl
      rw [bootVal_inj hn hm]
      exact hle
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑(udpBootN .@ uint.nat id) from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists ⟨some (u64Le (n + W64 1)), some cur⟩
    iframe Hds
    isplit
    · iintro Hds
      imod Hclose2 with -
      imod Hclose $$ [Hds Hwv Hhi] with -
      · inext
        iunfold udpBootBody
        iexists _
        iframe Hds Hwv
        ileft
        iexists hi'
        unfold udpHi
        iframe Hhi
        ipureintro
        exact hok'
      imodintro
      iframe
    iintro Hds
    imod Hclose2 with -
    imod ghostVar_update_halves (⟨some (u64Le (n + W64 1)), none⟩ : DurFs.DurSt) bn.wr _ _
      $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    imod udp_boot_bump γu id hi' n hle hlt _ (udpMsgN_sub_boot _) $$ Hmi [Hhi] with ⟨Hhi, Hctr⟩
    · unfold udpHi
      iexact Hhi
    rw [e1]
    imod Hclose $$ [Hds Hwv Hhi] with -
    · inext
      iunfold udpBootBody
      iexists _
      iframe Hds Hwv
      ileft
      iexists (n + W64 1)
      iframe Hhi
      ipureintro
      exact ⟨⟨n + W64 1, Or.inr rfl, Nat.le_refl _⟩, fun _ h => by cases h⟩
    imodintro
    iframe Hnc
    iintro Hdh Hcp
    iframe Hdh Hcp Hwr Hctr
  iintro %v ⟨%hv, Hdh, Hcp, Hwr, Hctr⟩
  subst hv
  try wp_auto
  iapply HΦ
  iframe Hctr
  iunfold udpBootStart
  iexists _
  iframe Hos Hsh Hdi Hdh Hcp Hbi Hwr
  ipureintro
  exact hdf

end proof

end kvraft
end EtcdGrove
end Perennial
