/-
`tx.commitFreelist()` (U10c of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 4, run only
when `!NoFreelistSync`): a buffer of `flCount fl` pages allocated (`tx.allocate`, from the
freelist or at the high-water mark, which then grows), the freelist written into it
(`freelist.Write`: the post-allocation freelist's ids), and `tx.meta.freelist` set to its id. On
an allocation error the transaction is rolled back (`tx.rollback()`) and done.

The spec is over the writer's working state (`wtxW`/`wdbW`, as `Tx.allocate`'s). The error path's
rollback needs `wtxEnd`; the caller's frame `F` supplies what the writer state lacks (the full
database, `rwlock`, the closed flag's half, the page tokens, the agreed state, the data's quarter,
the facts), stated as two entailments: for the state allocate leaves unchanged, and for a lost
mapping (`derefRel` and a re-base). On success `F` comes back.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Proof.go_etcd_io.bbolt.Inv.WAccess
public import Proof.go_etcd_io.bbolt.Commit.WriteFL
public import Proof.go_etcd_io.bbolt.Commit.RollbackSpec
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Write
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__EstimatedWritePageSize
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetFreelist
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.commitFreelist()`** (see the file header): `allocate`'s premises (for `flCount w.fl`
pages; the freelist's ids fewer than `2^48`), the caller's frame `F` with the two rollback
entailments (ghost updates: the caller's agreed state follows the re-based records). On success: `allocate`'s result `X1`/`w1` (`allocRes`, the page `id` at `p`, the
high-water mark bumped when taken from it), with the freelist page `flPageBytes w1.fl id` in its
buffer and `tx.meta.freelist = id`; `F` back. On an error: rolled back, done. -/
abbrev Tx.commitFreelist.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb) (F : IProp GF),
  X.t.mv.txid' = w.wtxid → X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms →
  derefPre X → liveFresh X → liveReach X → w.fl.allIds.length < 2 ^ 48 →
  (F ∗ wtxW K tx r false X ∗ wdbW K tx X.v w ⊢ |==> wtxEnd K tx r X (wLive X.v w.C) w) →
  (∀ (X' : WX) (w' : WDb), (∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) → w'.C = w.C →
    w'.fl = w.fl →
    F ∗ wtxLost K tx r false X' ∗ wdbLost K tx X'.v w' ⊢
      |==> wtxEnd K tx r X' (some X'.v, some (w'.C.txid + 1), false, false) w') →
  {{ F ∗ wtxW (GF := GF) K tx r false X ∗ wdbW K tx X.v w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"commitFreelist")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (X1 : WX) (w1 : WDb) (id : w64) (p : Loc),
        F ∗ wtxW K tx r false (X1.setFlPage id (flPageBytes w1.fl id (flCount w.fl))) ∗
        wdbW K tx X1.v w1 ∗
        ⌜allocRes X X1 w.fl w1.fl w.wtxid (flCount w.fl) p id ∧ w1.C = w.C ∧
          X1.t.mv.pgid'.toNat * 4096 ≤ mapLen w1.ms ∧ (w1 = w.withFl w1.fl ∨ wdbRemap w w1)⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ txDoneDef tx) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxHeartbeats 0 in
/-- **`tx.commitFreelist()`** proved: `EstimatedWritePageSize` over the freelist out of `wdbW`
(`wdbW_fl_acc`), `allocate` of `flCount` pages; on an error the frame's entailment gives
`wtxEnd` for `rollback` (`rbOK`: the live writer state, or the lost mapping's); on success the
new buffer and the meta copy out of `wtxW` (`wtxW_flpage_acc`), the freelist written into it,
`SetFreelist(p.Id())`, back as `setFlPage`. -/
theorem Tx.commitFreelist.wp_proof (hAlloc : Tx.allocate.spec (GF := GF) (hG := hG))
    (hRb : Tx.rollback.spec (GF := GF) (hG := hG))
    (hEst : internal.freelist.Interface.EstimatedWritePageSize.spec (GF := GF) (hG := hG))
    (hWrite : internal.freelist.Interface.Write.spec (GF := GF) (hG := hG))
    (hSet : internal.common.Meta.SetFreelist.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG)) :
    Tx.commitFreelist.spec (GF := GF) (hG := hG) := by
  intro K tx r X w F htx hhwm hdp hlf hlr hlen hrb1 hrb2
  wp_start as ⟨HF, Hw, Hd⟩
  icases wtxW_db_acc K tx r false X $$ Hw with ⟨⟨#Hpkg, #Hcore, %Hrdb⟩, Hdb, Hwb⟩
  icases wdbW_fl_acc K tx X.v w $$ Hd with ⟨%dqf, Hfl, Hflo, Hdb2⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨-, -, -, -, -, #Hfix, -⟩
  iunfold dbFixed at Hfix
  icases Hfix with ⟨#Hps, -⟩
  ihave #Hpkf : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply hEst w.fli w.fl $$ [$Hpkf $Hflo] as Hflo
  try wp_auto
  have hcnt : BitVec.sdiv (W64 ((16 + 8 * (w.fl.allIds.length +
      (if 65535 ≤ w.fl.allIds.length then 1 else 0)) : Nat) : Int)) (W64 4096) + W64 1 =
      W64 ((flCount w.fl : Nat) : Int) := by
    unfold flCount
    have : 16 + 8 * (w.fl.allIds.length + (if 65535 ≤ w.fl.allIds.length then 1 else 0)) < 2 ^ 52 := by
      split <;> omega
    have hm1 : (W64 ((16 + 8 * (w.fl.allIds.length +
        (if 65535 ≤ w.fl.allIds.length then 1 else 0)) : Nat) : Int)).msb = false := by
      rw [BitVec.msb_eq_decide]; simp; omega
    have hm2 : (W64 4096).msb = false := by decide
    rw [BitVec.sdiv_eq, hm1, hm2]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_udiv, BitVec.toNat_add]
    omega
  rw [hcnt]
  ihave Hd := Hdb2 $$ Hfl Hflo
  ihave Hw := Hwb $$ Hdb
  have hc1 : 1 ≤ flCount w.fl := by unfold flCount; omega
  have hc2 : flCount w.fl * 4096 < 2 ^ 62 := by unfold flCount; split <;> omega
  have hsc : sint.Z (W64 ((flCount w.fl : Nat) : Int)) = flCount w.fl := by word
  have hsn : sint.nat (W64 ((flCount w.fl : Nat) : Int)) = flCount w.fl := by word
  icases persistent_entails_left (show wdbW (GF := GF) K tx X.v w ⊢
      ⌜wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C⌝ by
        unfold wdbW; iintro ⟨-, %h⟩; ipureintro; exact h) $$ Hd with ⟨Hd, %Hwd⟩
  wp_apply hAlloc K tx r false X w (W64 ((flCount w.fl : Nat) : Int)) (by rw [hsc]; omega)
    (by rw [hsn]; omega) htx hhwm hdp hlf hlr $$ [Hw Hd]
    as %p %err Hres
  · iframe
  icases Hres with (⟨%He, %X1, %w1, %id, Hw, Hd, %Hal⟩ | ⟨%He, #Herr, Hfail⟩)
  · subst He
    try wp_auto
    simp only [hsn] at Hal
    obtain ⟨-, hpn, Xr, -, hcase⟩ := Hal.1
    obtain ⟨hh, hX1⟩ : ∃ h, X1 = Xr.addPage id p (flCount w.fl) h := by
      rcases hcase with ⟨-, -, e⟩ | ⟨-, -, -, e⟩
      · exact ⟨_, e⟩
      · exact ⟨_, e⟩
    have hfl1 : w1.fl.allIds.length ≤ w.fl.allIds.length := by
      rcases hcase with ⟨-, e, -⟩ | ⟨-, e, -, -⟩
      · rw [e]; exact alloc_allIds_le _ _ _ _
      · simp [e]
    have hroom : 8 * (w1.fl.allIds.length + 1) ≤ flCount w.fl * 4096 - 16 := by
      unfold flCount; exact flCount_room _ _ hfl1
    obtain ⟨hpm, hbf⟩ := addPage_lookups Xr id p (flCount w.fl) hh
    rw [← hX1] at hpm hbf
    icases wtxW_flpage_acc K tx r false X1 id p _ hpm hbf $$ Hw
      with ⟨%mp, %dqm, Hdb, Hme, Hmv, Hp, Hwb⟩
    icases wdbW_fl_acc K tx X1.v w1 $$ Hd with ⟨%dqf1, Hfl, Hflo, Hdb2⟩
    have hpl : (encode (⟨id, W16 0, W16 0, W32 ((flCount w.fl - 1 : Nat) : Int)⟩ : Page) ++
        List.replicate (flCount w.fl * 4096 - 16) (W8 0)).length = flCount w.fl * 4096 := by
      simp only [List.length_append, ByteEncoding.encode_length, List.length_replicate]; omega
    have hpne : (encode (⟨id, W16 0, W16 0, W32 ((flCount w.fl - 1 : Nat) : Int)⟩ : Page) ++
        List.replicate (flCount w.fl * 4096 - 16) (W8 0)) ≠ [] :=
      List.ne_nil_of_length_pos (by rw [hpl]; omega)
    icases Read.bytesPointsto_bounds _ _ _ hpne $$ Hp with ⟨Hp, %Hpb⟩
    rw [hpl] at Hpb
    icases (Spill.pageBuf_split p (DFrac.own 1) _ _ Hpb.1).1 $$ Hp with ⟨Hh, Hr⟩
    try wp_auto
    wp_apply hWrite w1.fli w1.fl p _ (flCount w.fl * 4096 - 16) hroom Hpb.1 (by omega)
      $$ [$Hpkf $Hflo $Hh $Hr] as ⟨Hflo, Hh, Hr⟩
    try wp_auto
    wp_apply hId p _ (DFrac.own 1) $$ [$Hpkc $Hh] as Hh
    try wp_auto
    wp_apply hSet mp X1.t.mv _ $$ [$Hpkc $Hmv] as Hmv
    try wp_auto
    ihave Hp := (Spill.pageBuf_split p (DFrac.own 1) _ _ Hpb.1).2 $$ [Hh Hr]
    · iframe
    ihave Hw := Hwb $$ %(flPageBytes w1.fl id (flCount w.fl)) [] Hdb Hme Hmv [Hp]
    · ipureintro; rw [flPageBytes_length _ _ _ hroom, hpl]
    · rw [← flPage_eq]; iexact Hp
    ihave Hd := Hdb2 $$ Hfl Hflo
    try wp_auto
    try iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists X1, w1, id, p
    iframe
    ipureintro; exact Hal
  · cases err with
    | nil => exact absurd rfl He
    | ok ei =>
    try wp_auto
    icases Hfail with (⟨Hw, Hd⟩ | ⟨%X', %w', Hw, Hd, %Hrel⟩)
    · ihave Hend : |==> wtxEnd K tx r X (wLive X.v w.C) w $$ [HF Hw Hd]
      · iapply hrb1; iframe
      imod Hend
      have hrbok : rbOK X (wLive X.v w.C) w := by
        refine ⟨X.v, w.C.txid + 1, false, true, rfl, ?_,
          ⟨fun _ => by rw [Hwd.2.1]; simp, fun _ => rfl⟩, fun _ => rfl, fun h => absurd h (by simp)⟩
        rw [htx]; rfl
      wp_apply hRb K tx r X (wLive X.v w.C) w hrbok $$ [Hend] as #Hdone
      · iexact Hend
      try wp_auto
      try iapply HΦ
      iright
      isplitr
      · ipureintro; exact fun h => nomatch h
      isplitr
      · iexact Herr
      iexact Hdone
    · icases persistent_entails_left (show wdbLost (GF := GF) K tx X'.v w' ⊢
          ⌜wdbOK w' ∧ w'.ms = none⌝ by
            unfold wdbLost; iintro ⟨-, %h⟩; ipureintro; exact h) $$ Hd with ⟨Hd, %Hwl⟩
      obtain ⟨⟨Xd, b0, hder, hX'⟩, hC, hfl⟩ := Hrel
      ihave Hend : |==> wtxEnd K tx r X' (some X'.v, some (w'.C.txid + 1), false, false) w'
        $$ [HF Hw Hd]
      · iapply hrb2 X' w' ⟨Xd, b0, hder, hX'⟩ hC hfl; iframe
      imod Hend
      have hrbok : rbOK X' (some X'.v, some (w'.C.txid + 1), false, false) w' := by
        refine ⟨X'.v, w'.C.txid + 1, false, false, rfl, ?_, ?_, ?_, ?_⟩
        rotate_left
        · simp [Hwl.2]
        · intro h; cases h
        · intro h; cases h
        rw [hX']
        show Xd.t.mv.txid' = _
        rw [hder.2.2.2.2.2.2.1, htx, hC]; rfl
      wp_apply hRb K tx r X' _ w' hrbok $$ [Hend] as #Hdone
      · iexact Hend
      try wp_auto
      try iapply HΦ
      iright
      isplitr
      · ipureintro; exact fun h => nomatch h
      isplitr
      · iexact Herr
      iexact Hdone

end proof

end bbolt
end EtcdGrove
end Perennial
