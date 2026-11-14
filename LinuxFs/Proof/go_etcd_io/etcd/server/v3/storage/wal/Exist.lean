/-
`wal.Exist` over `fsExt`: the proof (W12 of `notes/wal-fsext-plan.md`; spec
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean`), over the callee hypotheses of
`ExistCallees.lean` and `WithExt.spec` (proved); `os.ErrNotExist`'s value from `os`'s package fact
(`os.errNotExist_of_pkgInit`, 2026-11-14). One core
(`wal.Exist.wp_core`), for any update `A` the start step runs on the invariant's contents (`hA`):
the AU committed unchanged (`wal.Exist.wp_proof`), or nothing (`wal.Exist.wp_specCreate`, what
`Create` uses). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Exist
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ExistCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ExistPin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

/-- **`Exist`'s core** (see the file header): `A` in place of the client's update, `Lin` what the
start step gives of the WAL's state `od`; `false` only when there is no WAL. -/
theorem wal.Exist.wp_core (C : WalCodec) (Mr : WalMarshal)
    (wp_WithExt : go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt.spec (GF := GF) (hG := hG))
    (wp_RDabs : fileutil.ReadDir.specAbsentIs (GF := GF) (hG := hG))
    (wp_RDchild : fileutil.ReadDir.specChildIs (GF := GF) (hG := hG))
    (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (A : IProp GF)
    (Lin : Option WalDur → IProp GF)
    (hA : ∀ s, ⊢ A -∗ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ={⊤ \ ↑walN}=∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗ Lin (s.wal !! dir))
    (hin : InArea r dir nm) (hnmO : NameOk nm) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
        WalFs.walAreaOk C Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
        WalFs.walUnlockedTok ∗ A }}
      (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Exist)) (Val #dir))
    {{ (b : Bool), RET #b; osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
        WalFs.walUnlockedTok ∗ ∃ od, Lin od ∗ ⌜b = false → od = none⌝ }} := by
  wp_start as ⟨#Hok, Hp, Hres, Hperm, Hu, HA⟩
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, -, -, -, -, -, #Hfu, -, -, -, -, #Hos, -, -, #Hfp, #Hzp, -, -, -, -, -, -, -⟩
  try wp_auto
  wp_apply wp_WithExt as %g #Hg
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  try wp_auto
  have hdc := dir_child hin
  subst hdc
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb⟩
  iunfold walAreaRes at Hres
  icases Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %a1, %a2, Hc, %a3, %a4⟩
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_existStart C Mr R jr r (child r nm) nm N h Wn A Lin hA hin (a1 nm hin.1)
    $$ Hinv Hsi Hnc HA HN Hsf Hu with ⟨Hnc, HN, Hsf, %od, HL, Hcase⟩
  iframe Hnc
  imodintro
  icases Hcase with (⟨%hc, Hu⟩ | ⟨%hc, %J, %X, %hj, %q1, %q2, %hn, %hp, Hn1, Hsp, #Hk, Hl, Htf, Ho, HJ⟩)
  · obtain ⟨hod, hNnm, hnone⟩ := hc
    wp_apply wp_RDabs r nm _ [g] [go!".wal"] _ R jr _ 1 N _ h rfl hnmO hNnm hnone
      $$ [Hp Hperm HN Hosl] as %rs %err ⟨Hp, Hperm, HN, Hosl, %herr, %bn, #Herr⟩
    · iframe; iframe #
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      simp only [List.getD_cons_zero]
      iexact Hg
    ihave ⟨%ee, #Hee⟩ := os.errNotExist_of_pkgInit $$ Hos
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    try wp_auto
    wp_bind (App (App _ (Val #(GoInterface.ok ie))) (Val #ee))
    iunfold errIsNotExist at Herr
    iapply Herr $$ Hee
    inext
    wp_auto
    iapply HΦ
    iframe Hp Hperm Hu
    isplitl [HN Hsf Hc]
    · iunfold walAreaRes; iexists N, h, cl, Wn; iframe; ipureintro; exact ⟨a1, a2, a3, a4⟩
    iexists od; iframe HL; ipureintro; intro _; exact hod
  · obtain ⟨hJ, hX, b0, hb0w, hb0s⟩ := hp
    wp_apply wp_RDchild r nm _ [g] [go!".wal"] _ R jr _ (.only [nm]) _ hn J 1 (.except X) _ hj rfl hnmO
      (by simp [NameSet.Mem]) hJ
      $$ [Hsp Hn1 Hperm HJ Hosl] as %rs %err ⟨-, -, Hperm, HJ, Hosl, Hout⟩
    · iframe; iframe #
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      simp only [List.getD_cons_zero]
      iexact Hg
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_existEnd C Mr R jr r (child r nm) J X hj hX
      $$ Hinv Hsi Hnc Hk Hl Htf Ho HJ with ⟨Hnc, Hu⟩
    iframe Hnc
    imodintro
    icases Hout with (⟨%names, %rs', %hout, Hrs⟩ | ⟨%herr, #Herr⟩)
    · obtain ⟨rfl, -, hmem, -, hrd⟩ := hout
      have hb0 : b0 ∈ names := (hmem b0 (except_mem_of_walNameP hX hb0w)).1 hb0s
      have hne := readDirOut_wal_ne hrd hb0 hb0w
      try wp_auto
      ihave %hlen := ownSlice_len _ _ _ $$ Hrs
      have hl0 : rs.len ≠ W64 0 := by
        intro he
        rw [he] at hlen
        obtain ⟨h1, -⟩ := hlen
        have h0 : sint.nat (W64 0) = 0 := by rfl
        rw [h0] at h1
        exact hne (List.length_eq_zero_iff.1 h1)
      rw [decide_eq_false hl0]
      iapply HΦ
      iframe Hp Hperm Hu
      isplitl [HN Hsf Hc]
      · iunfold walAreaRes; iexists N, h, cl, Wn; iframe; ipureintro; exact ⟨a1, a2, a3, a4⟩
      iexists od; iframe HL; ipureintro; intro hc; cases hc
    · ihave ⟨%ee, #Hee⟩ := os.errNotExist_of_pkgInit $$ Hos
      cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      try wp_auto
      wp_bind (App (App _ (Val #(GoInterface.ok ie))) (Val #ee))
      iunfold errIsNotExist at Herr
      iapply Herr $$ Hee
      inext
      wp_auto
      iapply HΦ
      iframe Hp Hperm Hu
      isplitl [HN Hsf Hc]
      · iunfold walAreaRes; iexists N, h, cl, Wn; iframe; ipureintro; exact ⟨a1, a2, a3, a4⟩
      iexists od; iframe HL; ipureintro; intro hc; cases hc

/-- **`wal.Exist.spec`**: the core with the client's update committed unchanged
(`walInvBody_existAU`). -/
theorem wal.Exist.wp_proof (C : WalCodec) (Mr : WalMarshal)
    (wp_WithExt : go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt.spec (GF := GF) (hG := hG))
    (wp_RDabs : fileutil.ReadDir.specAbsentIs (GF := GF) (hG := hG))
    (wp_RDchild : fileutil.ReadDir.specChildIs (GF := GF) (hG := hG)) :
    wal.Exist.spec (GF := GF) C Mr := by
  intro R jr r dir nm qp Q hin hnmO
  iintro %Φ Hpre HΦ
  iapply (wal.Exist.wp_core C Mr wp_WithExt wp_RDabs wp_RDchild R jr r dir nm qp _
    (fun od => iprop(∃ o, Q o ∗ ⌜walOptLe o od⌝))
    (fun s => walInvBody_existAU C Mr R jr r s dir Q) hin hnmO) $$ Hpre
  inext
  iintro %b ⟨Hp, Hres, Hperm, Hu, %od, ⟨%o, HQ, %ho⟩, %hb⟩
  iapply HΦ
  iframe
  ipureintro
  intro hf
  exact existFalseOk_of_le ho (hb hf)

/-- **`wal.Exist.specCreate`** (what `Create` uses): the core with no update. -/
theorem wal.Exist.wp_specCreate (C : WalCodec) (Mr : WalMarshal)
    (wp_WithExt : go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt.spec (GF := GF) (hG := hG))
    (wp_RDabs : fileutil.ReadDir.specAbsentIs (GF := GF) (hG := hG))
    (wp_RDchild : fileutil.ReadDir.specChildIs (GF := GF) (hG := hG)) :
    wal.Exist.specCreate (GF := GF) C Mr := by
  intro R jr r dir nm qp hin hnmO
  iintro %Φ ⟨#Hpkg, #Hok, Hp, Hres, Hperm, Hu⟩ HΦ
  iapply (wal.Exist.wp_core C Mr wp_WithExt wp_RDabs wp_RDchild R jr r dir nm qp
    iprop(emp) (fun _ => iprop(emp))
    (fun s => by iintro - Hb; imodintro; iframe Hb) hin hnmO) $$ [Hp Hres Hperm Hu]
  · iframe; iframe #
  inext
  iintro %b ⟨Hp, Hres, Hperm, Hu, -⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
