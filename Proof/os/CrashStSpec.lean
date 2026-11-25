/-
The proofs of `Spec/os/CrashSt.lean`: the models' loops as in `Proof/os/OpenFileS.lean`,
`Proof/os/File__WriteAt.lean`, `Proof/os/File__Truncate.lean`, `Proof/os/File__Sync.lean` and
`Proof/golang_org/x/sys/unix/*.lean`, over the steps of `Proof/os/CrashStOps.lean`. The open's loop
keeps what its attempts may have made of the state (`CsOpenInv`); a write's loop keeps a state it
reached (`WReach`), with the bytes written so far (`fin_vals`); a truncate's a state not yet grown
(its `OsMeta` as given or as an attempt announced it) or grown. Lean-first (no Rocq counterpart).

But for the open, each loop is proved once (`<F>.wp_crashG`, of `<F>.tripleCrashG`) over any crash
invariant `I` with an accessor (`CsAcc`, the caller's part `csOwnG Tok`), on the steps' generic forms
(`wp_..._g`); `<F>.wp_proof_crashS` (`csInv`, `cs_acc`) and `<F>.wp_proof_crashI` (`csInvI`,
`csI_acc`; `Spec/os/CrashStI.lean`) are its instances.
-/
module

public import Spec.os.CrashSt
public import Spec.os.CrashStI
public import Proof.os.CrashStIOps
public import Proof.golang_org.x.sys.unix.Munmap
public import Perennial.Golang.Theory.Plain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [syscall.Assumptions] in
/-- `syscall.Fdatasync.specCrashS` over any crash invariant with an accessor (`CsAcc`). -/
abbrev syscall.Fdatasync.tripleCrashG : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (_hacc : CsAcc (GF := GF) N I Tok Ok d.ino) (m : OsMeta) (H F T : List ByteG)
    (fa fb : Nat),
  H.length = fa → fa + F.length = fb → (∀ y ∈ F, y = durB y.1) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok (csSynced m H F T fa fb) →
  {{ osInv (GF := GF) ∗ I ∗ osFd (GF := GF) fd dq d ∗
      csOwnG (GF := GF) Tok d.ino ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ csOwnG (GF := GF) Tok d.ino (csSynced m H F T fa fb)) ∨
       (⌜e ≠ 0⌝ ∗
         csOwnG (GF := GF) Tok d.ino ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)) }}

theorem syscall.Fdatasync.wp_crashG [syscall.Assumptions] :
    syscall.Fdatasync.tripleCrashG (GF := GF) (hG := hG) := by
  intro fd dq d N I _ Tok Ok hacc m H F T fa fb hH hF hFd hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  wp_apply wp_osFsync_g fd dq d N I Tok Ok hacc m H F T fa fb hH hF hFd hN hok
    $$ Hos Hinv Hfd Hown
    as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

theorem syscall.Fdatasync.wp_proof_crashS [syscall.Assumptions] :
    syscall.Fdatasync.specCrashS (GF := GF) (hG := hG) := by
  intro fd dq d N P R γ Good Ok m H F T fa fb hH hF hFd hN hok
  exact syscall.Fdatasync.wp_crashG fd dq d N (csInv (GF := GF) N P R γ Good Ok)
    (fun s => ghostVar γ (1 : Qp).half (some (d.ino, s) : CState))
    (fun s => Ok (some (d.ino, s))) (cs_acc N P R γ Good Ok d.ino) m H F T fa fb hH hF hFd hN hok

theorem syscall.Fdatasync.wp_proof_crashI [syscall.Assumptions] :
    syscall.Fdatasync.specCrashI (GF := GF) (hG := hG) := by
  intro A _ fd dq d N i γ γa γc Ok a m H F T fa fb hi hH hF hFd hN hok
  subst hi
  exact syscall.Fdatasync.wp_crashG fd dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N d.ino γ γa γc Ok a) m H F T fa fb hH hF hFd hN hok

variable [golang_org.x.sys.unix.Assumptions] in
/-- `golang_org.x.sys.unix.Mmap.specCrashS` over any crash invariant with an accessor (`CsAcc`). -/
abbrev golang_org.x.sys.unix.Mmap.tripleCrashG : Prop :=
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (_hacc : CsAcc (GF := GF) N I Tok Ok d.ino) (m : OsMeta)
    (bs : List ByteG) (fa fb : Nat),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ base : Loc,
    Ok ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩) →
  {{ osInv (GF := GF) ∗ I ∗ osFd (GF := GF) fd dq d ∗
      csOwnG (GF := GF) Tok d.ino ⟨m, bs, fa, fb, .idle⟩ }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          csOwnG (GF := GF) Tok d.ino ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ ∗
          ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil⌝ ∗ csOwnG (GF := GF) Tok d.ino ⟨m, bs, fa, fb, .idle⟩)) }}

theorem golang_org.x.sys.unix.Mmap.wp_crashG [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Mmap.tripleCrashG (GF := GF) (hG := hG) := by
  intro fd off len prot fl dq d N I _ Tok Ok hacc m bs fa fb hrd hoff hlen hprot hfl hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmap_g fd off len prot fl dq d N I Tok Ok hacc m bs fa fb hN hrd hoff hlen hprot
    hfl hok
    $$ Hos Hinv Hfd Hown as %base %e Hr Hfd
  icases Hr with (⟨%he, Hown, Hc⟩ | ⟨%he, Hown⟩)
  · obtain ⟨rfl, hpos, hmax⟩ := he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    wp_func_call
    wp_call
    have hnn : base ≠ null := by intro h; subst h; simp [null] at hpos
    have hlz : sint.Z len = (len.toNat : Int) := by
      simp only [sint.Z]; have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    rw [ite_eq_right (by omega), ite_eq_right hnn,
      ite_eq_right (by simp only [maxAddr] at hmax; push_cast; omega)]
    wp_auto
    rw [← show errnoErr 0 = interface.nil by unfold errnoErr; rfl]
    iapply HΦ
    iframe
    ileft
    iexists base
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨he, rfl⟩ := he
    have he' : ¬ e = W64 0 := he
    simp only [decide_eq_false he', Bool.not_false]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe
    iright
    iframe
    ipureintro; exact ⟨he, rfl⟩

theorem golang_org.x.sys.unix.Mmap.wp_proof_crashS [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Mmap.specCrashS (GF := GF) (hG := hG) := by
  intro fd off len prot fl dq d N P R γ Good Ok m bs fa fb hrd hoff hlen hprot hfl hN hok
  exact golang_org.x.sys.unix.Mmap.wp_crashG fd off len prot fl dq d N (csInv (GF := GF) N P R γ Good Ok)
    (fun s => ghostVar γ (1 : Qp).half (some (d.ino, s) : CState))
    (fun s => Ok (some (d.ino, s))) (cs_acc N P R γ Good Ok d.ino) m bs fa fb hrd hoff hlen hprot hfl hN hok

theorem golang_org.x.sys.unix.Mmap.wp_proof_crashI [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Mmap.specCrashI (GF := GF) (hG := hG) := by
  intro A _ fd off len prot fl dq d N i γ γa γc Ok a m bs fa fb hi hrd hoff hlen hprot hfl hN hok
  subst hi
  exact golang_org.x.sys.unix.Mmap.wp_crashG fd off len prot fl dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N d.ino γ γa γc Ok a) m bs fa fb hrd hoff hlen hprot hfl hN hok

variable [golang_org.x.sys.unix.Assumptions] in
/-- `golang_org.x.sys.unix.Munmap.specCrashS` over any crash invariant with an accessor (`CsAcc`). -/
abbrev golang_org.x.sys.unix.Munmap.tripleCrashG : Prop :=
  ∀ (base : Loc) (len : w64) (i : Ino) (N : Namespace) (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (_hacc : CsAcc (GF := GF) N I Tok Ok i) (m : OsMeta) (bs : List ByteG)
    (fa fb : Nat) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  Ok ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ →
  {{ osInv (GF := GF) ∗ I ∗
      csOwnG (GF := GF) Tok i ⟨m, bs, fa, fb, .idle⟩ ∗ cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ (e : w64), RET #(errnoErr e);
      (⌜e = 0⌝ ∗ csOwnG (GF := GF) Tok i ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩) ∨
      (⌜e ≠ 0⌝ ∗
        (csOwnG (GF := GF) Tok i ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ ∨
         (csOwnG (GF := GF) Tok i ⟨m, bs, fa, fb, .idle⟩ ∗ cellsR base 0 len.toNat vf))) }}

theorem golang_org.x.sys.unix.Munmap.wp_crashG [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Munmap.tripleCrashG (GF := GF) (hG := hG) := by
  intro base len p N I _ Tok Ok hacc m bs fa fb vf hpos hb hN hok
  wp_start as ⟨#Hos, #Hinv, Hown, Hc⟩
  by_cases hl0 : len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    iapply wp_errno
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iright; iframe
  · rw [decide_eq_false hl0]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z len := by
      simp only [sint.Z]; exact ⟨by decide, hpos⟩
    rw [if_pos h0]
    have hn : 0 < len.toNat := by
      have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    icases cellsR_pos base _ vf hn $$ Hc with ⟨Hc, %hbase⟩
    rw [show sint.Z (W64 0) = 0 from rfl, sliceIndexRef_byte ⟨base, len, len⟩ 0 hbase (Int.le_refl _)]
    have hb0 : (base +ₗ (0 : Int)) = base := by simp
    rw [hb0]
    wp_auto
    wp_apply wp_osMunmap_g base len len p N I Tok Ok hacc m bs fa fb len.toNat vf hN hb rfl rfl hok
      $$ Hos Hinv Hown Hc as %e Hr
    iapply wp_errno
    iapply HΦ
    iexact Hr

theorem golang_org.x.sys.unix.Munmap.wp_proof_crashS [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Munmap.specCrashS (GF := GF) (hG := hG) := by
  intro base len p N P R γ Good Ok m bs fa fb vf hpos hb hN hok
  exact golang_org.x.sys.unix.Munmap.wp_crashG base len p N (csInv (GF := GF) N P R γ Good Ok)
    (fun s => ghostVar γ (1 : Qp).half (some (p, s) : CState))
    (fun s => Ok (some (p, s))) (cs_acc N P R γ Good Ok p) m bs fa fb vf hpos hb hN hok

theorem golang_org.x.sys.unix.Munmap.wp_proof_crashI [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Munmap.specCrashI (GF := GF) (hG := hG) := by
  intro A _ base len p N γ γa γc Ok a m bs fa fb vf hpos hb hN hok
  exact golang_org.x.sys.unix.Munmap.wp_crashG base len p N (csInvI (GF := GF) N p γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N p γ γa γc Ok a) m bs fa fb vf hpos hb hN hok

variable [os.Assumptions]

/-- `os.File.Sync.specCrashS` over any crash invariant with an accessor (`CsAcc`). -/
abbrev os.File.Sync.tripleCrashG : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (N : Namespace)
    (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (_hacc : CsAcc (GF := GF) N I Tok Ok d.ino)
    (m : OsMeta) (H F T : List ByteG) (fa fb : Nat),
  H.length = fa → fa + F.length = fb → (∀ y ∈ F, y = durB y.1) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok (csSynced m H F T fa fb) →
  {{ osInv (GF := GF) ∗ I ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗
      csOwnG (GF := GF) Tok d.ino ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ csOwnG (GF := GF) Tok d.ino (csSynced m H F T fa fb)) ∨
       (⌜err ≠ interface.nil⌝ ∗
         csOwnG (GF := GF) Tok d.ino ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)) }}

theorem os.File.Sync.wp_crashG : os.File.Sync.tripleCrashG (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d N I _ Tok Ok hacc m H F T fa fb hH hF hFd hN hok
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hsys⟩, Hosfd, Hown⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hos Hosfd as Hosfd
  wp_apply wp_osFsync_g fd dq d N I Tok Ok hacc m H F T fa fb hH hF hFd hN hok
    $$ Hos Hinv Hosfd Hown as %e Hr Hosfd
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -⟩ | ⟨%he, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
  wp_auto
  icases Hr with (⟨%he, Hown⟩ | ⟨%he, Hown⟩)
  · subst he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    ileft
    isplitr; · ipureintro; rfl
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    iright
    iframe
    ipureintro; intro h; cases h

theorem os.File.Sync.wp_proof_crashS : os.File.Sync.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d N P R γ Good Ok m H F T fa fb hH hF hFd hN hok
  exact os.File.Sync.wp_crashG f fd name dqf dq d N (csInv (GF := GF) N P R γ Good Ok)
    (fun s => ghostVar γ (1 : Qp).half (some (d.ino, s) : CState))
    (fun s => Ok (some (d.ino, s))) (cs_acc N P R γ Good Ok d.ino) m H F T fa fb hH hF hFd hN hok

theorem os.File.Sync.wp_proof_crashI : os.File.Sync.specCrashI (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf dq d N i γ γa γc Ok a m H F T fa fb hi hH hF hFd hN hok
  subst hi
  exact os.File.Sync.wp_crashG f fd name dqf dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N d.ino γ γa γc Ok a) m H F T fa fb hH hF hFd hN hok

theorem os.OpenFile.wp_proof_crashS [os.file.FieldAssumptions] :
    os.OpenFile.specCrashS (GF := GF) (hG := hG) := by
  intro d b perm N R q γ Good Ok s hb hs hN hN' hok
  wp_start as ⟨#Hos, #Hsi, Hperm, #Hinv, Hown⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  obtain ⟨s', hs'⟩ : ∃ s', s' = s := ⟨_, rfl⟩
  ihave Hown := (show csOwn (GF := GF) (child d b) R γ s ⊢ csOwn (child d b) R γ s' by
    rw [hs']) $$ Hown
  have hm : CsOpenInv s s' := .inl hs'
  clear hs'
  iloeb as IH generalizing %s' %hm Hperm Hown HΦ
  rcases s' with _ | ⟨i, y⟩
  · -- nothing at the path: an attempt to create it
    obtain rfl : s = none := by
      rcases hm with h1 | ⟨i, h⟩
      · exact h1.symm
      · cases s <;> simp [csOpenSt, csNew] at h
    icases csOwn_none _ _ _ $$ Hown with ⟨Hv, %j, %b', %h, Ht, %hn⟩
    obtain ⟨hn, hfa⟩ := hn
    obtain ⟨hdj, hbb⟩ := fileAt_root hfa hb
    subst b'
    imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Ht with ⟨Ht, #Hlb⟩
    imod osPathS_root R d j (DFrac.own 1) hdj CoPset.subseteq_top $$ Hsi with Hp
    icases osCallPerm_child R d b _ j q $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_apply wp_osCallBeginS R (child d b) q h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs0 Hk -
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = flCreat from by decide]
    (try wp_auto)
    wp_apply wp_osOpenCreate_cs d b N R γ Good Ok j (DFrac.own 1) h t s0 q hN hN' hb hfa hn hs0
      (hok rfl) $$ Hos Hsi Hinv Hp Hv Ht Hk as %fd %e Hperm - Hres
    icases Hres with (⟨%i, %he, Hown, Hfd⟩ | ⟨%he, Hst⟩)
    · obtain ⟨rfl, hfd0⟩ := he
      rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)]
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      iapply HΦ
      iframe Hperm
      ileft
      iexists fd, i
      simp only [csOpenSt]
      iframe
      isplitr
      · ipureintro; exact ⟨trivial, hfd0, .inl trivial⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      (repeat' isplitl []) <;> iassumption
    · obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        icases Hst with (Hown | ⟨%i, Hown⟩)
        · iapply IH $$ %none %(.inl rfl) Hperm Hown HΦ
        · iapply IH $$ %(csNew i) %(.inr ⟨i, rfl⟩) Hperm Hown HΦ
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iframe Hperm
        iright
        simp only [csOpenSt]
        iframe Hst
        ipureintro; exact ⟨(fun h => by cases h), trivial⟩
  · -- the file `i` at the path: an attempt to open it
    obtain ⟨hsi, heq, -⟩ := csOpenInv_some hs hm
    icases csOwn_tree _ _ _ _ _ $$ Hown with ⟨%j, %b', %h, Ht, %hl, Hback⟩
    obtain ⟨hl, hfa⟩ := hl
    obtain ⟨hdj, hbb⟩ := fileAt_root hfa hb
    subst b'
    imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Ht with ⟨Ht, #Hlb⟩
    imod osPathS_root R d j (DFrac.own 1) hdj CoPset.subseteq_top $$ Hsi with Hp
    icases osCallPerm_child R d b _ j q $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_apply wp_osCallBeginS R (child d b) q h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs0 Hk -
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
    (try wp_auto)
    wp_apply wp_osOpenFileS R d b j i (.only [b]) (DFrac.own 1) _ h t s0 q (W64 0x80042)
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hb
      (by simp [NameSet.Mem]) hl CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hp Ht Hk as %fd %e %hres Hperm - Ht Hfd
    ihave Hown := Hback $$ Ht
    by_cases he0 : e = W64 0
    · subst he0
      rw [decide_eq_true rfl]
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i (W64 0x80042)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨i, true, true, none, none⟩
        by rw [openFd_rw]; split
           · iintro H; iexact H
           · exact absurd rfl ‹_›) $$ Hfd
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
      iapply HΦ
      iframe Hperm
      ileft
      iexists fd, i
      simp only [← heq]
      iframe
      isplitr
      · ipureintro; exact ⟨by simp, hfd0, hsi⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      (repeat' isplitl []) <;> iassumption
    · rw [decide_eq_false he0]
      iclear Hfd
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %_ %hm Hperm Hown HΦ
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iframe Hperm
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iright
        iexists i
        simp only [← heq]
        iexact Hown

/-- `os.File.WriteAt.specCrashS` over any crash invariant with an accessor (`CsAcc`). -/
abbrev os.File.WriteAt.tripleCrashG : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (_hacc : CsAcc (GF := GF) N I Tok Ok d.ino) (m : OsMeta)
    (bs : List ByteG) (fa fb : Nat),
  d.writable = true → 0 ≤ off.toInt → off.toNat ≤ m.size → off.toNat + data.length < 2 ^ 63 →
  0 < data.length → data.length ≤ 0x40000000 →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → (off.toNat + data.length ≤ fa ∨ fb ≤ off.toNat) →
  (∀ nn m' bs', WReach m bs off.toNat data nn m' bs' →
    Ok ⟨m', bs', fa, fb, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off.toNat + nn) (data.drop nn) n →
      Ok ⟨m', bs', fa, fb, .write t (off.toNat + nn) (data.drop nn) n⟩)) →
  {{ osInv (GF := GF) ∗ I ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      csOwnG (GF := GF) Tok d.ino ⟨m, bs, fa, fb, .idle⟩ ∗
      mcellsAny (GF := GF) m.maps off.toNat (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      mcellsAny m.maps off.toNat (off.toNat + data.length) ∗
      ∃ (nn : Nat) (m' : OsMeta) (bs' : List ByteG),
        ⌜WReach m bs off.toNat data nn m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ nn = data.length ∧
              off.toNat + data.length ≤ m'.size ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        csOwnG (GF := GF) Tok d.ino ⟨m', bs', fa, fb, .idle⟩ }}

theorem os.File.WriteAt.wp_crashG : os.File.WriteAt.tripleCrashG (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d N I _ Tok Ok hacc m bs fa fb hwr hoff hgap hbig hn hn2 hN hfz hW
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hsys⟩, Hsl, Hosfd, Hown, Hc⟩
  icases csOwnG_wf _ _ _ $$ Hown with %Hwf
  have hlen : bs.length = m.size := Hwf.1
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwfs
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  wp_pure
  wp_pure
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  -- the invariant: a state the loop reached, `nn` of the bytes written
  obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
  conv in (occs := 4) (#(W64 0) : val) => rw [← hnnv]
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  obtain ⟨bs', hbs'⟩ : ∃ bs', bs' = bs := ⟨_, rfl⟩
  have hR : WReach m bs off.toNat data nnv.toNat m' bs' := by
    subst hm' hbs' hnnv; exact .refl
  have hnn : nnv.toNat < data.length := by subst hnnv; exact hn
  have hS : off.toNat + nnv.toNat ≤ m'.size := by subst hnnv hm'; exact hgap
  have hpre : ∀ i < nnv.toNat, (bs'[off.toNat + i]?).map Prod.fst = data[i]? := by
    subst hnnv; intro i hi; exact absurd hi (Nat.not_lt_zero _)
  ihave Hown := (show csOwnG (GF := GF) Tok d.ino ⟨m, bs, fa, fb, .idle⟩ ⊢
    csOwnG (GF := GF) Tok d.ino ⟨m', bs', fa, fb, .idle⟩ by rw [hm', hbs']) $$ Hown
  clear hm' hbs' hnnv
  iloeb as IH generalizing %m' %bs' %nnv %hR %hnn %hS %hpre Hown Hosfd Hsl Hfd Hc HΦ
  have hNar := (hR.wIn hlen hgap).1
  -- one attempt, from `nn`
  have hnnz : sint.Z nnv = nnv.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nnv = nnv.toNat := by simp [sint.nat, hnnz]
  wp_auto
  have hmax : ¬ (sint.Z (W64 1073741824) < sint.Z (sl.len - nnv)) := by
    have hsub : sint.Z (sl.len - nnv) = sint.Z sl.len - sint.Z nnv := by
      have : sint.Z nnv ≤ sint.Z sl.len := by rw [hnnz, hslz]; omega
      have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
      word
    rw [hsub, hslz, hnnz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmax]
  wp_auto
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [hnnz, hslz]; omega
  rw [if_pos hsb]
  ihave ⟨Hsl1, Hsl2⟩ := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).1 $$ Hsl
  rw [hnnn]
  wp_apply wp_bytes_to_string _ (data.drop nnv.toNat) dqs $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).2 $$ [Hsl1 Hsl2]
  · rw [hnnn]; iframe
  have hoffv : (off + nnv).toNat = off.toNat + nnv.toNat := by
    rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
  have hoffv' : 0 ≤ (off + nnv).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hoffv]; omega)]; omega
  have hdl : (data.drop nnv.toNat).length = data.length - nnv.toNat := List.length_drop
  have hgap' : (off + nnv).toNat ≤ m'.size := by rw [hoffv]; exact hS
  have hfz' : (off + nnv).toNat + (data.drop nnv.toNat).length ≤ fa ∨ fb ≤ (off + nnv).toNat := by
    rw [hoffv, hdl]; omega
  have hcl : cfLo m' (off + nnv).toNat = off.toNat + nnv.toNat := by
    rw [hoffv]; unfold cfLo; omega
  have hend : (off + nnv).toNat + (data.drop nnv.toNat).length = off.toNat + data.length := by
    rw [hoffv, hdl]; omega
  -- the cells this attempt takes
  ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps off.toNat (off.toNat + nnv.toNat)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc
  ihave Hc2 := (show mcellsAny (GF := GF) m.maps (off.toNat + nnv.toNat) (off.toNat + data.length) ⊢
    mcellsAny m'.maps (cfLo m' (off + nnv).toNat) ((off + nnv).toNat + (data.drop nnv.toNat).length)
      by rw [hcl, hend, hNar.maps]) $$ Hc2
  have hdne : data.drop nnv.toNat ≠ [] := by
    intro h; have := congrArg List.length h; rw [hdl] at this; simp at this; omega
  have hW1 : ∀ t n, PwFresh m' bs' (off + nnv).toNat (data.drop nnv.toNat) n →
      Ok ⟨m', bs', fa, fb, .write t (off + nnv).toNat (data.drop nnv.toNat) n⟩ := by
    intro t n hfr; rw [hoffv] at hfr ⊢; exact (hW _ _ _ hR).2 hnn t n hfr
  wp_apply wp_osPWriteStart_g fd (off + nnv) (data.drop nnv.toNat) dq d N I Tok Ok hacc m' bs' fa fb
    hN hwr hoffv' hgap' hdne hfz' hW1 $$ Hos Hinv Hosfd Hown Hc2 as %t %nst %hfr Hosfd Hown
  have hW2 : ∀ k (zs : List Cands), k ≤ (data.drop nnv.toNat).length → (off + nnv).toNat ≤ m'.size →
      zs.length = pwSize m'.size (off + nnv).toNat k - m'.size → ZsOk m' zs →
      Ok ⟨pwPostK true m' (off + nnv).toNat (data.drop nnv.toNat) k nst,
        finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k nst zs, fa, fb, .idle⟩ := by
    intro k zs hk _ hzl hz; rw [hoffv] at hzl ⊢
    exact (hW _ _ _ (hR.step k _ nst zs hnn (by rw [hdl] at hk; exact hk) (.inl rfl) hzl hz (by rw [hoffv] at hfr; exact hfr))).1
  wp_apply wp_osPWriteFinish_g t d.ino (off + nnv).toNat (data.drop nnv.toNat) nst N I Tok Ok hacc m'
    bs' fa fb hN hW2 $$ Hos Hinv Hown as %k %e %zs %hke Hown Hc2
  obtain ⟨hk, hke, -, hzl, hzt⟩ := hke
  rw [hdl] at hk
  have hv := fin_vals (n := nst) (zs := zs) hNar.len hS (Nat.le_refl _) (by omega) hk hpre
  rw [← hoffv, Nat.max_eq_right (Nat.le_add_right _ _)] at hv
  obtain ⟨hS', hpre'⟩ := hv
  have hRs : ∀ nn', (nn' = nnv.toNat + k ∨ nn' = nnv.toNat) →
      WReach m bs off.toNat data nn' (pwPostK true m' (off + nnv).toNat (data.drop nnv.toNat) k nst)
        (finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k nst zs) := by
    intro nn' h; rw [hoffv] at hzl hfr ⊢; exact hR.step k nn' nst zs hnn hk h hzl hzt hfr
  -- the cells back
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc2 := (show mcellsAny (GF := GF) m'.maps (cfLo m' (off + nnv).toNat)
      ((off + nnv).toNat + (data.drop nnv.toNat).length) ⊢
    mcellsAny m.maps (off.toNat + nnv.toNat) (off.toNat + data.length)
      by rw [hcl, hend, hNar.maps]) $$ Hc2
  ihave Hc := mcellsAny_merge m.maps off.toNat (off.toNat + nnv.toNat) (off.toNat + data.length)
    (by omega) (by omega) $$ [Hc1 Hc2]
  · iframe
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %_ %_ %nnv %(hRs _ (.inr rfl))
      %hnn %(by show _ ≤ pwSize _ _ _; have := pwSize_ge3 m'.size (off + nnv).toNat k; omega)
      %(fun i hi => hpre' i (by omega)) Hown Hosfd Hsl Hfd Hc HΦ
  · rw [decide_eq_false he4]
    wp_auto
    have hWk : (W64 k).toNat = k := by
      simp only [W64]; rw [BitVec.toNat_ofInt]; omega
    have hnk : (nnv + W64 k).toNat = nnv.toNat + k := by
      rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
    by_cases hfull : nnv + W64 k = sl.len
    · rw [decide_eq_true hfull]
      wp_auto
      have hfk : nnv.toNat + k = data.length := by
        have := congrArg BitVec.toNat hfull; rw [hnk, hsln] at this
        simp only [W64] at this; rw [BitVec.toNat_ofInt] at this; omega
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨_, hRs _ (.inl rfl), .inl ⟨hsln, rfl, hfk, by show _ ≤ pwSize _ _ _; omega,
            fun i hi => hpre' i (by omega)⟩⟩
      · rw [decide_eq_false he0]
        wp_auto
        simp only [decide_eq_false he0, Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨_, hRs _ (.inl rfl), .inr ⟨rfl, by intro h; cases h⟩⟩
    · rw [decide_eq_false hfull]
      wp_auto
      by_cases he0 : e = W64 0
      · -- a short write: the next attempt from `nn + k`
        rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_pure
        have hne : nnv.toNat + k ≠ data.length := by
          intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
          rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
        iapply IH $$ %_ %_ %(nnv + W64 k) %(by rw [hnk]; exact hRs _ (.inl rfl))
          %(by rw [hnk]; omega) %(by rw [hnk]; show _ ≤ pwSize _ _ _; omega)
          %(fun i hi => hpre' i (by rw [hnk] at hi; omega)) Hown Hosfd Hsl Hfd Hc HΦ
      · rw [decide_eq_false he0]
        simp only [Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨_, hRs _ (.inl rfl), .inr ⟨rfl, by intro h; cases h⟩⟩

theorem os.File.WriteAt.wp_proof_crashS : os.File.WriteAt.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d N P R γ Good Ok m bs fa fb hwr hoff hgap hbig hn hn2 hN hfz hW
  exact os.File.WriteAt.wp_crashG f fd name dqf sl data dqs off dq d N (csInv (GF := GF) N P R γ Good Ok)
    (fun s => ghostVar γ (1 : Qp).half (some (d.ino, s) : CState))
    (fun s => Ok (some (d.ino, s))) (cs_acc N P R γ Good Ok d.ino) m bs fa fb hwr hoff hgap hbig hn hn2 hN hfz hW

theorem os.File.WriteAt.wp_proof_crashI : os.File.WriteAt.specCrashI (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sl data dqs off dq d N i γ γa γc Ok a m bs fa fb hi hwr hoff hgap hbig hn hn2 hN hfz hW
  subst hi
  exact os.File.WriteAt.wp_crashG f fd name dqf sl data dqs off dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N d.ino γ γa γc Ok a) m bs fa fb hwr hoff hgap hbig hn hn2 hN hfz hW

/-- `os.File.Truncate.specCrashS` over any crash invariant with an accessor (`CsAcc`). -/
abbrev os.File.Truncate.tripleCrashG : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (N : Namespace) (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (_hacc : CsAcc (GF := GF) N I Tok Ok d.ino) (m : OsMeta) (bs : List ByteG) (fa fb : Nat),
  0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ m' bs', TReach m bs sz.toNat m' bs' →
    Ok ⟨m', bs', fa, fb, .idle⟩ ∧
      ∀ t n, Ok ⟨m', bs', fa, fb, .trunc t sz.toNat n⟩) →
  {{ osInv (GF := GF) ∗ I ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnG (GF := GF) Tok d.ino ⟨m, bs, fa, fb, .idle⟩ ∗
      mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ ∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
          csGrownOwnG (GF := GF) Tok d.ino m0 bs fa fb sz.toNat n) ∨
       (⌜err ≠ interface.nil⌝ ∗
         ((∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
          csGrownOwnG (GF := GF) Tok d.ino m0 bs fa fb sz.toNat n) ∨
          (csOwnG (GF := GF) Tok d.ino ⟨m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat,
              bs, fa, fb, .idle⟩ ∗
            mcellsAny m.maps m.size (rsHi true m.size sz.toNat))))) }}

theorem os.File.Truncate.wp_crashG : os.File.Truncate.tripleCrashG (GF := GF) (hG := hG) := by
  intro f fd name dqf sz dq d N I _ Tok Ok hacc m bs fa fb hfd0 hwr hsz hgrow hN hT
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hsys⟩, Hosfd, Hown, Hc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  have h1 : ¬ (sint.Z fd < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd0
  rw [decide_eq_false h1]
  wp_auto
  have h2 : ¬ (sint.Z sz < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hsz
  rw [decide_eq_false h2]
  wp_auto
  have hmin : min m.size sz.toNat = m.size := Nat.min_eq_left hgrow
  -- the loop's states: not grown yet (`m`, or as an attempt announced it), or grown
  ihave HS : (∃ m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
      csOwnG (GF := GF) Tok d.ino ⟨m0, bs, fa, fb, .idle⟩ ∗ mcellsAny m.maps m.size (rsHi true m.size sz.toNat)) ∨
      (∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
        csGrownOwnG (GF := GF) Tok d.ino m0 bs fa fb sz.toNat n) $$ [Hown Hc]
  · ileft; iexists m; iframe; ipureintro; exact .inl rfl
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  icases HS with (⟨%m0, %hm0, Hown, Hc⟩ | ⟨%n0, %m0, %hm0, Hg⟩)
  · -- not grown yet
    have hsz0 : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
    have hmp0 : m0.maps = m.maps := by rcases hm0 with rfl | rfl <;> simp
    have hR0 : TReach m bs sz.toNat m0 bs := by rcases hm0 with rfl | rfl; exact .refl; exact .ann
    ihave Hc := (show mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) ⊢
      mcellsAny m0.maps m0.size (rsHi true m0.size sz.toNat) by rw [hsz0, hmp0]) $$ Hc
    wp_apply wp_osFtruncateStart_g fd sz dq d N I Tok Ok hacc m0 bs fa fb hN hwr hsz
      (by rw [hsz0]; exact hgrow) (hT _ _ hR0).2 $$ Hos Hinv Hosfd Hown Hc as %t %n Hosfd Hown
    have hpost : rsPost true m0 sz.toNat sz.toNat = rsPost true m sz.toNat sz.toNat := by
      rcases hm0 with rfl | rfl
      · rfl
      · exact os.rsPost_announce _ _ _ _
    have hann : m0.announce (min m0.size sz.toNat) (rsHi true m0.size sz.toNat) sz.toNat =
        m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat := by
      rw [hsz0]; rcases hm0 with rfl | rfl
      · rfl
      · exact os.announce_idem _ _ _ _
    have hokG : ∀ zs : List Cands, zs.length = sz.toNat - m0.size →
        Ok ⟨rsPost true m0 sz.toNat sz.toNat,
          bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])), fa, fb, .idle⟩ := by
      intro zs hz; rw [hpost]; rw [hsz0] at hz; exact (hT _ _ (.grown n zs hz)).1
    have hokF : Ok ⟨m0.announce (min m0.size sz.toNat) (rsHi true m0.size sz.toNat) sz.toNat,
        bs, fa, fb, .idle⟩ := by rw [hann]; exact (hT _ _ .ann).1
    wp_apply wp_osFtruncateFinish_g t d.ino sz.toNat n N I Tok Ok hacc m0 bs fa fb hN hokG hokF
      $$ Hos Hinv Hown as %e Hr
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ [Hr] Hosfd Hfd HΦ
      icases Hr with (⟨%he, Hg⟩ | ⟨-, (Hg | ⟨Hown, Hc⟩)⟩)
      · iright; iexists n, m0; iframe; ipureintro; exact hm0
      · iright; iexists n, m0; iframe; ipureintro; exact hm0
      · ileft; iexists _; rw [hann]; iframe Hown
        isplitr
        · ipureintro; exact .inr rfl
        ihave Hc := mcells_any (GF := GF) _ _ _ _ $$ Hc
        iapply (show mcellsAny (GF := GF) m0.maps m0.size (rsHi true m0.size sz.toNat) ⊢
          mcellsAny m.maps m.size (rsHi true m.size sz.toNat) by rw [hsz0, hmp0]); iexact Hc
    · rw [decide_eq_false he4]
      wp_auto
      icases Hr with (⟨%he, Hg⟩ | ⟨%he, HS⟩)
      · subst he
        rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
        simp only [Bool.not_true]
        wp_auto
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        ileft
        isplitr; · ipureintro; rfl
        iexists n, m0; iframe; ipureintro; exact hm0
      · have he0' : ¬ e = W64 0 := he
        rw [decide_eq_false he0']
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        iright
        isplitr; · ipureintro; intro h; cases h
        icases HS with (Hg | ⟨Hown, Hc⟩)
        · ileft; iexists n, m0; iframe; ipureintro; exact hm0
        · iright; rw [hann]; iframe Hown
          ihave Hc := mcells_any (GF := GF) _ _ _ _ $$ Hc
          iapply (show mcellsAny (GF := GF) m0.maps m0.size (rsHi true m0.size sz.toNat) ⊢
            mcellsAny m.maps m.size (rsHi true m.size sz.toNat) by rw [hsz0, hmp0]); iexact Hc
  · -- grown: a further attempt is a resize to the size the file has
    have hsz0 : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
    have hmp0 : m0.maps = m.maps := by rcases hm0 with rfl | rfl <;> simp
    have hpost : rsPost true m0 sz.toNat sz.toNat = rsPost true m sz.toNat sz.toNat := by
      rcases hm0 with rfl | rfl
      · rfl
      · exact os.rsPost_announce _ _ _ _
    iunfold csGrownOwnG at Hg
    icases Hg with ⟨%zs, %hzs, Hown, Hcs⟩
    have hR0 : TReach m bs sz.toNat (rsPost true m0 sz.toNat sz.toNat)
        (bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n0)]))) := by
      rw [hpost]; exact .grown n0 zs (by rw [hzs.1, hsz0])
    have hgsz : (rsPost true m0 sz.toNat sz.toNat).size = sz.toNat := rfl
    have hgmaps : (rsPost true m0 sz.toNat sz.toNat).maps = m0.maps := by simp [rsPost]
    have hRR : rsHi true sz.toNat sz.toNat = rsHi true m0.size sz.toNat := by
      simp only [rsHi, if_true, Nat.max_self, Nat.max_eq_right (show m0.size ≤ sz.toNat by omega)]
    have hR1 := le_rsHi true m0.size sz.toNat
    icases (mcells_split (GF := GF) m0.maps m0.size sz.toNat (rsHi true m0.size sz.toNat) _
      (by omega) (by omega)).1 $$ Hcs with ⟨Hc1, Hc2⟩
    ihave Hc0 := mcells_any (GF := GF) _ _ _ _ $$ Hc2
    ihave Hc0 := (show mcellsAny (GF := GF) m0.maps sz.toNat (rsHi true m0.size sz.toNat) ⊢
      mcellsAny (rsPost true m0 sz.toNat sz.toNat).maps (rsPost true m0 sz.toNat sz.toNat).size
        (rsHi true (rsPost true m0 sz.toNat sz.toNat).size sz.toNat) by rw [hgsz, hgmaps, hRR]) $$ Hc0
    wp_apply wp_osFtruncateStart_g fd sz dq d N I Tok Ok hacc _ _ fa fb hN hwr hsz
      (by rw [hgsz]; exact Nat.le_refl _) (hT _ _ hR0).2 $$ Hos Hinv Hosfd Hown Hc0 as %t %n Hosfd Hown
    have hokG : ∀ zs' : List Cands, zs'.length = sz.toNat - (rsPost true m0 sz.toNat sz.toNat).size →
        Ok ⟨rsPost true (rsPost true m0 sz.toNat sz.toNat) sz.toNat sz.toNat,
          (bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n0)]))) ++
            zs'.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])), fa, fb, .idle⟩ := by
      intro zs' hz
      rw [hgsz, Nat.sub_self] at hz
      rw [List.eq_nil_of_length_eq_zero hz, List.map_nil, List.append_nil, os.rsPost_rsPost]
      exact (hT _ _ hR0).1
    have hokF : Ok ⟨(rsPost true m0 sz.toNat sz.toNat).announce
        (min (rsPost true m0 sz.toNat sz.toNat).size sz.toNat)
        (rsHi true (rsPost true m0 sz.toNat sz.toNat).size sz.toNat)
        sz.toNat, bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n0)])), fa, fb, .idle⟩ := by
      rw [os.announce_rsPost]; exact (hT _ _ hR0).1
    wp_apply wp_osFtruncateFinish_g t d.ino sz.toNat n N I Tok Ok hacc _ _ fa fb hN hokG hokF
      $$ Hos Hinv Hown as %e Hr
    -- the state is the grown one again
    ihave Hown : csOwnG (GF := GF) Tok d.ino ⟨rsPost true m0 sz.toNat sz.toNat,
        bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n0)])), fa, fb, .idle⟩ ∗
        mcells m0.maps sz.toNat (rsHi true m0.size sz.toNat) (rsCell sz.toNat) $$ [Hr]
    · unfold csGrownOwnG
      icases Hr with (⟨-, ⟨%zs', %hzs', Hown, Hc⟩⟩ | ⟨-, (⟨%zs', %hzs', Hown, Hc⟩ | ⟨Hown, Hc⟩)⟩)
      · rw [hgsz, Nat.sub_self] at hzs'
        rw [List.eq_nil_of_length_eq_zero hzs'.1, List.map_nil, List.append_nil, os.rsPost_rsPost] at *
        rw [hgsz, hgmaps, hRR]
        iframe
      · rw [hgsz, Nat.sub_self] at hzs'
        rw [List.eq_nil_of_length_eq_zero hzs'.1, List.map_nil, List.append_nil, os.rsPost_rsPost] at *
        rw [hgsz, hgmaps, hRR]
        iframe
      · have hA : (rsPost true m0 sz.toNat sz.toNat).announce (min sz.toNat sz.toNat)
            (rsHi true sz.toNat sz.toNat) sz.toNat = rsPost true m0 sz.toNat sz.toNat :=
          os.announce_rsPost true m0 sz.toNat
        isplitl [Hown]
        · iapply (show csOwnG (GF := GF) Tok d.ino ⟨(rsPost true m0 sz.toNat sz.toNat).announce
              (min sz.toNat sz.toNat) (rsHi true sz.toNat sz.toNat) sz.toNat,
              bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n0)])), fa, fb, .idle⟩ ⊢
            csOwnG (GF := GF) Tok d.ino ⟨rsPost true m0 sz.toNat sz.toNat,
              bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n0)])), fa, fb, .idle⟩ by rw [hA])
          iexact Hown
        · rw [← hRR, touch_maps]
          iapply (mcells_congr_iff (GF := GF) _ _ _ _ _ (fun i h1 _ => by
            simp only [rsOld, rsCell]; rw [if_neg (by omega), if_neg (by omega)])).1 $$ Hc
    icases Hown with ⟨Hown, Hc2⟩
    ihave Hcs := (mcells_split (GF := GF) m0.maps m0.size sz.toNat (rsHi true m0.size sz.toNat) _
      (by omega) (by omega)).2 $$ [Hc1 Hc2]
    · iframe
    ihave Hg : csGrownOwnG (GF := GF) Tok d.ino m0 bs fa fb sz.toNat n0 $$ [Hown Hcs]
    · unfold csGrownOwnG; iexists zs; iframe; ipureintro; exact hzs
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ [Hg] Hosfd Hfd HΦ
      iright; iexists n0, m0; iframe; ipureintro; exact hm0
    · rw [decide_eq_false he4]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_auto
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        ileft
        isplitr; · ipureintro; rfl
        iexists n0, m0; iframe; ipureintro; exact hm0
      · rw [decide_eq_false he0]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        iright
        isplitr; · ipureintro; intro h; cases h
        ileft; iexists n0, m0; iframe; ipureintro; exact hm0

theorem os.File.Truncate.wp_proof_crashS : os.File.Truncate.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf sz dq d N P R γ Good Ok m bs fa fb hfd0 hwr hsz hgrow hN hT
  exact os.File.Truncate.wp_crashG f fd name dqf sz dq d N (csInv (GF := GF) N P R γ Good Ok)
    (fun s => ghostVar γ (1 : Qp).half (some (d.ino, s) : CState))
    (fun s => Ok (some (d.ino, s))) (cs_acc N P R γ Good Ok d.ino) m bs fa fb hfd0 hwr hsz hgrow hN hT

theorem os.File.Truncate.wp_proof_crashI : os.File.Truncate.specCrashI (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sz dq d N i γ γa γc Ok a m bs fa fb hi hfd0 hwr hsz hgrow hN hT
  subst hi
  exact os.File.Truncate.wp_crashG f fd name dqf sz dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N d.ino γ γa γc Ok a) m bs fa fb hfd0 hwr hsz hgrow hN hT

end proof

end EtcdGrove
end Perennial
