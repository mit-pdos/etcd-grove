/-
The extension's operations over a file in a `csInvI` (`Proof/os/CrashStI.lean`), the inode-keyed
crash invariant: `csI_acc` is its accessor (`CsAcc`, `CrashStOps.lean`: opened with the caller's
token `csTokI`, whose state it updates on closing; the value `a` is unchanged), and each operation
is the instance of the generic one (`wp_..._g`), as `wp_..._cs` is for `csInv`. The caller's part
is `csOwnI i γ γa s a`; it shows `Ok a` of each state the call passes through. The file's descriptor
is of the invariant's inode (`d.ino = i`). Lean-first (no Rocq counterpart).

* `wp_osPWriteStart_csI`/`wp_osPWriteFinish_csI`, `wp_osFtruncateStart_csI`/`wp_osFtruncateFinish_csI`,
  `wp_osFsync_csI` (`fsync` and `fdatasync`), `wp_osMmap_csI`, `wp_osMunmap_csI`.
-/
module

public import Proof.os.CrashStI

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {A : Type} [Pos.Countable A]

/-- **`csInvI`'s accessor**, the caller's value being `a`: the caller's token is its halves of the
two ghost variables; the state's is updated on closing. -/
theorem csI_acc (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) :
    CsAcc (L := L) N (csInvI (L := L) N i γ γa γc Ok) (csTokI γ γa a) (Ok a) i := by
  unfold CsAcc csTokI
  intro E s hE
  iintro #Hinv ⟨Hv, Ha⟩
  imod csInvI_open N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, %Hok, Hclose⟩
  imodintro
  iframe Hr
  isplitr
  · ipureintro; exact Hok
  iintro %s' %hs' Hr'
  imod ghostVar_update_halves s' γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Ha' Hr'] with -
  · inext; unfold csInvIBody; ileft; iexists s', a; iframe; ipureintro; exact hs'
  imodintro; iframe

/-- `wp_osPWriteStart_g` over `csInvI`. -/
theorem wp_osPWriteStart_csI (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta)
    (bs : List ByteG) (fa fb : Nat) (hi : d.ino = i) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hgap : off.toNat ≤ m.size) (hd : data ≠ [])
    (hfz : off.toNat + data.length ≤ fa ∨ fb ≤ off.toNat)
    (hok : ∀ t n, PwFresh m bs off.toNat data n → Ok a ⟨m, bs, fa, fb, .write t off.toNat data n⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInvI (L := L) N i γ γa γc Ok -∗ osFd (L := L) fd dq d -∗
      csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .idle⟩ a -∗
      mcellsAny (L := L) m.maps (cfLo m off.toNat) (off.toNat + data.length) -∗
      (∀ t : Nat, ∀ n : Nat, ⌜PwFresh m bs off.toNat data n⌝ -∗ osFd (L := L) fd dq d -∗
        csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .write t off.toNat data n⟩ a -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  subst hi
  exact wp_osPWriteStart_g fd off data dq d N (csInvI (L := L) N d.ino γ γa γc Ok) _ _
    (csI_acc N d.ino γ γa γc Ok a) m bs fa fb hN hwr hoff hgap hd hfz hok Φ

/-- `wp_osPWriteFinish_g` over `csInvI`. -/
theorem wp_osPWriteFinish_csI (t : Nat) (i : Ino) (off : Nat) (data : List w8) (n : Nat)
    (N : Namespace) (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta)
    (bs : List ByteG) (fa fb : Nat) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : ∀ k (zs : List Cands), k ≤ data.length → off ≤ m.size →
      zs.length = pwSize m.size off k - m.size → ZsOk m zs →
      Ok a ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInvI (L := L) N i γ γa γc Ok -∗
      csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .write t off data n⟩ a -∗
      (∀ (k : Nat) (e : w64) (zs : List Cands),
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧ off ≤ m.size ∧
          zs.length = pwSize m.size off k - m.size ∧ ZsOk m zs⌝ -∗
        csOwnI (L := L) i γ γa ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb,
          .idle⟩ a -∗
        mcells (L := L) m.maps (cfLo m off) (off + data.length)
          (pwCell m.size off data k (cfRange m bs off data.length)) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} :=
  wp_osPWriteFinish_g t i off data n N (csInvI (L := L) N i γ γa γc Ok) _ _
    (csI_acc N i γ γa γc Ok a) m bs fa fb hN hok Φ

/-- `wp_osFtruncateStart_g` over `csInvI`. -/
theorem wp_osFtruncateStart_csI (fd sz : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs : List ByteG) (fa fb : Nat)
    (hi : d.ino = i) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true)
    (hsz0 : 0 ≤ sz.toInt) (hgrow : m.size ≤ sz.toNat)
    (hok : ∀ t n, Ok a ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInvI (L := L) N i γ γa γc Ok -∗ osFd (L := L) fd dq d -∗
      csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .idle⟩ a -∗
      mcellsAny (L := L) m.maps m.size (rsHi true m.size sz.toNat) -∗
      (∀ t : Nat, ∀ n : Nat, osFd (L := L) fd dq d -∗
        csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩ a -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) {{ Φ }} := by
  subst hi
  exact wp_osFtruncateStart_g fd sz dq d N (csInvI (L := L) N d.ino γ γa γc Ok) _ _
    (csI_acc N d.ino γ γa γc Ok a) m bs fa fb hN hwr hsz0 hgrow hok Φ

/-- `wp_osFtruncateFinish_g` over `csInvI`. -/
theorem wp_osFtruncateFinish_csI (t : Nat) (i : Ino) (sz n : Nat) (N : Namespace)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs : List ByteG) (fa fb : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hokG : ∀ zs : List Cands, zs.length = sz - m.size →
      Ok a ⟨rsPost true m sz sz, bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])), fa, fb, .idle⟩)
    (hokF : Ok a ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInvI (L := L) N i γ γa γc Ok -∗
      csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .trunc t sz n⟩ a -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csGrownOwnI (L := L) i γ γa m bs fa fb sz n a) ∨
         (⌜e ≠ 0⌝ ∗ (csGrownOwnI (L := L) i γ γa m bs fa fb sz n a ∨
           (csOwnI (L := L) i γ γa ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb,
              .idle⟩ a ∗
             mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsOld m.size m.size []))))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) {{ Φ }} :=
  wp_osFtruncateFinish_g t i sz n N (csInvI (L := L) N i γ γa γc Ok) _ _
    (csI_acc N i γ γa γc Ok a) m bs fa fb hN hokG hokF Φ

/-- `wp_osFsync_g` over `csInvI`. -/
theorem wp_osFsync_csI (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (H F T : List ByteG) (fa fb : Nat)
    (hi : d.ino = i) (hH : H.length = fa) (hF : fa + F.length = fb) (hFd : ∀ y ∈ F, y = durB y.1)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hok : Ok a (csSynced m H F T fa fb)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInvI (L := L) N i γ γa γc Ok -∗ osFd (L := L) fd dq d -∗
      csOwnI (L := L) i γ γa ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ a -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwnI (L := L) i γ γa (csSynced m H F T fa fb) a) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ csOwnI (L := L) i γ γa ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ a)) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  subst hi
  exact wp_osFsync_g fd dq d N (csInvI (L := L) N d.ino γ γa γc Ok) _ _
    (csI_acc N d.ino γ γa γc Ok a) m H F T fa fb hH hF hFd hN hok Φ

/-- `wp_osMmap_g` over `csInvI`. -/
theorem wp_osMmap_csI (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs : List ByteG) (fa fb : Nat)
    (hi : d.ino = i) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hrd : d.readable = true) (hoff : off = 0)
    (hlen : 0 < len.toInt) (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE)
    (hok : ∀ base : Loc, Ok a ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInvI (L := L) N i γ γa γc Ok -∗ osFd (L := L) fd dq d -∗
      csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .idle⟩ a -∗
      (∀ base : Loc, ∀ e : w64,
        ((⌜e = 0 ∧ 0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ ∗
            csOwnI (L := L) i γ γa ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ a ∗
            ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
         (⌜e ≠ 0 ∧ base = null⌝ ∗ csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .idle⟩ a)) -∗
        osFd (L := L) fd dq d -∗ Φ (PairV (#base) (#e))) -∗
      WP (ExternalOp fsExt.name "Mmap"
        (Val (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))))) {{ Φ }} := by
  subst hi
  exact wp_osMmap_g fd off len prot fl dq d N (csInvI (L := L) N d.ino γ γa γc Ok) _ _
    (csI_acc N d.ino γ γa γc Ok a) m bs fa fb hN hrd hoff hlen hprot hfl hok Φ

/-- `wp_osMunmap_g` over `csInvI`. -/
theorem wp_osMunmap_csI (base : Loc) (len cap : w64) (i : Ino) (N : Namespace) (γ γa γc : GName)
    (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs : List ByteG) (fa fb n : Nat) (vf : Nat → val)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hb : m.maps !! base = some n) (hlen : len.toNat = n)
    (hcap : cap.toNat = n)
    (hok : Ok a ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInvI (L := L) N i γ γa γc Ok -∗
      csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .idle⟩ a -∗ cellsR base 0 n vf -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwnI (L := L) i γ γa ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ a) ∨
         (⌜e ≠ 0⌝ ∗
           (csOwnI (L := L) i γ γa ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ a ∨
            (csOwnI (L := L) i γ γa ⟨m, bs, fa, fb, .idle⟩ a ∗ cellsR base 0 n vf)))) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Munmap" (Val (PairV (#base) (PairV (#len) (#cap))))) {{ Φ }} :=
  wp_osMunmap_g base len cap i N (csInvI (L := L) N i γ γa γc Ok) _ _
    (csI_acc N i γ γa γc Ok a) m bs fa fb n vf hN hb hlen hcap hok Φ

end ops

end Perennial
