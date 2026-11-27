/-
Crash-aware specs of the `os`, `syscall` and `golang.org/x/sys/unix` calls on a file in the
inode-keyed crash invariant (`csInvI N i γ γa γc Ok`, `Proof/os/CrashStI.lean`): those of
`Spec/os/CrashSt.lean` (the same loops, `WReach` and `TReach`), with `csInvI` for `csInv` and the
caller's part `csOwnI i γ γa s a` for `csOwnF γ (some (i, s))`. The caller shows `Ok a` of each state
the call passes through, its value `a` unchanged; the descriptor is of the invariant's inode
(`d.ino = i`). No open: the invariant is made from the file whole (`csInvI_alloc`), after it is
open. Reads and `Stat` use the crash-free specs, which take any fractions (`csOwnI_idle`). Proved
in `Proof/os/CrashStSpec.lean`, with `csInv`'s, from one generic proof each. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.os.CrashSt
public import Proof.os.CrashStI

@[expose] public section

noncomputable section

namespace Perennial

open Fs

namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [os.Assumptions] in
/-- `os.File.WriteAt.specCrashS` over `csInvI`. -/
abbrev os.File.WriteAt.specCrashI : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (data : List w8) (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs : List ByteG) (fa fb : Nat),
  d.ino = i → d.writable = true → 0 ≤ off.toInt → off.toNat ≤ m.size →
  off.toNat + data.length < 2 ^ 63 → 0 < data.length → data.length ≤ 0x40000000 →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → (off.toNat + data.length ≤ fa ∨ fb ≤ off.toNat) →
  (∀ nn m' bs', WReach m bs off.toNat data nn m' bs' →
    Ok a ⟨m', bs', fa, fb, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off.toNat + nn) (data.drop nn) n →
      Ok a ⟨m', bs', fa, fb, .write t (off.toNat + nn) (data.drop nn) n⟩)) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      csOwnI (GF := GF) i γ γa ⟨m, bs, fa, fb, .idle⟩ a ∗
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
        csOwnI i γ γa ⟨m', bs', fa, fb, .idle⟩ a }}

variable [os.Assumptions] in
/-- `os.File.Truncate.specCrashS` over `csInvI`. -/
abbrev os.File.Truncate.specCrashI : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64)
    (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (a : A) (m : OsMeta) (bs : List ByteG) (fa fb : Nat),
  d.ino = i → 0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ m' bs', TReach m bs sz.toNat m' bs' →
    Ok a ⟨m', bs', fa, fb, .idle⟩ ∧ ∀ t n, Ok a ⟨m', bs', fa, fb, .trunc t sz.toNat n⟩) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnI (GF := GF) i γ γa ⟨m, bs, fa, fb, .idle⟩ a ∗
      mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ ∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
          csGrownOwnI i γ γa m0 bs fa fb sz.toNat n a) ∨
       (⌜err ≠ interface.nil⌝ ∗
         ((∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
          csGrownOwnI i γ γa m0 bs fa fb sz.toNat n a) ∨
          (csOwnI i γ γa ⟨m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat,
              bs, fa, fb, .idle⟩ a ∗
            mcellsAny m.maps m.size (rsHi true m.size sz.toNat))))) }}

variable [os.Assumptions] in
/-- `os.File.Sync.specCrashS` over `csInvI`. -/
abbrev os.File.Sync.specCrashI : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd)
    (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta)
    (H F T : List ByteG) (fa fb : Nat),
  d.ino = i → H.length = fa → fa + F.length = fb → (∀ y ∈ F, y = durB y.1) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok a (csSynced m H F T fa fb) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnI (GF := GF) i γ γa ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ a }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ csOwnI i γ γa (csSynced m H F T fa fb) a) ∨
       (⌜err ≠ interface.nil⌝ ∗ csOwnI i γ γa ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ a)) }}

variable [syscall.Assumptions] in
/-- `syscall.Fdatasync.specCrashS` over `csInvI`. -/
abbrev syscall.Fdatasync.specCrashI : Prop :=
  ∀ {A : Type} [Pos.Countable A] (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (H F T : List ByteG) (fa fb : Nat),
  d.ino = i → H.length = fa → fa + F.length = fb → (∀ y ∈ F, y = durB y.1) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok a (csSynced m H F T fa fb) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ osFd (GF := GF) fd dq d ∗
      csOwnI (GF := GF) i γ γa ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ a }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ csOwnI i γ γa (csSynced m H F T fa fb) a) ∨
       (⌜e ≠ 0⌝ ∗ csOwnI i γ γa ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ a)) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- `golang_org.x.sys.unix.Mmap.specCrashS` over `csInvI`. -/
abbrev golang_org.x.sys.unix.Mmap.specCrashI : Prop :=
  ∀ {A : Type} [Pos.Countable A] (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace)
    (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs : List ByteG)
    (fa fb : Nat),
  d.ino = i → d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ base : Loc, Ok a ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ osFd (GF := GF) fd dq d ∗
      csOwnI (GF := GF) i γ γa ⟨m, bs, fa, fb, .idle⟩ a }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          csOwnI i γ γa ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ a ∗
          ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil⌝ ∗ csOwnI i γ γa ⟨m, bs, fa, fb, .idle⟩ a)) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- `golang_org.x.sys.unix.Munmap.specCrashS` over `csInvI`. -/
abbrev golang_org.x.sys.unix.Munmap.specCrashI : Prop :=
  ∀ {A : Type} [Pos.Countable A] (base : Loc) (len : w64) (i : Ino) (N : Namespace)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs : List ByteG) (fa fb : Nat)
    (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  Ok a ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗
      csOwnI (GF := GF) i γ γa ⟨m, bs, fa, fb, .idle⟩ a ∗ cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ (e : w64), RET #(errnoErr e);
      (⌜e = 0⌝ ∗ csOwnI i γ γa ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ a) ∨
      (⌜e ≠ 0⌝ ∗
        (csOwnI i γ γa ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ a ∨
         (csOwnI i γ γa ⟨m, bs, fa, fb, .idle⟩ a ∗ cellsR base 0 len.toNat vf))) }}

end spec

end EtcdGrove
end Perennial
