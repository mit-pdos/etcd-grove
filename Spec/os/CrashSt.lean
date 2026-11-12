/-
Crash-aware specs of the `os`, `syscall` and `golang.org/x/sys/unix` calls minibolt makes on its
database file, over the generic crash invariant (`csInv N path γ Ok`, `Proof/os/CrashSt.lean`):
the caller holds its part (`csOwn path γ s`) and shows `Ok` of each state the call passes through.
Proved in `Proof/os/CrashStSpec.lean`. Lean-first (no Rocq counterpart).

* `os.OpenFile.specCrashS`: absent or idle, to `csOpen s` (created if absent); on failure maybe.
* `os.File.WriteAt.specCrashS`: idle, to an idle state the loop reached (`WReach`: each attempt
  writes a prefix of the data, `finMeta`/`finBytes`), with the data written on success. The caller
  shows `Ok` of every state the loop may pass through: each `WReach` state idle, and with the next
  attempt in flight. The write misses the frozen bytes, and the mapped cells of its range are
  passed through (`mcellsAny`).
* `os.File.Truncate.specCrashS`: idle, growing: to grown (`csGrownOwn`), or on failure maybe not
  (`ftMeta`); `Ok` of each `TReach` state, idle and with a truncate in flight.
* `syscall.Fdatasync.specCrashS` and `os.File.Sync.specCrashS`: idle `H ++ (F ++ T)` (`F` the
  frozen bytes) to `csSynced hd` (the bytes after the frozen ones synced, keeping the ones before
  them, shown clean, among the durable bytes known; or, `hd`, the ones before them), which the
  caller shows `Ok`; on failure `ok` is lost.
* `golang_org.x.sys.unix.Mmap.specCrashS`/`Munmap.specCrashS`: the mappings change.
-/
module

public import Proof.os.CrashStOps
public import Spec.golang_org.x.sys.unix.Mmap
public import Spec.golang_org.x.sys.unix.Munmap

@[expose] public section

noncomputable section

namespace Perennial

/-- The states a `WriteAt` of `data` at `off` reaches from `m`, `bs`: each attempt writes a
prefix of the data. -/
inductive WReach (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat) (data : List w8) :
    OsMeta → List (w8 × Bool) → Prop
  | refl : WReach m bs off data m bs
  | step {m' : OsMeta} {bs' : List (w8 × Bool)} (k : Nat) :
      WReach m bs off data m' bs' → k ≤ data.length →
      WReach m bs off data (finMeta m' off data k) (finBytes m' bs' off data k)

theorem WReach.narrow {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {m' : OsMeta} {bs' : List (w8 × Bool)} (h : WReach m bs off data m' bs')
    (hl : bs.length = m.size) : Narrow m bs off data m' bs' := by
  induction h with
  | refl => exact narrow_refl off data hl
  | step k _ hk ih => exact narrow_fin ih hk

/-- The states a growing `Truncate` to `sz` reaches from `m`, `bs`: unchanged, the size bound
widened (a failed attempt), grown. -/
inductive TReach (m : OsMeta) (bs : List (w8 × Bool)) (sz : Nat) :
    OsMeta → List (w8 × Bool) → Prop
  | refl : TReach m bs sz m bs
  | ft : TReach m bs sz (ftMeta m sz) bs
  | grown : TReach m bs sz (m.grown sz) (bs ++ List.replicate (sz - m.size) (0, false))

namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.OpenFile.specCrashS : Prop :=
  ∀ (path : GoString) (perm : w32) (N : Namespace) (γ : GName) (Ok : CState → Prop) (s : CState),
  (s = none ∨ ∃ m bs fa fb, s = some ⟨m, bs, fa, fb, .idle⟩) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  Ok (csOpen s) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N path γ Ok ∗ csOwn (GF := GF) path γ s }}
    (App (App (App (Val (@! os.OpenFile)) (Val #path)) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      (∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd path (DFrac.own 1) ∗
          osFd fd (DFrac.own 1) ⟨path, true, true⟩ ∗ csOwn path γ (csOpen s)) ∨
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗
        ∃ s' : CState, ⌜s' = s ∨ s' = csOpen s⌝ ∗ csOwn path γ s') }}

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.File.WriteAt.specCrashS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName)
    (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat),
  d.writable = true → 0 ≤ off.toInt → 0 < data.length → data.length ≤ 0x40000000 →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → (off.toNat + data.length ≤ fa ∨ fb ≤ off.toNat) →
  (∀ m' bs', WReach m bs off.toNat data m' bs' →
    Ok (some ⟨m', bs', fa, fb, .idle⟩) ∧ ∀ t, Ok (some ⟨m', bs', fa, fb, .write t off.toNat data⟩)) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N d.path γ Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      csOwn (GF := GF) d.path γ (some ⟨m, bs, fa, fb, .idle⟩) ∗
      mcellsAny (GF := GF) m.maps (cfLo m off.toNat) (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      mcellsAny m.maps (cfLo m off.toNat) (off.toNat + data.length) ∗
      ∃ (m' : OsMeta) (bs' : List (w8 × Bool)),
        ⌜WReach m bs off.toNat data m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ off.toNat + data.length ≤ m'.size ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        csOwn d.path γ (some ⟨m', bs', fa, fb, .idle⟩) }}

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.File.Truncate.specCrashS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (N : Namespace) (γ : GName) (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool))
    (fa fb hi : Nat),
  0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat → MapsBelow m.maps hi →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ m' bs', TReach m bs sz.toNat m' bs' →
    Ok (some ⟨m', bs', fa, fb, .idle⟩) ∧ ∀ t, Ok (some ⟨m', bs', fa, fb, .trunc t sz.toNat⟩)) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N d.path γ Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwn (GF := GF) d.path γ (some ⟨m, bs, fa, fb, .idle⟩) ∗
      mcellsAny (GF := GF) m.maps m.size hi }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ csGrownOwn d.path γ m bs fa fb sz.toNat hi) ∨
       (⌜err ≠ interface.nil⌝ ∗
         (csGrownOwn d.path γ m bs fa fb sz.toNat hi ∨
          (csOwn d.path γ (some ⟨ftMeta m sz.toNat, bs, fa, fb, .idle⟩) ∗
            mcellsAny m.maps m.size hi)))) }}

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.File.Sync.specCrashS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName)
    (Ok : CState → Prop) (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat) (hd : Bool),
  H.length = fa → fa + F.length = fb → (hd = false → ∀ y ∈ H, y.2 = true) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok (some (csSynced hd m H F T fa fb)) →
  Ok (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N d.path γ Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwn (GF := GF) d.path γ (some ⟨m, H ++ (F ++ T), fa, fb, .idle⟩) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ csOwn d.path γ (some (csSynced hd m H F T fa fb))) ∨
       (⌜err ≠ interface.nil⌝ ∗
         csOwn d.path γ (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩))) }}

variable [syscall.Assumptions] in
/-- See the file header. -/
abbrev syscall.Fdatasync.specCrashS : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName) (Ok : CState → Prop)
    (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat) (hd : Bool),
  H.length = fa → fa + F.length = fb → (hd = false → ∀ y ∈ H, y.2 = true) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok (some (csSynced hd m H F T fa fb)) →
  Ok (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N d.path γ Ok ∗ osFd (GF := GF) fd dq d ∗
      csOwn (GF := GF) d.path γ (some ⟨m, H ++ (F ++ T), fa, fb, .idle⟩) }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ csOwn d.path γ (some (csSynced hd m H F T fa fb))) ∨
       (⌜e ≠ 0⌝ ∗ csOwn d.path γ (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩))) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- See the file header. -/
abbrev golang_org.x.sys.unix.Mmap.specCrashS : Prop :=
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName)
    (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ base : Loc, Ok (some ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩)) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N d.path γ Ok ∗ osFd (GF := GF) fd dq d ∗
      csOwn (GF := GF) d.path γ (some ⟨m, bs, fa, fb, .idle⟩) }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          csOwn d.path γ (some ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩) ∗
          ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil⌝ ∗ csOwn d.path γ (some ⟨m, bs, fa, fb, .idle⟩))) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- See the file header. -/
abbrev golang_org.x.sys.unix.Munmap.specCrashS : Prop :=
  ∀ (base : Loc) (len : w64) (p : GoString) (N : Namespace) (γ : GName) (Ok : CState → Prop)
    (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  Ok (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N p γ Ok ∗
      csOwn (GF := GF) p γ (some ⟨m, bs, fa, fb, .idle⟩) ∗ cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ (e : w64), RET #(errnoErr e);
      (⌜e = 0⌝ ∗ csOwn p γ (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)) ∨
      (⌜e ≠ 0⌝ ∗
        (csOwn p γ (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩) ∨
         (csOwn p γ (some ⟨m, bs, fa, fb, .idle⟩) ∗ cellsR base 0 len.toNat vf))) }}

end spec

end EtcdGrove
end Perennial
