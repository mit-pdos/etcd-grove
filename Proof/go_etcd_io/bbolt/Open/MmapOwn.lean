/-
`db.mmapUnlocked(minsz)` in `Open`'s owned phase (U11, `notes/bbolt-proof-plan.md`; design §3.11
"Open", step 1.4; the fork's `Open` maps the file before any lock invariant exists): no writer
(`rwtx` nil), nothing mapped before; the file's bytes are held, so that the new mapping's cells of
the file's extent are known (`cellsR_agree_bytes`, around the first step of the `Mlock` load, as in
`Mmap/RemapBody`). The file's metas are not both invalid (`Open` maps a `metaOk` file), so the
mapping, once made, is kept.
-/
module

public import Proof.go_etcd_io.bbolt.Open.Close
public import Proof.go_etcd_io.bbolt.Mmap.RemapBody

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The fields `mmapUnlocked` reads in `Open`'s owned phase. -/
def mmapOwnFix (db : Loc) (lg : GoInterface) (mf mx : w64) (dq : DFrac) : IProp GF :=
  iprop(db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗ db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
    db.[DB, go!"MaxSize"] ↦{dq} mx ∗ db.[DB, go!"Mlock"] ↦□ false ∗
    db.[DB, go!"MmapFlags"] ↦□ mf ∗ db.[DB, go!"rwtx"] ↦{dq} null)

/-- **`db.mmapUnlocked(minsz)`, owned** (`Open`): the file `p` (`OsMeta` `m`, nothing mapped,
its bytes `xs` held whole), at least 8192 bytes holding a valid meta in one of its two first
slots. On success the mapping `base`/`L` (`mmapSize`'s of the larger of the file's size and
`minsz`) is in the fields and in OsFs, its client halves of the file's extent hold the file's
bytes (as bytes at a half), the rest any values. On an error (`fmt` formats it) nothing is mapped
in the fields (OsFs may keep a leaked mapping). -/
abbrev DB.mmapUnlocked.spec_own : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (lg : GoInterface) (mf mx : w64) (dq : DFrac)
    (m : OsMeta) (xs : List ByteG) (minsz : w64),
  db ≠ null → m.maps = ∅ → xs.length = m.size → m.size < 2 ^ 63 →
  (mf = W64 0 ∨ mf = W64 0x8000) →
  (8192 ≤ m.size → metaValid (metaOf (bytesAt (xs.map Prod.fst) 0 4096)) ∨
    metaValid (metaOf (bytesAt (xs.map Prod.fst) 4096 4096))) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      mmapOwnFix (GF := GF) db lg mf mx dq ∗
      db.[DB, go!"file"] ↦{dq} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨p.ino, true, true⟩ ∗ osMeta p.ino (DFrac.own 1) m ∗
      osBytes p.ino 0 (DFrac.own 1) xs ∗
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"mmapUnlocked")) (Val #minsz))
  {{ (err : GoInterface), RET #err; mmapOwnFix db lg mf mx dq ∗
      db.[DB, go!"file"] ↦{dq} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨p.ino, true, true⟩ ∗ osBytes p.ino 0 (DFrac.own 1) xs ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (base : Loc) (L : Nat),
          ⌜mmapSizeOf (max m.size (sint.nat minsz)) = some L ∧ m.size ≤ L ∧ sint.nat minsz ≤ L ∧
            8192 ≤ m.size⌝ ∗
          mapFields db (DFrac.own 1) (some (base, L)) ∗ db.[DB, go!"datasz"] ↦ W64 (L : Int) ∗
          osMeta p.ino (DFrac.own 1) (some { m with maps := GMap.singleton base L }) ∗
          bytesPointsto base (DFrac.own (1 : Qp).half) (xs.map Prod.fst) ∗
          ∃ vf, cellsR base m.size (L - m.size) vf) ∨
       (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
          mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
          ∃ m' : OsMeta, osMeta p.ino (DFrac.own 1) m')) }}

theorem DB.mmapUnlocked.wp_proof_own (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hFileSize : DB.fileSize.spec (GF := GF) (hG := hG))
    (hMmapSize : DB.mmapSize.spec (GF := GF) (hG := hG))
    (hMmapF : mmapF.spec (GF := GF) (hG := hG))
    (hPage : DB.page.spec (GF := GF) (hG := hG))
    (hMeta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : internal.common.Meta.Validate.spec (GF := GF) (hG := hG)) :
    DB.mmapUnlocked.spec_own (GF := GF) (hG := hG) := by
  intro db f fd p lg mf mx dq m xs minsz hdb hmaps hxl hsz hmf hval
  unfold mmapOwnFix
  wp_start as ⟨#Hos, ⟨#Hlg, #Hlgok, #Hps, Hmx, #Hml, #Hmff, Hrw⟩, Hfile, Hfo, Hfd, Hosm, Hxs,
    Hmf0, Hdsz⟩
  ihave %hgoos : ⌜goosLinux⌝ $$ []
  · iapply goosLinux_of_pkgInit $$ Hpkg
  ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
  · iapply goarchAmd64_of_pkgInit $$ Hpkg
  unfold goosLinux at hgoos
  unfold goarchAmd64 at hgoarch
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply hLogger db lg hdb $$ []
  · iframe #
  try wp_auto
  wp_apply hFileSize db f fd p dq (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    ⟨p.ino, true, true⟩ m rfl hsz $$ [Hfile Hfo Hfd Hosm]
    as %fsz %err ⟨Hfile, Hfo, Hfd, Hosm, Hfs⟩
  · iframe; iframe #
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlgok
  | ok li =>
  icases Hfs with (%Hfs | ⟨%hne, #HeS⟩)
  rotate_left
  · -- `fileSize` failed: logged, returned
    cases err with
    | nil => exact absurd rfl hne.1
    | ok ii =>
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    iapply HΦ
    iframe; iframe #
    iright
    isplitr
    · ipureintro; exact fun h => nomatch h
    iframe
  obtain ⟨rfl, rfl, hfs8⟩ := Hfs
  have hfz : sint.Z (W64 (m.size : Int)) = m.size := by word
  wp_auto
  wp_join iprop(∃ s : w64, size_ptr ↦ s ∗ minsz_ptr ↦ minsz ∗
      ⌜sint.Z s = max (m.size : Int) (sint.Z minsz)⌝) with [size minsz] as ⟨%sz0, size, minsz, %Hsz0⟩
  · iexists minsz; iframe; ipureintro; omega
  · iexists _; iframe; ipureintro; omega
  wp_apply hMmapSize db sz0 (by omega) as %nsz %err2 Hms
  · iframe #
  try wp_auto
  irevert Hms
  rcases hmo : mmapSizeOf (sint.nat sz0) with _ | L'
  · -- `mmapSize` failed: logged, returned
    iintro ⟨%hne, #HeS⟩
    cases err2 with
    | nil => exact absurd rfl hne.1
    | ok ii =>
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    iapply HΦ
    iframe; iframe #
    iright
    isplitr
    · ipureintro; exact fun h => nomatch h
    iframe
  iintro %Hms
  obtain ⟨rfl, hnsz⟩ := Hms
  try wp_auto
  try rw [hgoos]
  wp_join with [size fileSize db Hmx]
  · try wp_auto
    try wp_if_destruct
    all_goals try wp_auto
    all_goals try wp_if_destruct
    all_goals try wp_auto
    all_goals try wp_join_done
  try wp_auto
  wp_apply DB.munmap.wp_proof_none db (W64 0) $$ [Hmf0 Hdsz] as ⟨Hmf0, Hdsz⟩
  · iframe
  try wp_auto
  have hL'p := mmapSizeOf_props _ _ hmo
  have hnszZ : sint.Z nsz = (L' : Int) := by
    have : sint.nat nsz = (sint.Z nsz).toNat := rfl
    have h0 : 0 ≤ sint.Z nsz := by omega
    omega
  simp only [mapFields]
  icases Hmf0 with ⟨Hdr, Hdd, Hm0f, Hm1f⟩
  wp_apply hMmapF db f fd p dq (DFrac.own 1) (DFrac.own 1) mf m nsz slice.nil null (W64 0) hmf
    (by simp only [sint.Z] at hnszZ; omega) $$ [Hfile Hfo Hfd Hosm Hdr Hdd Hdsz]
    as %e ⟨Hfile, Hfo, Hfd, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%base, %hbase, Hdr, Hdd, Hdsz, Hosm, Hmc⟩ | ⟨Hdr, Hdd, Hdsz, %he, #HeS, Hres⟩)
  rotate_left
  · -- `mmap` failed: logged, returned (no deferred unmap yet)
    cases e with
    | nil => exact absurd rfl he.1
    | ok ii =>
    try rw [hgoarch]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    try simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
      show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 from rfl, List.set_cons_succ, List.set_cons_zero]
    wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 100, W8 118] _
      [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
        interface.mkOk go.int #nsz, GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    iapply HΦ
    iframe; iframe #
    iright
    isplitr
    · ipureintro; exact fun h => nomatch h
    try simp only [mapFields]
    iframe
    icases Hres with (Hosm | ⟨%b', -, Hosm, -⟩)
    · iexists m; iexact Hosm
    · iexists _; iexact Hosm
  obtain ⟨rfl, hbpos⟩ := hbase
  ihave #HmlW : (⌜True⌝ -∗ db.[DB, go!"Mlock"] ↦□ false : IProp GF) $$ []
  · iintro -; iexact Hml
  iclear Hml
  try wp_auto
  have hLn : nsz.toNat = L' := by
    have h1 := hnszZ
    simp only [sint.Z] at h1
    rw [BitVec.toInt_eq_toNat_cond] at h1
    split at h1 <;> omega
  have hmL : m.size ≤ L' := by
    have := hL'p.1; have e : sint.nat sz0 = (sint.Z sz0).toNat := rfl
    have h4 : (m.size : Int) ≤ sint.Z sz0 := by rw [Hsz0]; exact Int.le_max_left _ _
    omega
  have hminL : sint.nat minsz ≤ L' := by
    have := hL'p.1; have e : sint.nat sz0 = (sint.Z sz0).toNat := rfl
    have e2 : sint.nat minsz = (sint.Z minsz).toNat := rfl
    have h4 : sint.Z minsz ≤ sint.Z sz0 := by rw [Hsz0]; exact Int.le_max_right _ _
    omega
  have hsz0 : sint.nat sz0 = max m.size (sint.nat minsz) := by
    have e : sint.nat sz0 = (sint.Z sz0).toNat := rfl
    have e2 : sint.nat minsz = (sint.Z minsz).toNat := rfl
    omega
  have hb2 : ({ m with maps := <[base := L']> m.maps } : OsMeta).maps !! base =
      some L' := GMap.lookup_insert _ _ _
  unfold mapCells
  icases Hmc with ⟨%bs', -, Hc⟩
  rw [hLn]
  icases (cellsR_append (GF := GF) base 0 m.size (L' - m.size) _).1 $$ [Hc] with ⟨Hc0, Hc1⟩
  · rw [show m.size + (L' - m.size) = L' by omega]; iexact Hc
  rw [Nat.zero_add]
  wp_bind (App (Val (GoInstruction (GoLoad go.bool))) (Val #(db.[DB, go!"Mlock"])))
  iapply wp_load_bool_split
  ihave Hc0 : cellsR base 0 xs.length (fun i => toCellVal bs'[i]?) $$ [Hc0]
  · rw [hxl]; iexact Hc0
  iapply (cellsR_agree_bytes _ rfl p (DFrac.own 1) _ base L' hb2 _
    (fun x hx => CoPset.subseteq_top x hx) _ xs 0 _ (by omega)) $$ Hos Hosm Hxs Hc0
  iintro Hosm Hxs Hc0
  ihave #Hml := HmlW $$ []
  · ipureintro; trivial
  ihave Hml' := bool_heap _ _ _ $$ Hml
  iapply (wp_start_read _ _ _) $$ [Hml']
  · iexact Hml'
  inext
  iintro ⟨Hst, Hrest⟩
  wp_pures
  wp_bind (FinishRead _)
  iapply (wp_finish_read _ _ _) $$ [Hst Hrest]
  · iframe
  inext
  iintro -
  wp_pures
  wp_auto
  -- the file's bytes at a half
  ihave Hb : bytesPointsto base (DFrac.own (1 : Qp).half) (xs.map Prod.fst) $$ [Hc0]
  · have e := cellsR_bytes (GF := GF) base (xs.map Prod.fst) 0
    rw [List.length_map, Int.natCast_zero, loc_add_0] at e
    iapply e $$ Hc0
  have hxne : xs.map Prod.fst ≠ [] := by
    intro h; have := congrArg List.length h
    simp only [List.length_map, List.length_nil] at this; omega
  icases bytes_bounds_keep base _ _ hxne $$ Hb with ⟨%Hbb, Hb⟩
  rw [List.length_map] at Hbb
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_apply hPage db base (W64 0) (DFrac.own 1) hbpos (by decide) $$ [Hdd] as Hdd
  · iframe; iframe #
  rw [show (((0 * 4096 : Nat)) : Int) = 0 from rfl, loc_add_0]
  wp_apply hMeta base hbpos (by omega)
  try wp_auto
  wp_apply hPage db base (W64 1) (DFrac.own 1) hbpos (by decide) $$ [Hdd] as Hdd
  · iframe; iframe #
  rw [show (((1 * 4096 : Nat)) : Int) = 4096 from rfl]
  have hb1 : 0 < (base +ₗ (4096 : Int)).addr := by simp only [Loc.add]; omega
  wp_apply hMeta (base +ₗ (4096 : Int)) hb1 (by simp only [Loc.add]; omega)
  try wp_auto
  have e0 : base +ₗ (16 : Int) = base +ₗ ((16 : Nat) : Int) := by simp
  icases bytesPointsto_view_read (V := Meta) base _ (xs.map Prod.fst) 16 _ e0 (by simp; omega) hbpos
    $$ Hb with ⟨M0, C0⟩
  have hpA : 0 < (base +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
  wp_apply hValidate _ _ (DFrac.own (1 : Qp).half) hpA $$ [M0] as %ev0 ⟨M0, %He0⟩
  · iframe
  ihave Hb := C0 $$ M0
  try wp_auto
  have e1 : base +ₗ (4096 : Int) +ₗ (16 : Int) = base +ₗ ((4112 : Nat) : Int) := by
    rw [loc_add_assoc]; rfl
  icases bytesPointsto_view_read (V := Meta) base _ (xs.map Prod.fst) 4112 _ e1 (by simp; omega)
    hbpos $$ Hb with ⟨M1, C1⟩
  have hpB : 0 < (base +ₗ (4096 : Int) +ₗ (16 : Int)).addr := by
    simp only [Loc.add]; omega
  wp_apply hValidate _ _ (DFrac.own (1 : Qp).half) hpB $$ [M1] as %ev1 ⟨M1, %He1⟩
  · iframe
  ihave Hb := C1 $$ M1
  try wp_auto
  have hv' : metaValid (decode (((xs.map Prod.fst).drop 16).take 64) : Meta) ∨
      metaValid (decode (((xs.map Prod.fst).drop 4112).take 64) : Meta) := by
    have h := hval hfs8
    simp only [metaOf, bytesAt, List.drop_take, List.take_take, List.drop_drop, List.drop_zero] at h
    exact h
  have hnszE : nsz = W64 (L' : Int) := by
    apply BitVec.toInt_inj.mp
    have : sint.Z (W64 (L' : Int)) = (L' : Int) := by
      have := hL'p.2.2.1; word
    simp only [sint.Z] at this hnszZ
    rw [hnszZ, this]
  have hfin : ∀ ev1 : GoInterface, (ev1 = GoInterface.nil ↔
      metaValid (decode (((xs.map Prod.fst).drop 4112).take 64) : Meta)) →
      ¬ metaValid (decode (((xs.map Prod.fst).drop 16).take 64) : Meta) → ev1 = GoInterface.nil := by
    intro ev1 h1 h0
    exact h1.2 (hv'.resolve_left h0)
  have hnil : ev0 = GoInterface.nil ∨ ev1 = GoInterface.nil := by
    rcases hv' with h | h
    · exact .inl (He0.2 h)
    · exact .inr (He1.2 h)
  clear hfin
  rcases hnil with rfl | rfl
  rotate_left
  rcases ev0 with _ | i0
  all_goals
    try wp_auto
    iapply HΦ
    iframe; iframe #
    ileft
    isplitr
    · ipureintro; rfl
    iexists base, L'
    isplitr
    · ipureintro; exact ⟨hsz0 ▸ hmo, hmL, hminL, hfs8⟩
    try simp only [mapFields]
    rw [hmaps, GMap.insert_empty] at *
    rw [hnszE, show base +ₗ (4112 : Int) = base +ₗ (4096 : Int) +ₗ (16 : Int) by
      rw [loc_add_assoc]; rfl]
    iframe
    isplitr
    · ipureintro; exact hL'p.2.2.1
    isplitr
    · ipureintro; exact hbpos
    ipureintro; exact hL'p.2.2.2

end own

end bbolt
end EtcdGrove
end Perennial
