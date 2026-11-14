/- Lean-first (no Rocq counterpart).

# The lemmas of `Create`'s client update at the rename (W4; `CreateAu.lean`)

What `walCreate_osAUnc` needs of the invariant's parts besides `walsOk_create` (`CreateCommit.lean`):

* the claims: the creating claim occurs once (`ClaimOnce`), so the commit replaces exactly that
  occurrence (`claimOnce_repl`); the creating map after the commit (`creatingOk_create`);
* the WAL state: `createSt` is above the old state (`absLe_createSt`) with its keys in the area;
* the segments' resources: with one more layout (`laysResF_insert`), with the writes in flight
  changed only off the layouts' segments (`laysResF_congr`), and the tails (`walTailsRes_create`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCommit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.InvInos

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The commit replaces the one occurrence of the creating claim.** -/
theorem claimOnce_repl {c c' : Claim} {cl : List Claim} (h : ClaimOnce c cl) :
    ∃ l1 l2, cl = l1 ++ c :: l2 ∧ replClaim c c' cl = l1 ++ c' :: l2 := by
  classical
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  refine ⟨l1, l2, rfl, ?_⟩
  unfold replClaim
  rw [List.map_append, List.map_cons, if_pos rfl]
  have e : ∀ l : List Claim, c ∉ l → l.map (fun x => if x = c then c' else x) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons y ys ih =>
      rw [List.map_cons, if_neg (fun (e : y = c) => hl (e ▸ List.mem_cons_self ..)),
        ih (fun hm => hl (List.mem_cons_of_mem _ hm))]
  rw [e l1 h1, e l2 h2]

/-- A claim once in `cl`, neither the replaced one nor its replacement, nor of `J`, is once in the
claims after the commit. -/
theorem claimOnce_createClaims {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {cc : Ents} {J : Ino} {X : List GoString} {hJ : NamesH} {c : Claim}
    (h1 : ClaimOnce c cl) (hne0 : c ≠ (jr, N, h)) (hne1 : c ≠ (jr, N, h.log x e cc))
    (hJ1 : c.1 ≠ J) : ClaimOnce c (createClaims cl jr N h x e cc J X hJ) := by
  classical
  obtain ⟨l1, l2, rfl, hl1, hl2⟩ := h1
  let f : Claim → Claim := fun y => if y = (jr, N, h) then (jr, N, h.log x e cc) else y
  have hnf : ∀ l : List Claim, c ∉ l → c ∉ l.map f := by
    intro l hl hm
    obtain ⟨y, hy, hfy⟩ := List.mem_map.1 hm
    by_cases hy0 : y = (jr, N, h)
    · simp only [f, if_pos hy0] at hfy; exact hne1 hfy.symm
    · simp only [f, if_neg hy0] at hfy; exact hl (hfy ▸ hy)
  refine ⟨l1.map f, l2.map f ++ [(J, NameSet.except X, hJ)], ?_, hnf l1 hl1, ?_⟩
  · unfold createClaims replClaim
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append]
    rw [if_neg hne0]
  · intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hnf l2 hl2 hm
    · simp only [List.mem_singleton] at hm; exact hJ1 (by rw [hm])

/-- **The creating map after the commit** (the committed entry deleted): the other entries' claims are
not the replaced one, so they stay, once, exclusive. -/
theorem creatingOk_create {jr : Ino} {cl : List Claim}
    {CR : GMap GoString (NameSet × NamesH × Ino)}
    {dir nm : GoString} {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {cc : Ents} {J : Ino}
    {X : List GoString} {hJ : NamesH}
    (hco : CreatingOk jr cl CR) (hd : CR !! dir = some (N, h, J)) (hnmN : N.Mem nm) (hJjr : J ≠ jr) :
    CreatingOk jr (createClaims cl jr N h x e cc J X hJ) (GMap.delete dir CR) := by
  classical
  obtain ⟨-, -, hex0, -, hdist0, -, -, hJd0, -⟩ := hco dir N h J hd
  intro dir' N' h' J' hd'
  have hdd : dir' ≠ dir := by
    rintro rfl; rw [GMap.lookup_delete_eq] at hd'; cases hd'
  rw [GMap.lookup_delete_ne _ (Ne.symm hdd)] at hd'
  obtain ⟨hm, hcoh, hex, honce, hdist, hJ'jr, hJ'c, hJ'd, hJ'b⟩ := hco dir' N' h' J' hd'
  have hJJ' : J' ≠ J := hJd0 dir' (N', h', J') hdd hd'
  have hne : (jr, N', h') ≠ (jr, N, h) := by
    intro he
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact hdist0 dir' J' hdd hd'
  -- the replaced claim's names are not `N'`'s
  have hNN : ∀ b, N'.Mem b → ¬ N.Mem b :=
    hex (jr, N, h) (by obtain ⟨l1, l2, hcl, -, -⟩ := (hco dir N h J hd).2.2.2.1; rw [hcl]; simp)
      (Ne.symm hne) rfl
  have hne1 : (jr, N', h') ≠ (jr, N, h.log x e cc) := by
    intro he
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    exact hNN nm hnmN hnmN
  refine ⟨mem_createClaims_other hm hne, hcoh, ?_, claimOnce_createClaims honce hne hne1
    (fun h1 => hJjr h1.symm), ?_, hJ'jr, ?_, ?_, hJ'b⟩
  · intro c hc hcne hcj b hb
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      by_cases h0 : c0 = (jr, N, h)
      · simp only [if_pos h0]
        exact hNN b hb
      · simp only [if_neg h0] at hcne hcj ⊢
        exact hex c0 hc0 hcne hcj b hb
    · simp only [List.mem_singleton] at hc
      subst hc; exact absurd hcj hJjr
  · intro dir'' J'' hne'' hl
    by_cases h2 : dir'' = dir
    · subst h2; rw [GMap.lookup_delete_eq] at hl; cases hl
    · rw [GMap.lookup_delete_ne _ (Ne.symm h2)] at hl
      exact hdist dir'' J'' hne'' hl
  · intro c hc hcj b hb
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      by_cases h0 : c0 = (jr, N, h)
      · simp only [if_pos h0] at hcj; exact absurd hcj.symm hJ'jr
      · simp only [if_neg h0] at hcj ⊢
        exact hJ'c c0 hc0 hcj b hb
    · simp only [List.mem_singleton] at hc
      subst hc; exact absurd hcj.symm hJJ'
  · intro dir'' y hne'' hl
    by_cases h2 : dir'' = dir
    · subst h2; rw [GMap.lookup_delete_eq] at hl; cases hl
    · rw [GMap.lookup_delete_ne _ (Ne.symm h2)] at hl
      exact hJ'd dir'' y hne'' hl

/-- The commit's WAL state is above the old one, the new WAL's directory in the area. -/
theorem absLe_createSt {s : AbsDiskState} {dir : GoString} {md : List w8}
    (hd : s.wal !! dir = none) : absLe s (createSt s dir md) := by
  refine ⟨rfl, fun _ h => h, fun dir' d hd' => ?_⟩
  have hdd : dir' ≠ dir := by rintro rfl; rw [hd] at hd'; cases hd'
  refine ⟨d, ?_, Nat.le_refl _, Nat.le_refl _, id⟩
  unfold createSt
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
  exact hd'

theorem walKeysInArea_createSt {s : AbsDiskState} {dir nm : GoString} {md : List w8}
    (hin : InArea s.area dir nm) (hk : walKeysInArea s) : walKeysInArea (createSt s dir md) := by
  intro k d hkd
  show walAreaDir s.area k
  by_cases hkk : k = dir
  · subst hkk; exact ⟨nm, hin.1, hin.2⟩
  · unfold createSt at hkd
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)] at hkd
    exact hk k d hkd

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The segments' parts, layout by layout. -/
theorem laysResF_map (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) :
    laysResF (L := L) F Ls ⊣⊢ [∗map] _dir ↦ lay ∈ Ls, [∗list] g ∈ lay.segs, segResF (L := L) F g := by
  unfold laysResF segsAll
  rw [BigSepL.bigSepL_flatMap (PROP := IProp GF)]
  exact (BigSepM.bigSepM_toList (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, segResF (L := L) F g)) (m := Ls)).symm

/-- **One more layout's segments.** -/
theorem laysResF_insert (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) (dir : GoString)
    (lay : WalLay) (hd : Ls !! dir = none) :
    ([∗list] g ∈ lay.segs, segResF (L := L) F g) ∗ laysResF (L := L) F Ls ⊢
      laysResF (L := L) F (<[dir := lay]> Ls) := by
  iintro ⟨Hs, Hl⟩
  iapply (laysResF_map (L := L) F _).2
  ihave Hl := (laysResF_map (L := L) F Ls).1 $$ Hl
  iapply (BigSepM.bigSepM_insert (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, segResF (L := L) F g)) hd).2
  iframe Hs Hl

/-- **The segments' parts with the writes in flight changed off them.** -/
theorem laysResF_congr (F F' : GMap Ino SegFl) (Ls : GMap GoString WalLay)
    (h : ∀ g ∈ segsAll Ls, F' !! g.ino = F !! g.ino) :
    laysResF (L := L) F Ls ⊢ laysResF (L := L) F' Ls := by
  unfold laysResF
  refine BigSepL.bigSepL_mono (fun {k g} hk => ?_)
  have e := h g (List.mem_of_getElem? hk)
  unfold segResF
  rw [e]

/-- **The tails after the commit**: the new WAL has no open handle; the others' tails are as before,
the writes in flight unchanged on their segments. -/
theorem walTailsRes_create (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay) (F F' : GMap Ino SegFl)
    (dir : GoString) (md : List w8) (lay : WalLay) (hd : s.wal !! dir = none)
    (h : ∀ g ∈ segsAll Ls, F' !! g.ino = F !! g.ino) (hLd : Ls !! dir = none)
    (hF : ∀ i, F' !! i ≠ none → F !! i ≠ none) (hidle : TailIdle C Mr (walDurFresh md) lay) :
    walTailsRes (W := W) C Mr s Ls F ⊢
      walTailsRes (W := W) C Mr (createSt s dir md) (<[dir := lay]> Ls) F' := by
  unfold walTailsRes
  letI := walAllG (W := W)
  iintro ⟨%T, Ha, %Ho, %Hi, Hm, HL⟩
  iexists T
  ihave HL := walLentRes_insert_new (W := W) T Ls dir lay hLd $$ HL
  iframe Ha HL
  isplitr
  · ipureintro; exact Ho.insert_new hLd hF
  isplitr
  · ipureintro
    intro k d' lay' hk hd' hl'
    by_cases hkd : k = dir
    · subst hkd
      rw [GMap.lookup_insert] at hl'; cases hl'
      unfold createSt at hd'; rw [GMap.lookup_insert] at hd'; cases hd'
      exact hidle
    · unfold createSt at hd'; rw [GMap.lookup_insert_ne _ _ (Ne.symm hkd)] at hd'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hkd)] at hl'
      exact Hi k d' lay' hk hd' hl'
  iapply BigSepM.bigSepM_mono_of_forall _ $$ Hm
  intro dir' γ
  iintro ⟨%d, %lay', %g, %hp, Hv⟩
  obtain ⟨hd', hl', hg, hz, hb⟩ := hp
  have hdd : dir' ≠ dir := by rintro rfl; rw [hd] at hd'; cases hd'
  have hgm : g ∈ segsAll Ls := mem_segsAll hl' (List.mem_of_getLast? hg)
  iexists d, lay', g
  rw [h g hgm]
  iframe Hv
  ipureintro
  refine ⟨?_, ?_, hg, hz, hb⟩
  · unfold createSt; rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hd'
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hl'

end iris

end WalFs
end EtcdGrove
end Perennial

end
