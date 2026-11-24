/-
**What a crash image of a WAL's files decodes to** (pure; W1 of `notes/wal-fsext-plan.md`, §2.2).
The files present are the first ones of the WAL's (a cut's new file is named only by its rename,
after the old file was truncated and synced, wal.go:882-936): every file but the last is intact (its
frames and its zero tail); the last is an image of its intended bytes that starts with its durable
records (its headers, synced before the rename, wal.go:927, and the synced operations) and has no
collision with its intended records. Then the reader's records are those of an image `I` of the
history (`walImg`), file by file, the cuts' headers included.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncSegs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

open go_etcd_io.raft.v3

section img
variable [GooseExts]

/-- The intact files of the segments `Spre` (each its frames and a zero tail of `zs`). -/
def intactFiles (C : WalCodec) (M : WalMarshal) (md : List w8) (first : Bool) (P : WalHist)
    (c : w32) (Spre : List WalHist) (zs : List Nat) : List (List w8) :=
  List.zipWith (fun rs z => segFile C rs z) (chainSegs C c (segsDs M md first P Spre)) zs

theorem crcAfter_append (C : WalCodec) (c : w32) (D E : List (w64 × List w8)) :
    crcAfter C c (D ++ E) = crcAfter C (crcAfter C c D) E := by
  simp [crcAfter, List.foldl_append]

theorem segsDs_append (M : WalMarshal) (md : List w8) (first : Bool) (P : WalHist) :
    ∀ (A B : List WalHist), segsDs M md first P (A ++ B) =
      segsDs M md first P A ++ segsDs M md (if A = [] then first else false) (P ++ A.flatten) B
  | [], B => by simp [segsDs]
  | S :: A, B => by
    simp only [List.cons_append, segsDs, List.flatten_cons, List.cons_ne_nil, ite_false]
    rw [segsDs_append M md false (P ++ S) A B, List.append_assoc]
    by_cases hA : A = [] <;> simp [hA]

/-- **What the reader reads of the last file**: a prefix of the intended records `chainRecs C c D`, at
least the first `k`, then the records `X` (P6: `X = []` from `NoCollisionFrom`,
`lastDec_of_noCollision`; a running WAL's last file, all of `D` then a torn `Save`'s entry records). -/
def LastDec (C : WalCodec) (c : w32) (D : List (w64 × List w8)) (k : Nat) (X : List WalRec)
    (last : List w8) : Prop :=
  recFrames C ((chainRecs C c D).take k) <+: last ∧
    ∃ N, k ≤ N ∧ (walDecodeFrom C true last 0 c).recs = (chainRecs C c D).take N ++ X

theorem lastDec_of_noCollision {C : WalCodec} (hC : C.Ok) {c : w32} {D : List (w64 × List w8)}
    {k : Nat} {last : List w8} (hfit : RecsFit C (chainRecs C c D))
    (hch : ChainOk C c (chainRecs C c D))
    (hdur : recFrames C ((chainRecs C c D).take k) <+: last)
    (hnc : NoCollisionFrom C c (chainRecs C c D) last) (hk : k ≤ D.length) :
    LastDec C c D k [] last := by
  have hhi := walDecodeFrom_prefix hC hfit hch hnc
  have hlo := walDecodeFrom_of_prefix hC true
    (fun r hr => hfit r (List.mem_of_mem_take hr))
    ((chainOk_append C c _ _).mp (by rw [List.take_append_drop]; exact hch)).1 hdur
  have hNlo := hlo.length_le
  refine ⟨hdur, (walDecodeFrom C true last 0 c).recs.length, ?_, by
    rw [List.append_nil]; exact List.prefix_iff_eq_take.mp hhi⟩
  simp only [List.length_take, length_chainRecs] at hNlo
  omega

/-- **The reader on intact files then an image of the next file's intended bytes.** -/
theorem walDecodeFiles_core {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8)
    (S : List WalOp) (m' : Nat) (X : List WalRec) (last : List w8) :
    ∀ (Spre : List WalHist) (zs : List Nat) (first : Bool) (P : WalHist) (c : w32),
    zs.length = Spre.length → (∀ z ∈ zs, z = 0 ∨ 8 ≤ z) →
    RecsFit C (chainRecs C c (segsDs M md first P (Spre ++ [S])).flatten) →
    (let first' := if Spre = [] then first else false
     let P' := P ++ Spre.flatten
     let c' := crcAfter C c (segsDs M md first P Spre).flatten
     let D := segHdrDs M md first' P' ++ S.flatMap (opDs M)
     LastDec C c' D ((segHdrDs M md first' P').length + ((S.take m').flatMap (opDs M)).length)
       X last) →
    ∃ n, ((S.take m').flatMap (opDs M)).length ≤ n ∧
      (walDecodeFiles C (intactFiles C M md first P c Spre zs ++ [last]) c).recs =
        chainRecs C c ((segsDs M md first P (Spre ++ [histCut M S n])).flatten ++ histCutRest M S n) ++
          X := by
  intro Spre
  induction Spre with
  | nil =>
    intro zs first P c hzl _ hfit hlast
    have hzs : zs = [] := List.eq_nil_of_length_eq_zero hzl
    subst hzs
    simp only [ite_eq_left, List.flatten_nil, List.append_nil, segsDs, crcAfter, List.foldl_nil,
      List.nil_append] at hlast hfit ⊢
    obtain ⟨-, N, hNlo, ht⟩ := hlast
    refine ⟨N - (segHdrDs M md first P).length, by omega, ?_⟩
    show (walDecodeFrom C true last 0 c).recs = _
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    rw [flatMap_histCut]
    have e : segHdrDs M md first P ++ (S.flatMap (opDs M)).take (N - (segHdrDs M md first P).length)
        = (segHdrDs M md first P ++ S.flatMap (opDs M)).take N := by
      rw [List.take_append, List.take_of_length_le (l := segHdrDs M md first P) (by omega)]
    rw [e, chainRecs_take]
    exact ht
  | cons S0 Spre ih =>
    intro zs first P c hzl hz hfit hlast
    obtain ⟨z, zs', rfl⟩ : ∃ z zs', zs = z :: zs' := by
      cases zs with
      | nil => simp at hzl
      | cons z zs' => exact ⟨z, zs', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hzl
    obtain ⟨D0, hD0⟩ : ∃ D0, D0 = segHdrDs M md first P ++ S0.flatMap (opDs M) := ⟨_, rfl⟩
    have hsd : ∀ X : List WalHist, (segsDs M md first P (S0 :: X)).flatten =
        D0 ++ (segsDs M md false (P ++ S0) X).flatten := fun X => by simp [segsDs, hD0]
    have hfit0 : RecsFit C (chainRecs C c D0) := fun r hr => hfit r (by
      rw [List.cons_append, hsd, chainRecs_append]; exact List.mem_append_left _ hr)
    have hfit1 : RecsFit C (chainRecs C (crcAfter C c D0)
        (segsDs M md false (P ++ S0) (Spre ++ [S])).flatten) := fun r hr => hfit r (by
      rw [List.cons_append, hsd, chainRecs_append]; exact List.mem_append_right _ hr)
    have hch0 : ChainOk C c (chainRecs C c D0) := by
      rw [hD0]; exact chainOk_chainRecs hC c _ (by simpa [segsDs] using segsDs_crcOk M md first P [S0])
    obtain ⟨n, hn, ih'⟩ := ih zs' false (P ++ S0) (crcAfter C c D0) hzl
      (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz')) hfit1 (by
        simp only [List.cons_ne_nil, ite_false, List.flatten_cons, ite_self] at hlast ⊢
        rw [hsd, crcAfter_append] at hlast
        simpa only [List.append_assoc] using hlast)
    refine ⟨n, hn, ?_⟩
    have hf : intactFiles C M md first P c (S0 :: Spre) (z :: zs') =
        segFile C (chainRecs C c D0) z :: intactFiles C M md false (P ++ S0) (crcAfter C c D0) Spre zs' := by
      simp [intactFiles, segsDs, chainSegs, hD0]
    rw [hf, List.cons_append, List.cons_append, hsd, List.append_assoc, chainRecs_append C c D0, List.append_assoc, ← ih']
    obtain ⟨g, gs, hg⟩ : ∃ g gs, intactFiles C M md false (P ++ S0) (crcAfter C c D0) Spre zs' ++ [last]
        = g :: gs := by
      cases intactFiles C M md false (P ++ S0) (crcAfter C c D0) Spre zs' with
      | nil => exact ⟨last, [], rfl⟩
      | cons g gs => exact ⟨g, gs ++ [last], rfl⟩
    rw [hg]
    simp only [walDecodeFiles, walDecodeFrom_segFile hC false hfit0 hch0 (hz z (by simp)),
      chainEnd_chainRecs, ite_true]

/-- A history image inside a segment is one of the whole history, the segments before it kept. -/
theorem walImgS_lift {P S R : WalHist} {m m' : Nat} {J : WalHist} (h : walImgS S m' J)
    (hm : m ≤ P.length + m') : walImgS (P ++ S ++ R) m (P ++ J) := by
  obtain ⟨j, h1, h2, rfl⟩ := h
  have htk : (P ++ S ++ R).take (P.length + j) = P ++ S.take j := by
    rw [List.append_assoc, List.take_append, List.take_of_length_le (l := P) (by omega),
      Nat.add_sub_cancel_left, List.take_append_of_le_length h2]
  exact ⟨P.length + j, by omega, by simp; omega, htk.symm⟩

/-- **(b) + (c) over files: what a crash image of a WAL's files decodes to.** The WAL's segments
are `Spre ++ S :: Spost` (its history `H` their concatenation), its first `m` operations synced;
the files present are those of `Spre`, intact (frames, zero tails `zs`), then an image `last` of
`S`'s file that starts with its headers and the synced operations' records and has no collision with
its records (`LastDec`; the files after it absent). Then the reader's records are the WAL's records for the
segments `Spre ++ [J]` of an image `I` of `H`. -/
theorem walDecodeFiles_walImg {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8)
    (Spre : List WalHist) (S : WalHist) (Spost : List WalHist) (zs : List Nat) (last : List w8)
    (m : Nat) (hzl : zs.length = Spre.length) (hz : ∀ z ∈ zs, z = 0 ∨ 8 ≤ z)
    (hfit : RecsFit C (recsOfSegs C M md (Spre ++ S :: Spost)))
    (hm : m ≤ Spre.flatten.length + S.length)
    (hlast :
      let first' := if Spre = [] then true else false
      let c' := crcAfter C 0#32 (segsDs M md true [] Spre).flatten
      let D := segHdrDs M md first' Spre.flatten ++ S.flatMap (opDs M)
      LastDec C c' D ((segHdrDs M md first' Spre.flatten).length +
          ((S.take (m - Spre.flatten.length)).flatMap (opDs M)).length) [] last) :
    ∃ I Ss' ps, walImgS (Spre ++ S :: Spost).flatten m I ∧ Ss'.flatten = I ∧
      (∀ p ∈ ps, p.1 = entryType) ∧
      (walDecodeFiles C (intactFiles C M md true [] 0#32 Spre zs ++ [last]) 0#32).recs =
        chainRecs C 0#32 ((segsDs M md true [] Ss').flatten ++ ps) := by
  have hfit' : RecsFit C (chainRecs C 0#32 (segsDs M md true [] (Spre ++ [S])).flatten) := by
    intro r hr; apply hfit
    unfold recsOfSegs
    rw [show Spre ++ S :: Spost = (Spre ++ [S]) ++ Spost by simp, segsDs_append,
      List.flatten_append, chainRecs_append]
    exact List.mem_append_left _ hr
  obtain ⟨n, hn, hdec⟩ := walDecodeFiles_core hC M md S (m - Spre.flatten.length) [] last Spre zs
    true [] 0#32 hzl hz hfit' (by simpa using hlast)
  rw [List.append_nil] at hdec
  refine ⟨Spre.flatten ++ histCut M S n, Spre ++ [histCut M S n], histCutRest M S n, ?_, by simp,
    histCutRest_entry M S n, hdec⟩
  have hJ := walImgS_histCut M S (m - Spre.flatten.length) n (by omega) hn
  have := walImgS_lift (P := Spre.flatten) (R := Spost.flatten) (m := m) hJ (by omega)
  simpa using this

end img

end WalEnc
end EtcdGrove
end Perennial
