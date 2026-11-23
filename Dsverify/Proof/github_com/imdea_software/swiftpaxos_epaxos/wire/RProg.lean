/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Proof/wire/RProg.lean (notes/dsv-epaxos.md),
restated over dsv-bufio's `*bufio.Reader` (`rdOwn`, `BufRd`): the stream facts come from the
reader's stream fact `rd.F` (`bufio.ownBufReader_fact`, never unfolding the reader), a step later;
`io.ReadFull`/`io.ReadAtLeast` through the reader are Perennial's (`io.wp_ReadFull`,
`io.wp_ReadAtLeast`) over `bufio.ownBufReader_readerOk`. The lab's error fact (`errOrNil`) is
gone: an error is only non-`nil`.

Reading an encoding from a `*bufio.Reader` (internal to the wire package): the stream facts
(`nextIs`) carried along a decoder, and `ReadFull` / `ReadAtLeast` on the buffered reader (as an
`io.Reader`, `brIface`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Marshal
public import Proof.bufio.ReaderLaws
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps
public import Proof.bufio.Own
public import Perennial.Proof.io.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS BufRd.F_persistent

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-! ## Stream facts -/

/-- `nextIs` moves past bytes `d` already read, given a pure code fact. -/
theorem nextIs_shift {A B : Type} (rd : BufRd GF) (R d : List w8)
    (enc : A → List w8) (wf : A → Prop) (enc' : B → List w8) (wf' : B → Prop)
    (h : ∀ (v : A) (ext t : List w8), wf v → d ++ t <+: enc v ++ ext →
      ∃ (v' : B) (ext' : List w8), wf' v' ∧ t <+: enc' v' ++ ext') :
    nextIs rd R enc wf ⊢ nextIs rd (R ++ d) enc' wf' := by
  unfold nextIs
  iintro #H
  imodintro
  iintro %S HS
  ihave Hp := H $$ %S HS
  inext
  icases Hp with %Hp
  ipureintro
  intro hpre
  have hR : R <+: S := (List.prefix_append R d).trans hpre
  obtain ⟨v, ext, hv, hx⟩ := Hp hR
  obtain ⟨u, hu⟩ := hpre
  subst hu
  refine h v ext _ hv ?_
  have : (R ++ d ++ u).drop R.length = d ++ u := by simp
  rw [this] at hx
  simpa using hx

/-- `nextIs` of a total code (every byte string is a prefix of some encoding). -/
theorem nextIs_total {A : Type} (rd : BufRd GF) (R : List w8)
    (enc : A → List w8) (wf : A → Prop)
    (h : ∀ t : List w8, ∃ (v : A) (ext : List w8), wf v ∧ t <+: enc v ++ ext) :
    ⊢ nextIs rd R enc wf := by
  unfold nextIs
  iintro !> %S -
  inext
  ipureintro
  intro _
  exact h _

/-- A fixed-length code whose words are all encodings is total. -/
theorem total_of_fixed {A : Type} (enc : A → List w8) (n : Nat) (hl : ∀ v, (enc v).length = n)
    (hs : ∀ t : List w8, t.length = n → ∃ v, enc v = t) (t : List w8) :
    ∃ (v : A) (ext : List w8), True ∧ t <+: enc v ++ ext := by
  obtain ⟨v, hv⟩ := hs ((t ++ List.replicate n (W8 0)).take n) (by simp)
  refine ⟨v, t.drop n, trivial, ?_⟩
  rw [hv, List.take_append]
  by_cases htn : t.length ≤ n
  · rw [List.drop_eq_nil_of_le htn, List.append_nil, List.take_of_length_le htn]
    exact List.prefix_append _ _
  · have : n - t.length = 0 := by omega
    rw [this, List.take_zero, List.append_nil, List.take_append_drop]
    exact List.prefix_refl _

/-- What the reader has returned since `R` is a prefix of an encoding (a step later). -/
theorem nextIs_read {A : Type} (br : Loc) (rd : BufRd GF)
    (R d : List w8) (enc : A → List w8) (wf : A → Prop) :
    (nextIs rd R enc wf ∗ rdOwn br rd (R ++ d)) ⊢
      rdOwn br rd (R ++ d) ∗ ▷ ⌜∃ (v : A) (ext : List w8), wf v ∧ d <+: enc v ++ ext⌝ := by
  iintro ⟨#H, Hr⟩
  ihave ⟨Hr, #HF⟩ := EtcdGrove.bufio.ownBufReader_fact br rd.ri rd.Pre rd.S rd.E (R ++ d) rd.F
    rd.F_of rd.F_pre $$ Hr
  iframe Hr
  iunfold nextIs at H
  ihave Hp := H $$ %_ HF
  inext
  icases Hp with %Hp
  ipureintro
  obtain ⟨v, ext, hv, hx⟩ := Hp (List.prefix_append _ _)
  refine ⟨v, ext, hv, ?_⟩
  simpa using hx

variable [bufio.Assumptions] [io.Assumptions]

/-- `io`'s error values a reader's results name. -/
theorem io_errs :
    isPkgInit (PROP := IProp GF) pkg_id.bufio ⊢ ∃ eof ueof sb : GoInterface,
      ⌜ueof ≠ interface.nil ∧ sb ≠ interface.nil⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr io.ErrShortBuffer ↦□ sb := by
  iintro #Hb
  ihave #Hio := EtcdGrove.bufio.io_init_of_bufio $$ Hb
  ihave Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, #Hsb, #HEOF, #HUEOF, -⟩
  iunfold errors.newVar at Hsb HEOF HUEOF
  icases Hsb with ⟨%xs, #Hsb, -⟩
  icases HEOF with ⟨%xe, #HEOF, -⟩
  icases HUEOF with ⟨%xu, #HUEOF, -⟩
  iexists _, _, _
  iframe Hio HEOF HUEOF Hsb
  ipureintro
  exact ⟨by simp, by simp⟩

set_option goose.wp.extras true

variable [EpBufioDeps GF]

/-- `io.ReadFull(br, buf)` on the buffered reader. -/
theorem wp_ReadFull_br (br : Loc) (rd : BufRd GF)
    (R : List w8) (buf : GoSlice) (bs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ rdOwn br rd R ∗ buf ↦* bs }}
      (App (App (Val (@! io.ReadFull)) (Val #(brIface br))) (Val #buf))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ data.length = bs.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗ rdOwn br rd (R ++ data) }} := by
  iintro %Φ ⟨#Hpkg, Hown, Hb⟩ HΦ
  ihave ⟨%eof, %ueof, %sb, %Hne, #Hio, #Heof, #Hueof, -⟩ := io_errs $$ Hpkg
  ihave #Hok := EtcdGrove.bufio.ownBufReader_readerOk EpBufioDeps.readOk br
    rd.ri rd.Pre rd.S rd.E
  rw [show brIface br = interface.ok (EtcdGrove.bufio.readerIface br) from rfl]
  wp_apply io.wp_ReadFull (EtcdGrove.bufio.readerIface br) _
    (EtcdGrove.bufio.ownBufReader br rd.ri rd.Pre rd.S rd.E) _ R buf bs eof ueof
    $$ [$Hio $Hok $Heof $Hueof $Hown $Hb] as %n %err ⟨%ys, %Hys, Hb, Hown, #Hres⟩
  · ipureintro; intro ys _ hm; exact rd.Pre_pos _ _ hm
  obtain ⟨hn, hle⟩ := Hys
  iunfold io.readFullRes at Hres
  iapply HΦ
  iexists ys
  iframe Hb Hown
  icases Hres with (%Hr | ⟨%e, %Hr, -⟩)
  · ipureintro
    exact ⟨EtcdGrove.bufio.w64_of_sintZ hn, hle, by simp [Hr.1, Hr.2]⟩
  · ipureintro
    obtain ⟨hlt, hne, h1, h2⟩ := Hr
    refine ⟨EtcdGrove.bufio.w64_of_sintZ hn, hle, ?_⟩
    constructor
    · intro herr
      by_cases hc : e = eof ∧ ys ≠ []
      · exact absurd (h1 hc ▸ herr) Hne.1
      · exact absurd (h2 hc ▸ herr) hne
    · intro h; omega

/-- `io.ReadAtLeast(br, buf, min)` on the buffered reader. -/
theorem wp_ReadAtLeast_br (br : Loc) (rd : BufRd GF)
    (R : List w8) (buf : GoSlice) (bs : List w8) (min : w64) (hmin : sint.Z min ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ rdOwn br rd R ∗ buf ↦* bs }}
      (App (App (App (Val (@! io.ReadAtLeast)) (Val #(brIface br))) (Val #buf)) (Val #min))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ sint.Z min ≤ data.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗ rdOwn br rd (R ++ data) }} := by
  iintro %Φ ⟨#Hpkg, Hown, Hb⟩ HΦ
  ihave ⟨%eof, %ueof, %sb, %Hne, #Hio, #Heof, #Hueof, #Hsb⟩ := io_errs $$ Hpkg
  ihave #Hok := EtcdGrove.bufio.ownBufReader_readerOk EpBufioDeps.readOk br
    rd.ri rd.Pre rd.S rd.E
  rw [show brIface br = interface.ok (EtcdGrove.bufio.readerIface br) from rfl]
  wp_apply io.wp_ReadAtLeast (EtcdGrove.bufio.readerIface br) _
    (EtcdGrove.bufio.ownBufReader br rd.ri rd.Pre rd.S rd.E) _ R buf bs min eof ueof sb
    $$ [$Hio $Hok $Heof $Hueof $Hsb $Hown $Hb] as %n %err ⟨%ys, %Hys, Hb, Hown, #Hres⟩
  · ipureintro; intro ys _ hm; exact rd.Pre_pos _ _ hm
  obtain ⟨hn, hle⟩ := Hys
  iunfold io.readAtLeastRes at Hres
  iapply HΦ
  iexists ys
  iframe Hb Hown
  icases Hres with (%Hr | %Hr | ⟨%e, %Hr, -⟩)
  · exfalso; omega
  · ipureintro
    exact ⟨EtcdGrove.bufio.w64_of_sintZ hn, hle, by simp [Hr.2.2, Hr.2.1]⟩
  · ipureintro
    obtain ⟨-, hlt, hne, h1, h2⟩ := Hr
    refine ⟨EtcdGrove.bufio.w64_of_sintZ hn, hle, ?_⟩
    constructor
    · intro herr
      by_cases hc : e = eof ∧ ys ≠ []
      · exact absurd (h1 hc ▸ herr) Hne.1
      · exact absurd (h2 hc ▸ herr) hne
    · intro h; omega

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
