/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: pure facts of the wire

* **The answers' wire is prefix-free** (`respsWire_prefix_decode`): if the wire of answers `A`, each
  delimited by its `Content-Length` (`respOk`, not `close`), followed by more bytes is a prefix of the wire
  of answers `Rs` (each such an answer or net/http's `400`), then `Rs` starts with `A` and has one more.
  By `respWire_inj`: an answer's wire followed by anything is read back as that answer, the status line
  up to its LF (the status a decimal without a space, the reason without LF), the header lines `k: v`
  up to the empty line (a key without `:`, neither starts with CR), then the body by its
  `Content-Length` (`fmt.decimalNat` is injective); net/http's `400` has no `Content-Length`, so no
  such answer's wire starts it.
* The driver's requests are ones the server reads as written (`DReq.reqOk`), its junk is junk
  (`junkWire_ok`), their paths and the mux's two patterns (`DReq.route`: `/echo` and `/status` are routed
  to their handlers, every other path is not redirected and under neither pattern).
* Header lines: `hdrGetL` through `dropConn`, `Content-Length`'s value (`fmtInt_small`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs
public import Perennial.Proof.internal.strconv.FormatBasics
public import Perennial.Proof.fmt.DoPrintfLemmas

@[expose] public section

noncomputable section

namespace Perennial

open net.http (HReq Resp RespSlot ReqSlot HdrLine)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

/-! ## Bytes and lists -/

theorem wire_nm_app {c : w8} {a b : List w8} (ha : c ∉ a) (hb : c ∉ b) : c ∉ a ++ b :=
  fun h => (List.mem_append.1 h).elim ha hb

theorem wire_nm_cons {c x : w8} {l : List w8} (hx : c ≠ x) (hl : c ∉ l) : c ∉ x :: l :=
  fun h => (List.mem_cons.1 h).elim hx hl

theorem wire_nm_all {p : w8 → Bool} {l : List w8} {c : w8} (hl : ∀ x ∈ l, p x = true)
    (hc : p c = false) : c ∉ l := fun h => by
  have := hl c h
  rw [hc] at this
  exact Bool.false_ne_true this

/-- A list split at its first `c`: the parts before it and after it are determined. -/
theorem wire_split_at (c : w8) (a a' u v : List w8) (ha : c ∉ a) (ha' : c ∉ a')
    (h : a ++ c :: u = a' ++ c :: v) : a = a' ∧ u = v := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simp only [List.nil_append, List.cons.injEq, true_and] at h; exact ⟨rfl, h⟩
    | cons b a' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [h.1]; exact List.mem_cons_self) ha'
  | cons b a ih =>
    cases a' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [← h.1]; exact List.mem_cons_self) ha
    | cons b' a' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih a' (fun hm => ha (List.mem_cons_of_mem _ hm))
        (fun hm => ha' (List.mem_cons_of_mem _ hm)) h
      exact ⟨by rw [this.1], this.2⟩

/-- A decimal's bytes are digits. -/
theorem wire_dec_nm (n : Nat) {c : w8} (hc : c.toNat < 48 ∨ 57 < c.toNat) :
    c ∉ fmt.decimalNat n := fun h => by
  have h' : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := fmt.decimalNat_isDigit n c h
  omega

theorem decimalNat_inj {n m : Nat} (h : fmt.decimalNat n = fmt.decimalNat m) : n = m :=
  calc n = (fmt.decimalNat n).foldl fmt.digitStep 0 := (fmt.foldl_digitStep_decimalNat n).symm
    _ = (fmt.decimalNat m).foldl fmt.digitStep 0 := by rw [h]
    _ = m := fmt.foldl_digitStep_decimalNat m

/-! ## The answers' wire is prefix-free -/

/-- What reading an answer's head back needs of it: its reason and header lines as `respOk` has
them (net/http's `400` too). -/
def wireShape (ρ : Resp) : Prop :=
  ρ.reason.all net.http.valByte = true ∧ ∀ kv ∈ ρ.hc, net.http.hdrLineOk kv

theorem wireShape_of_ok {ρ : Resp} (h : net.http.respOk ρ) : wireShape ρ :=
  ⟨h.2.2.1, h.2.2.2.1.2⟩

theorem wireShape_bad : wireShape net.http.badResp := ⟨by decide, net.http.badHdr_ok.2⟩

/-- An answer's wire, cut at the status line's LF and at the empty line. -/
theorem respWire_split (ρ : Resp) (S : List w8) :
    net.http.respWire ρ ++ S =
      (go!"HTTP/1.1 " ++ (fmt.decimalNat (uint.nat ρ.st) ++ W8 32 :: (ρ.reason ++ [W8 13]))) ++
        W8 10 :: (ρ.hc.flatMap net.http.hdrLineWire ++ W8 13 :: W8 10 :: (ρ.body ++ S)) := by
  simp only [net.http.respWire, net.http.respHeadWire, net.http.hdrWire, List.append_assoc,
    List.cons_append, List.nil_append, List.singleton_append]

theorem respWire_append_ne_nil (ρ : Resp) (S : List w8) : net.http.respWire ρ ++ S ≠ [] := by
  rw [respWire_split]; simp

/-- A header line, cut at its LF. -/
theorem hdrLineWire_split (kv : HdrLine) (Z : List w8) :
    net.http.hdrLineWire kv ++ Z = (kv.1 ++ W8 58 :: W8 32 :: (kv.2 ++ [W8 13])) ++ W8 10 :: Z := by
  simp only [net.http.hdrLineWire, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append]

theorem hdrLine_nlf (kv : HdrLine) (h : net.http.hdrLineOk kv) :
    W8 10 ∉ kv.1 ++ W8 58 :: W8 32 :: (kv.2 ++ [W8 13]) :=
  wire_nm_app (wire_nm_all (List.all_eq_true.1 h.2.1) (by decide))
    (wire_nm_cons (by decide) (wire_nm_cons (by decide)
      (wire_nm_app (wire_nm_all (List.all_eq_true.1 h.2.2.2.1) (by decide)) (by decide))))

/-- A header line starts with a byte of its key, not CR. -/
theorem hdrLine_head (kv : HdrLine) (Z : List w8) (h : net.http.hdrLineOk kv) :
    ∃ c rest, net.http.hdrLineWire kv ++ Z = c :: rest ∧ net.http.fieldByte c = true := by
  obtain ⟨c, ks, hks⟩ := List.exists_cons_of_ne_nil h.1
  refine ⟨c, (ks ++ W8 58 :: W8 32 :: (kv.2 ++ [W8 13])) ++ W8 10 :: Z, ?_, ?_⟩
  · rw [hdrLineWire_split, hks]; rfl
  · exact List.all_eq_true.1 h.2.1 c (by rw [hks]; exact List.mem_cons_self)

/-- The header lines up to the empty line are determined. -/
theorem hdrs_inj (hc : List HdrLine) : ∀ (hc' : List HdrLine) (X Y : List w8),
    (∀ kv ∈ hc, net.http.hdrLineOk kv) → (∀ kv ∈ hc', net.http.hdrLineOk kv) →
    hc.flatMap net.http.hdrLineWire ++ W8 13 :: W8 10 :: X =
      hc'.flatMap net.http.hdrLineWire ++ W8 13 :: W8 10 :: Y → hc = hc' ∧ X = Y := by
  induction hc with
  | nil =>
    intro hc' X Y _ hok' h
    cases hc' with
    | nil =>
      simp only [List.flatMap_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | cons kv' hc' =>
      exfalso
      obtain ⟨c, rest, hcr, hf⟩ :=
        hdrLine_head kv' (hc'.flatMap net.http.hdrLineWire ++ W8 13 :: W8 10 :: Y)
          (hok' kv' List.mem_cons_self)
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_assoc] at h
      rw [hcr] at h
      rw [← (List.cons.inj h).1] at hf
      exact absurd hf (by decide)
  | cons kv hc ih =>
    intro hc' X Y hok hok' h
    cases hc' with
    | nil =>
      exfalso
      obtain ⟨c, rest, hcr, hf⟩ :=
        hdrLine_head kv (hc.flatMap net.http.hdrLineWire ++ W8 13 :: W8 10 :: X)
          (hok kv List.mem_cons_self)
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_assoc] at h
      rw [hcr] at h
      rw [(List.cons.inj h).1] at hf
      exact absurd hf (by decide)
    | cons kv' hc' =>
      have hkv := hok kv List.mem_cons_self
      have hkv' := hok' kv' List.mem_cons_self
      simp only [List.flatMap_cons, List.append_assoc] at h
      rw [hdrLineWire_split, hdrLineWire_split] at h
      obtain ⟨hl, hrest⟩ :=
        wire_split_at (W8 10) _ _ _ _ (hdrLine_nlf kv hkv) (hdrLine_nlf kv' hkv') h
      obtain ⟨hk, hv⟩ := wire_split_at (W8 58) _ _ _ _
        (wire_nm_all (List.all_eq_true.1 hkv.2.1) (by decide))
        (wire_nm_all (List.all_eq_true.1 hkv'.2.1) (by decide)) hl
      have hv' := List.append_cancel_right (List.cons.inj hv).2
      obtain ⟨e, eXY⟩ := ih hc' X Y (fun k hk => hok k (List.mem_cons_of_mem _ hk))
        (fun k hk => hok' k (List.mem_cons_of_mem _ hk)) hrest
      exact ⟨by rw [Prod.ext hk hv', e], eXY⟩

/-- An answer's head followed by anything is read back as its status, reason and header lines. -/
theorem respWire_head_inj (ρ σ : Resp) (S T : List w8) (hρ : wireShape ρ) (hσ : wireShape σ)
    (h : net.http.respWire ρ ++ S = net.http.respWire σ ++ T) :
    ρ.st = σ.st ∧ ρ.reason = σ.reason ∧ ρ.hc = σ.hc ∧ ρ.body ++ S = σ.body ++ T := by
  rw [respWire_split ρ S, respWire_split σ T] at h
  have nlf : ∀ τ : Resp, wireShape τ →
      W8 10 ∉ go!"HTTP/1.1 " ++ (fmt.decimalNat (uint.nat τ.st) ++ W8 32 :: (τ.reason ++ [W8 13])) :=
    fun τ hτ => wire_nm_app (by decide) (wire_nm_app (wire_dec_nm _ (by decide))
      (wire_nm_cons (by decide) (wire_nm_app (wire_nm_all (List.all_eq_true.1 hτ.1) (by decide))
        (by decide))))
  obtain ⟨h1, h2⟩ := wire_split_at (W8 10) _ _ _ _ (nlf ρ hρ) (nlf σ hσ) h
  have h1' := List.append_cancel_left h1
  obtain ⟨hd, hr⟩ := wire_split_at (W8 32) _ _ _ _ (wire_dec_nm _ (by decide))
    (wire_dec_nm _ (by decide)) h1'
  have hst : ρ.st = σ.st := BitVec.eq_of_toNat_eq (decimalNat_inj hd)
  obtain ⟨hhc, hb⟩ := hdrs_inj ρ.hc σ.hc _ _ hρ.2 hσ.2 h2
  exact ⟨hst, List.append_cancel_right hr, hhc, hb⟩

/-- What `respOk` says of the body of an answer that is not `close`. -/
theorem respOk_body (ρ : Resp) (h : net.http.respOk ρ) (hc : ρ.close = false) :
    (net.http.bodyAllowed ρ.st = true →
      net.http.hdrGetL ρ.hc go!"Content-Length" = fmt.decimalNat ρ.body.length) ∧
    (net.http.bodyAllowed ρ.st = false → ρ.body = []) := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := h
  rw [hc, if_neg Bool.false_ne_true] at h
  constructor
  · intro hb; rw [if_pos hb] at h; exact h
  · intro hb; rw [if_neg (by rw [hb]; exact Bool.false_ne_true)] at h; exact h.2

/-- An answer's wire followed by anything is read back as that answer and the rest; no such
answer's wire starts net/http's `400`'s. -/
theorem respWire_inj (ρ : Resp) (hρ : net.http.respOk ρ ∧ ρ.close = false) (x : RespSlot)
    (hx : (∃ σ, x = .ans σ ∧ net.http.respOk σ ∧ σ.close = false) ∨ x = .bad) (S T : List w8)
    (h : net.http.respWire ρ ++ S = net.http.respSlotWire x ++ T) : x = .ans ρ ∧ S = T := by
  rcases hx with ⟨σ, rfl, hσ, hσc⟩ | rfl
  · obtain ⟨hst, hr, hhc, hb⟩ :=
      respWire_head_inj ρ σ S T (wireShape_of_ok hρ.1) (wireShape_of_ok hσ) h
    have bρ := respOk_body ρ hρ.1 hρ.2
    have bσ := respOk_body σ hσ hσc
    have hbody : ρ.body = σ.body ∧ S = T := by
      cases hba : net.http.bodyAllowed σ.st
      · have e1 := bρ.2 (by rw [hst]; exact hba)
        have e2 := bσ.2 hba
        rw [e1, e2] at hb ⊢
        exact ⟨rfl, by simpa using hb⟩
      · have e1 := bρ.1 (by rw [hst]; exact hba)
        have e2 := bσ.1 hba
        rw [hhc] at e1
        exact List.append_inj hb (decimalNat_inj (e1.symm.trans e2))
    have hcl : ρ.close = σ.close := hρ.2.trans hσc.symm
    have hρσ : ρ = σ := by
      cases ρ; cases σ
      simp only [net.http.Resp.mk.injEq]
      exact ⟨hst, hr, hhc, hbody.1, hcl⟩
    exact ⟨by rw [hρσ], hbody.2⟩
  · exfalso
    obtain ⟨hst, -, hhc, -⟩ :=
      respWire_head_inj ρ net.http.badResp S T (wireShape_of_ok hρ.1) wireShape_bad h
    have e1 := (respOk_body ρ hρ.1 hρ.2).1 (by rw [hst]; decide)
    rw [hhc, (by decide : net.http.hdrGetL net.http.badResp.hc go!"Content-Length" = [])] at e1
    exact fmt.decimalNat_ne_nil _ e1.symm

theorem respsWire_nil : net.http.respsWire [] = [] := rfl

theorem respsWire_cons (x : RespSlot) (Rs : List RespSlot) :
    net.http.respsWire (x :: Rs) = net.http.respSlotWire x ++ net.http.respsWire Rs := rfl

theorem respsWire_prefix_decode_aux (A : List Resp) : ∀ (Rs : List RespSlot) (y : List w8),
    (∀ ρ ∈ A, net.http.respOk ρ ∧ ρ.close = false) →
    (∀ x ∈ Rs, (∃ ρ, x = .ans ρ ∧ net.http.respOk ρ ∧ ρ.close = false) ∨ x = .bad) →
    net.http.respsWire (A.map RespSlot.ans) ++ y <+: net.http.respsWire Rs → y ≠ [] →
    ∃ x rest, Rs = A.map RespSlot.ans ++ x :: rest := by
  induction A with
  | nil =>
    intro Rs y _ _ hp hy
    obtain ⟨z, hz⟩ := hp
    cases Rs with
    | nil =>
      cases y with
      | nil => exact absurd rfl hy
      | cons a y => simp [respsWire_nil] at hz
    | cons x rest => exact ⟨x, rest, rfl⟩
  | cons ρ A ih =>
    intro Rs y hA hRs hp hy
    obtain ⟨z, hz⟩ := hp
    rw [List.map_cons, respsWire_cons, List.append_assoc, List.append_assoc] at hz
    cases Rs with
    | nil => exact absurd hz (respWire_append_ne_nil ρ _)
    | cons x rest =>
      rw [respsWire_cons] at hz
      obtain ⟨rfl, hrest⟩ :=
        respWire_inj ρ (hA ρ List.mem_cons_self) x (hRs x List.mem_cons_self) _ _ hz
      obtain ⟨x', rest', hr⟩ := ih rest y (fun σ hσ => hA σ (List.mem_cons_of_mem _ hσ))
        (fun x hx => hRs x (List.mem_cons_of_mem _ hx)) ⟨z, by rw [List.append_assoc]; exact hrest⟩ hy
      exact ⟨x', rest', by rw [hr, List.map_cons, List.cons_append]⟩

/-- See the file header. -/
theorem respsWire_prefix_decode (A : List Resp) (Rs : List RespSlot) (y : List w8)
    (hA : ∀ ρ ∈ A, net.http.respOk ρ ∧ ρ.close = false)
    (hRs : ∀ x ∈ Rs, (∃ ρ, x = .ans ρ ∧ net.http.respOk ρ ∧ ρ.close = false) ∨ x = .bad)
    (hp : net.http.respsWire (A.map RespSlot.ans) ++ y <+: net.http.respsWire Rs) (hy : y ≠ []) :
    ∃ x rest, Rs = A.map RespSlot.ans ++ x :: rest :=
  respsWire_prefix_decode_aux A Rs y hA hRs hp hy

/-! ## The driver's requests -/

theorem pathByte_letter (c : w8) (h : 97 ≤ c.toNat ∧ c.toNat ≤ 122) : net.http.pathByte c = true := by
  unfold net.http.pathByte; simp only [decide_eq_true_eq]; exact Or.inl h

theorem word_val {v : List w8} (hv : isWord v) : ∀ c ∈ v, 33 ≤ c.toNat ∧ c.toNat ≤ 126 :=
  fun c hc => by have := hv.2 c hc; omega

theorem decimalNat_val (n : Nat) : ∀ c ∈ fmt.decimalNat n, 33 ≤ c.toNat ∧ c.toNat ≤ 126 :=
  fun c hc => by
    have h : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := fmt.decimalNat_isDigit n c hc
    omega

theorem word_nm {w : List w8} (hw : isWord w) {c : w8} (hc : c.toNat < 97) : c ∉ w :=
  fun h => by have := (hw.2 c h).1; omega

theorem word_ne {w : List w8} (hw : isWord w) (s : List w8) (hs : ∃ c ∈ s, c.toNat < 97) : w ≠ s := by
  rintro rfl
  obtain ⟨c, hc, hlt⟩ := hs
  exact word_nm hw hlt hc

/-- A header line whose value is printable without spaces. -/
theorem hdrLineOk_of (k v : List w8)
    (hk : k ≠ [] ∧ k.all net.http.fieldByte = true ∧ net.http.canonQuick k = true)
    (hv : ∀ c ∈ v, 33 ≤ c.toNat ∧ c.toNat ≤ 126) : net.http.hdrLineOk (k, v) := by
  unfold net.http.hdrLineOk
  refine ⟨hk.1, hk.2.1, hk.2.2, List.all_eq_true.2 fun c hc => ?_, fun h => ?_, fun h => ?_⟩
  · have := hv c hc
    unfold net.http.valByte; simp only [decide_eq_true_eq]; omega
  · have h' : v.head? = some (W8 32) := h
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.1 h'
    exact absurd (hv (W8 32) (by rw [hys]; exact List.mem_cons_self)).1 (by decide)
  · have h' : v.getLast? = some (W8 32) := h
    exact absurd (hv (W8 32) (List.mem_of_getLast? h')).1 (by decide)

theorem hdrGetL_cons_eq (k v : List w8) (hb : List HdrLine) :
    net.http.hdrGetL ((k, v) :: hb) k = v := by
  unfold net.http.hdrGetL
  rw [List.find?_cons_of_pos (by simp)]
  rfl

theorem hdrGetL_cons_ne (k k' v : List w8) (hb : List HdrLine) (h : k ≠ k') :
    net.http.hdrGetL ((k, v) :: hb) k' = net.http.hdrGetL hb k' := by
  unfold net.http.hdrGetL
  rw [List.find?_cons_of_neg (by simpa using h)]

theorem reqWire_nope_head (w : List w8) : go!"/nope/" ++ w = W8 47 :: (go!"nope" ++ W8 47 :: w) := by
  rw [show (go!"/nope/" : List w8) = W8 47 :: (go!"nope" ++ [W8 47]) by decide]
  simp

/-- The driver's requests are read as written. -/
theorem DReq.reqOk (d : DReq) (hd : d.ok) (hj : d ≠ .junk) : net.http.reqOk d.hreq d.body := by
  cases d with
  | echo m v b =>
    obtain ⟨hm, hv, hb⟩ := hd
    show net.http.reqOk ⟨m, driverHost, go!"/echo",
      [(go!"X-Driver", v), (go!"Content-Length", fmt.decimalNat b.length)]⟩ b
    have hdl := fmt.length_decimalNat_le b.length 2 (by decide) (Nat.lt_of_le_of_lt hb.1 (by decide))
    unfold net.http.reqOk
    dsimp only
    rcases hm with rfl | rfl <;>
    refine ⟨by unfold net.http.methOk; decide, by unfold net.http.reqPath; decide, by decide, ?_, ?_,
      Or.inl (by rw [hdrGetL_cons_ne _ _ _ _ (by decide), hdrGetL_cons_eq]), by simp, ?_,
      Nat.lt_of_le_of_lt hb.1 (by decide)⟩
    all_goals first
      | (unfold net.http.hdrBlockOk
         refine ⟨?_, ?_⟩
         · show [go!"Host", go!"X-Driver", go!"Content-Length"].Nodup; decide
         · intro kv hkv
           simp only [List.mem_cons, List.not_mem_nil, or_false] at hkv
           rcases hkv with rfl | rfl | rfl
           · decide
           · exact hdrLineOk_of _ _ (by decide) (word_val hv)
           · exact hdrLineOk_of _ _ (by decide) (decimalNat_val _))
      | (intro kv hkv
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hkv
         rcases hkv with rfl | rfl
         · exact (by decide : go!"X-Driver" ∉ net.http.reqKeysOut)
         · exact (by decide : go!"Content-Length" ∉ net.http.reqKeysOut))
      | (simp only [net.http.reqWire, net.http.hdrWire, net.http.hdrLineWire, driverHost,
           List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_cons,
           List.length_nil, Nat.reducePow]
         have := hv.1
         omega)
  | status =>
    show net.http.reqOk ⟨go!"GET", driverHost, go!"/status", []⟩ []
    unfold net.http.reqOk
    exact ⟨by unfold net.http.methOk; decide, by unfold net.http.reqPath; decide, by decide,
      by decide, by simp, Or.inr ⟨by simp, rfl⟩, by simp, by decide, by decide⟩
  | nope w =>
    have hw : isWord w := hd
    show net.http.reqOk ⟨go!"GET", driverHost, go!"/nope/" ++ w, []⟩ []
    unfold net.http.reqOk
    refine ⟨(by unfold net.http.methOk; decide : net.http.methOk go!"GET"), ?_,
      (by decide : driverHost.all net.http.hostByte = true),
      (by decide : net.http.hdrBlockOk [(go!"Host", driverHost)]), by simp,
      Or.inr ⟨by simp, rfl⟩, by simp, ?_, by decide⟩
    · unfold net.http.reqPath
      refine ⟨by rw [reqWire_nope_head]; rfl, fun c hc => ?_⟩
      rcases List.mem_append.1 hc with h | h
      · exact (by decide : ∀ c ∈ (go!"/nope/" : List w8), net.http.pathByte c = true) c h
      · exact pathByte_letter c (hw.2 c h)
    · simp only [net.http.reqWire, net.http.hdrWire, net.http.hdrLineWire, driverHost,
        List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_cons,
        List.length_nil, Nat.reducePow]
      have := hw.1
      omega
  | junk => exact absurd rfl hj

/-- The junk request is rejected at its request line. -/
theorem junkWire_ok : net.http.junkOk junkWire := by
  unfold net.http.junkOk
  exact ⟨go!"NOT A REQUEST\r", go!"\r\n", by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- The mux's patterns, as `HandleFunc` registers them (`/echo`, then `/status`). -/
def drvPats : List GoString := [go!"/status", go!"/echo"]

/-- A path of one segment is clean. -/
theorem pathClean_one (s : List w8) (h47 : W8 47 ∉ s) (h1 : s ≠ go!".") (h2 : s ≠ go!"..") :
    net.http.pathClean (W8 47 :: s) := by
  simp only [net.http.pathClean, List.drop_one, List.tail_cons]
  rw [List.splitOn_eq_singleton h47]
  intro i t hi
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨h1, h2, by simp⟩
  · simp at hi

/-- A path of two segments, the first not empty, is clean. -/
theorem pathClean_two (s w : List w8) (hs47 : W8 47 ∉ s) (hw47 : W8 47 ∉ w)
    (hs : s ≠ [] ∧ s ≠ go!"." ∧ s ≠ go!"..") (hw : w ≠ go!"." ∧ w ≠ go!"..") :
    net.http.pathClean (W8 47 :: (s ++ W8 47 :: w)) := by
  simp only [net.http.pathClean, List.drop_one, List.tail_cons]
  rw [List.splitOn_append_cons_self_of_not_mem hs47, List.splitOn_eq_singleton hw47]
  intro i t hi
  rcases i with _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨hs.2.1, hs.2.2, fun _ => hs.1⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact ⟨hw.1, hw.2, by simp⟩
  · simp at hi

theorem pathClean_status : net.http.pathClean go!"/status" := by
  rw [show (go!"/status" : List w8) = W8 47 :: go!"status" by decide]
  exact pathClean_one _ (by decide) (by decide) (by decide)

theorem pathClean_echo : net.http.pathClean go!"/echo" := by
  rw [show (go!"/echo" : List w8) = W8 47 :: go!"echo" by decide]
  exact pathClean_one _ (by decide) (by decide) (by decide)

theorem pathClean_nope (w : List w8) (hw : isWord w) : net.http.pathClean (go!"/nope/" ++ w) := by
  rw [reqWire_nope_head]
  exact pathClean_two _ _ (by decide) (word_nm hw (by decide)) (by decide)
    ⟨word_ne hw _ ⟨W8 46, by decide, by decide⟩, word_ne hw _ ⟨W8 46, by decide, by decide⟩⟩

theorem drvPats_ok : ∀ p ∈ drvPats, net.http.litPattern p ∧ net.http.pathClean p := by
  intro p hp
  simp only [drvPats, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by unfold net.http.litPattern; decide, pathClean_status⟩
  · exact ⟨by unfold net.http.litPattern; decide, pathClean_echo⟩

theorem drvPats_last : ∀ q ∈ drvPats, q.getLast? ≠ some (W8 47) := by decide

theorem drvPats_not_redirect (p : GoString) (hc : net.http.pathClean p) :
    ¬ net.http.muxRedirect drvPats p := by
  rintro (h | ⟨-, -, hm⟩)
  · exact h hc
  · exact drvPats_last _ hm List.getLast?_concat

/-- The driver's paths and the mux: `/echo` and `/status` are routed to their handlers (the path is
the pattern), and no other path is redirected or under a pattern. -/
theorem DReq.route (d : DReq) (hd : d.ok) (hj : d ≠ .junk) :
    ¬ net.http.muxRedirect drvPats d.hreq.path ∧
    (d.hreq.path ≠ go!"/echo" → d.hreq.path ≠ go!"/status" →
      ∀ p ∈ drvPats, ¬ net.http.pathUnder p d.hreq.path) := by
  refine ⟨drvPats_not_redirect _ ?_, fun h1 h2 p hp hu => ?_⟩
  · cases d with
    | echo m v b => exact pathClean_echo
    | status => exact pathClean_status
    | nope w => exact pathClean_nope w hd
    | junk => exact absurd rfl hj
  · rcases hu with hu | ⟨hl, -⟩
    · subst hu
      simp only [drvPats, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hp | hp
      · exact h2 hp
      · exact h1 hp
    · exact drvPats_last p hp hl

/-- A path under `/echo` (or `/status`) is it. -/
theorem pathUnder_lit (p q : GoString) (hp : p.getLast? ≠ some (W8 47))
    (h : net.http.pathUnder p q) : q = p := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact absurd h hp

/-! ## Header lines -/

theorem find?_filter_of {α : Type _} (l : List α) (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) : (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos (h a hp), List.find?_cons_of_pos hp, List.find?_cons_of_pos hp]
    · rw [List.find?_cons_of_neg hp, ← ih]
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq, List.find?_cons_of_neg hp]
      · rw [List.filter_cons_of_neg hq]

/-- `dropConn` keeps every other key's value. -/
theorem hdrGetL_dropConn (hc : List HdrLine) (k : GoString) (hk : k ≠ go!"Connection") :
    net.http.hdrGetL (net.http.dropConn hc) k = net.http.hdrGetL hc k := by
  unfold net.http.hdrGetL net.http.dropConn
  rw [find?_filter_of]
  intro a ha
  simp only [decide_eq_true_eq] at ha ⊢
  rw [ha]
  exact hk

/-- `strconv`'s base-`10` digits are `fmt`'s decimal. -/
theorem baseDigits_ten (b : Nat) (hb : 2 ≤ b) (h10 : b = 10) (m : Nat) :
    (internal.strconv.baseDigits b hb m).map internal.strconv.digitChar = fmt.decimalNat m := by
  subst h10
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [internal.strconv.baseDigits]
    by_cases hm : m < 10
    · rw [if_pos hm, fmt.decimalNat_of_lt hm]
      simp [internal.strconv.digitChar, fmt.digitByte, hm]
    · rw [if_neg hm, fmt.decimalNat_of_ge (by omega), List.map_append, ih (m / 10) (by omega)]
      have : m % 10 < 10 := Nat.mod_lt _ (by omega)
      simp [internal.strconv.digitChar, fmt.digitByte, this]

/-- `strconv.Itoa` of a body's length (at most `32`) is its decimal. -/
theorem fmtInt_small (n : Nat) (hn : n ≤ 32) :
    internal.strconv.fmtInt (W64 n) (W64 10) = fmt.decimalNat n := by
  have h1 : (W64 (n : Int)).toNat = n := by
    have hz := uint_Z_W64 (n : Int) (by omega)
      (Int.lt_of_le_of_lt (show (n : Int) ≤ 32 by omega) (by decide))
    simp only [uint.Z] at hz
    omega
  have h2 : ¬ sint.Z (W64 (n : Int)) < 0 := by
    simp only [sint.Z]
    rw [BitVec.toInt_eq_toNat_cond, h1]
    have : 2 * n < 2 ^ 64 := Nat.lt_of_le_of_lt (show 2 * n ≤ 64 by omega) (by decide)
    rw [if_pos this]
    omega
  unfold internal.strconv.fmtInt internal.strconv.fmtUint
  rw [if_neg h2, dif_pos (by decide), h1]
  exact baseDigits_ten _ _ (by decide) n

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
